import Lean
import Forge.Checker.Tactic
/-
  `forge_cone?`: the cone oracle called through a BOUNDED DATA PROTOCOL.

  WHAT IT DOES.
  1. Reifies the goal and hypotheses exactly as `forge_cone` does (the same
     `reifyProblem` from `Tactic.lean`, so the same atom and constraint order).
  2. Serialises the reified problem as one JSON object
       {"target": Poly, "inequalities": [Poly], "equalities": [Poly]}
     in the polynomial shape of `tools/export_lean_cone.py` (the same
     `polyJson` that `forge_reify` prints).
  3. Runs the oracle command (option `forge.oracle.cmd`, default
     `python tools/forge_oracle.py`) as a child process, writes the problem to
     its stdin, and reads at most `forge.oracle.maxOutputBytes` bytes of stdout
     within `forge.oracle.timeoutMs` milliseconds. Over either bound the child
     is killed and the tactic FAILS.
  4. DECODES the reply strictly (see `decodeReply`): a character-level prescan
     outside strings (no floats, exponents, `true`/`false`/`null`; bounded digit
     runs and nesting), then `Lean.Json.parse`, then a duplicate-key check, then
     an exact field set for every object, integer-only numbers of bounded size,
     monomials of exactly the problem's arity, `powers` of exactly the number of
     inequalities, exactly one multiplier per equality, and bounded counts. Any
     deviation FAILS with a message naming it.
  5. Renders the decoded `Cert` as Lean source text, parses it as a term, and
     hands that term to `runForgeCone` -- the SAME kernel-checked path as
     `forge_cone ... using c`: `decide` on `Cert.check`, then `cone_denote`,
     `Meta.check`, `isDefEq` against the goal, and the kernel at declaration
     time.
  6. On success, emits a "Try this:" suggestion replacing `forge_cone?` with
     the explicit `forge_cone ... using { scale := …, squares := …, … }`, so the
     saved proof does not call the oracle.

  WHAT IS TRUSTED. Nothing that crosses the boundary. The final proof term is
  `cone_denote c x tp gs fs hcheck hg hf` with `c` a closed `Cert` literal and
  `hcheck` a `decide` proof; it mentions no IO, no Python, no `ofReduceBool`.
  The decoder exists to fail EARLY and CLEARLY and to bound resource use -- a
  certificate that decodes is still only a proposal, and one that is wrong is
  rejected by `Cert.check` under `decide`, exactly as in `forge_cone`.

  WHAT IS NOT DONE. There is no fallback: if the oracle fails, times out, says
  `unknown`, or returns a certificate that does not check, the tactic fails.

  COMMAND RESOLUTION. `forge.oracle.cmd` is split on spaces (so paths with
  spaces are not supported). A token that is a relative path naming an
  existing file in the working directory or one of its four nearest ancestors
  is replaced by that absolute path; this is what lets the default find
  `tools/forge_oracle.py` when Lean runs in `lean/`.
-/
namespace Forge.Checker.Oracle

open Lean Meta Elab Tactic
open Forge.Checker Forge.Checker.Tactic

register_option forge.oracle.cmd : String := {
  defValue := "python tools/forge_oracle.py"
  descr := "forge_cone?: the oracle command, split on spaces; relative file paths are \
    resolved against the working directory and its ancestors"
}

register_option forge.oracle.timeoutMs : Nat := {
  defValue := 60000
  descr := "forge_cone?: wall-clock limit for the oracle process, in milliseconds"
}

register_option forge.oracle.maxOutputBytes : Nat := {
  defValue := 1000000
  descr := "forge_cone?: the most stdout bytes accepted from the oracle"
}

register_option forge.oracle.reportTime : Bool := {
  defValue := false
  descr := "forge_cone?: log the oracle and checking wall-clock times"
}

/-! ### Decoder bounds (fixed; the producer honours the same numbers) -/

def maxSquares : Nat := 1000
def maxTerms : Nat := 1000

/-- The length of the term list `collect` receives when `Cert.check` runs on this
certificate and problem: the target, plus each square's product with its
constraint powers, plus each multiplier times its equality. Every list
operation in the checker is structurally recursive over this list, so it -- and
not the number of squares -- is what the kernel's recursion limit tracks.

Review showed why this matters: 1000 zero-weight squares with empty polynomials
check in seconds, while ONE square with 45 terms (2025 products) does not. -/
def checkSize (c : Cert) (p : Poly) (ineqs eqs : List Poly) : Nat :=
  let powers (es : List Nat) : Nat :=
    (es.zip ineqs).foldl (fun acc eg => acc * eg.2.length ^ eg.1) 1
  let cone := c.squares.foldl
    (fun acc s => acc + powers s.powers * (s.poly.length * s.poly.length)) 0
  let mults := (c.multipliers.zip eqs).foldl (fun acc hf => acc + hf.1.length * hf.2.length) 0
  p.length + cone + mults

/-- MEASURED, NOT DERIVED. On leanprover/lean4 v4.34.0 with `decide +kernel`, a
univariate square with k terms against its expanded target checked at k = 40
(size 79 + 1600 = 1679) and failed with "(kernel) deep recursion detected" at
k = 45 (size 89 + 2025 = 2114). The limit is set below the largest size seen to
pass. Other shapes may differ; a certificate over this limit is refused BEFORE
checking, with that reason, rather than reported as rejected. The previous
decoder bounds (1000 squares, 1000 terms per polynomial) were structural caps
that the checker could not in fact meet -- review measured the gap. -/
def measuredCheckLimit : Nat := 1600
def maxDigits : Nat := 100
def maxExponent : Nat := 64
def maxVariables : Nat := 64
def maxDepth : Nat := 16

/-! ### The request -/

def requestJson (prob : Problem) : Json :=
  let n := prob.atoms.size
  Json.mkObj [
    ("target", polyJson n (IExpr.toPoly prob.targetR.val)),
    ("inequalities", Json.arr (prob.ineqs.map (fun h => polyJson n (IExpr.toPoly h.expr.val)))),
    ("equalities", Json.arr (prob.eqs.map (fun h => polyJson n (IExpr.toPoly h.expr.val))))]

/-! ### Running the process, bounded in time and output -/

/-- Read until EOF, keeping at most `cap + 1` bytes; stop early (returning
`true`) once more than `cap` bytes have arrived. -/
partial def readBounded (h : IO.FS.Handle) (cap : Nat) (acc : ByteArray := .empty) :
    IO (ByteArray × Bool) := do
  let chunk ← h.read 65536
  if chunk.isEmpty then return (acc, false)
  let acc := acc ++ chunk
  if acc.size > cap then return (acc, true)
  readBounded h cap acc

/-- Read until EOF, keeping only the first `keep` bytes (used for stderr, so a
chatty child can never block on a full pipe). -/
partial def drainKeep (h : IO.FS.Handle) (keep : Nat) (acc : ByteArray := .empty) :
    IO ByteArray := do
  let chunk ← h.read 65536
  if chunk.isEmpty then return acc
  let acc := if acc.size < keep then acc ++ chunk.extract 0 (keep - acc.size) else acc
  drainKeep h keep acc

/-- Write the request and drop the handle, which closes the child's stdin. -/
def writeAndClose (h : IO.FS.Handle) (s : String) : IO Unit := do
  h.putStr s
  h.flush

structure RunResult where
  exitCode : Option UInt32
  stdout : ByteArray
  overflow : Bool
  timedOut : Bool
  stderr : String
  ms : Nat

def ancestors (d : System.FilePath) : Nat → List System.FilePath
  | 0 => [d]
  | k + 1 => d :: match d.parent with
    | some p => if p == d then [] else ancestors p k
    | none => []

def resolveToken (cwd : System.FilePath) (tok : String) : IO String := do
  let fp : System.FilePath := tok
  if tok.startsWith "-" || fp.isAbsolute then return tok
  -- Only tokens that are visibly PATHS are resolved against the working directory
  -- and its ancestors. A bare program name such as `python` is left for the
  -- operating system to find on PATH; before this, a stray file named `python`
  -- in the working directory or any of four ancestors silently replaced the
  -- interpreter (found by review).
  unless tok.any (fun ch => ch == '/' || ch == '\\') do return tok
  for d in ancestors cwd 4 do
    let cand := d / fp
    if ← cand.pathExists then
      if !(← cand.isDir) then return cand.toString
  return tok

def runOracle (cmd : String) (input : String) (timeoutMs cap : Nat) : IO RunResult := do
  let toks := (cmd.splitOn " ").filter (· ≠ "")
  if toks.isEmpty then throw (IO.userError "forge.oracle.cmd is empty")
  let cwd ← IO.currentDir
  let toks ← toks.mapM (resolveToken cwd)
  let t0 ← IO.monoMsNow
  let child ← IO.Process.spawn {
    cmd := toks.head!, args := toks.tail.toArray,
    stdin := .piped, stdout := .piped, stderr := .piped }
  let outTask ← IO.asTask (readBounded child.stdout cap) .dedicated
  let errTask ← IO.asTask (drainKeep child.stderr 2000) .dedicated
  let (stdin, child) ← child.takeStdin
  -- A child that exits without reading its input makes this write fail; the
  -- reply (or its absence) is what decides the outcome, not the write.
  try writeAndClose stdin input catch _ => pure ()
  let mut code : Option UInt32 := none
  let mut timedOut := false
  let mut overflow := false
  repeat
    match ← child.tryWait with
    | some c =>
      code := some c
      break
    | none =>
      if (← IO.monoMsNow) ≥ t0 + timeoutMs then
        timedOut := true
        try child.kill catch _ => pure ()
        break
      if ← IO.hasFinished outTask then
        if let .ok (_, true) := outTask.get then
          overflow := true
          try child.kill catch _ => pure ()
          break
      IO.sleep 5
  if code.isNone then
    try discard <| child.wait catch _ => pure ()
  let (out, over) ← match ← IO.wait outTask with
    | .ok r => pure r
    | .error e => throw e
  let err ← match ← IO.wait errTask with
    | .ok r => pure (String.fromUTF8? r |>.getD "<stderr is not UTF-8>")
    | .error _ => pure ""
  let t1 ← IO.monoMsNow
  return { exitCode := code, stdout := out, overflow := overflow || over,
           timedOut, stderr := err, ms := t1 - t0 }

/-! ### Strict decoding

Everything in this section runs in `Except String`. It is untrusted in the
same sense as the reifier: a bug here can make `forge_cone?` fail, and cannot
make it prove anything, because the decoded certificate still goes through
`Cert.check` under `decide`. -/

/-- A character-level scan of the reply, outside JSON strings. Only the
characters of integers and structure are allowed, which rules out floats,
exponents (`1e999999999` would make the core parser build a huge number before
any bound is checked), `true`, `false` and `null`. Digit runs and nesting depth
are bounded for the same reason. Returns the number of `:` outside strings,
which `fieldCount` later compares to detect duplicate keys. -/
def prescan (s : String) : Except String Nat := Id.run do
  let mut inStr := false
  let mut esc := false
  let mut depth := 0
  let mut run := 0
  let mut colons := 0
  for c in s.toList do
    if inStr then
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == '"' then inStr := false
      continue
    if c.isDigit then
      run := run + 1
      if run > maxDigits then
        return .error s!"a number has more than {maxDigits} digits"
      continue
    run := 0
    if c == '"' then inStr := true
    else if c == '{' || c == '[' then
      depth := depth + 1
      if depth > maxDepth then return .error s!"nesting deeper than {maxDepth}"
    else if c == '}' || c == ']' then depth := depth - 1
    else if c == ':' then colons := colons + 1
    else if c == ',' || c == '-' || c == ' ' || c == '\n' || c == '\r' || c == '\t' then
      pure ()
    else
      return .error s!"character '{c}' (code {c.toNat}) outside a string; only integers, \
        strings, arrays and objects are part of the protocol"
  return .ok colons

/-- Number of object fields in a parsed value. -/
partial def fieldCount : Json → Nat
  | .obj kvs => kvs.foldl (fun acc _ v => acc + 1 + fieldCount v) 0
  | .arr a => a.foldl (fun acc v => acc + fieldCount v) 0
  | _ => 0

def expectObj (j : Json) (what : String) (keys : List String) :
    Except String (Std.TreeMap.Raw String Json compare) := do
  let .obj kvs := j | throw s!"{what}: expected an object"
  let actual := kvs.foldl (fun acc k _ => acc.push k) (#[] : Array String)
  let expected := keys.toArray.qsort (· < ·)
  let actual := actual.qsort (· < ·)
  unless actual == expected do
    throw s!"{what}: expected exactly the fields {expected.toList}, got {actual.toList}"
  return kvs

def field (kvs : Std.TreeMap.Raw String Json compare) (k : String) : Json :=
  (kvs.get? k).getD .null

def expectArr (j : Json) (what : String) (maxLen : Nat) : Except String (Array Json) := do
  let .arr a := j | throw s!"{what}: expected an array"
  if a.size > maxLen then throw s!"{what}: more than {maxLen} elements"
  return a

def expectInt (j : Json) (what : String) : Except String Int := do
  match j with
  | .num ⟨m, 0⟩ =>
    if m.natAbs ≥ 10 ^ maxDigits then throw s!"{what}: integer with more than {maxDigits} digits"
    return m
  | .num _ => throw s!"{what}: expected an integer, got a non-integer number"
  | _ => throw s!"{what}: expected an integer"

def expectNat (j : Json) (what : String) (bound : Nat) : Except String Nat := do
  let i ← expectInt j what
  if i < 0 then throw s!"{what}: expected a nonnegative integer, got {i}"
  if i.toNat > bound then throw s!"{what}: {i} exceeds the bound {bound}"
  return i.toNat

def decodePoly (n : Nat) (j : Json) (what : String) : Except String Poly := do
  let kvs ← expectObj j what ["n", "terms"]
  let n' ← expectNat (field kvs "n") s!"{what}.n" maxVariables
  unless n' == n do throw s!"{what}.n: expected {n} (the number of atoms), got {n'}"
  let terms ← expectArr (field kvs "terms") s!"{what}.terms" maxTerms
  let mut out : Array (Mono × Int) := #[]
  for h : i in [0:terms.size] do
    let w := s!"{what}.terms[{i}]"
    let pair ← expectArr terms[i] w 2
    unless pair.size == 2 do throw s!"{w}: expected [monomial, coefficient]"
    let mono ← expectArr pair[0]! s!"{w}.monomial" n
    unless mono.size == n do
      throw s!"{w}.monomial: expected exactly {n} exponents, got {mono.size}"
    let es ← mono.mapIdxM fun k e => expectNat e s!"{w}.monomial[{k}]" maxExponent
    let c ← expectInt pair[1]! s!"{w}.coefficient"
    out := out.push (es.toList, c)
  return out.toList

/-- The decoded reply. -/
inductive Reply where
  | cert (c : Cert)
  | declined (status reason : String)

def decodeValue (j : Json) (nAtoms nIneqs nEqs : Nat) : Except String Reply := do
  let .obj kvs := j | throw "reply: expected an object"
  let .str status := field kvs "status" | throw "reply.status: expected a string"
  if status == "unknown" || status == "error" then
    let kvs ← expectObj j "reply" ["status", "reason"]
    let .str reason := field kvs "reason" | throw "reply.reason: expected a string"
    return .declined status (reason.take 500).toString
  unless status == "certificate" do
    throw s!"reply.status: expected \"certificate\", \"unknown\" or \"error\", got {repr status}"
  let kvs ← expectObj j "reply" ["status", "scale", "squares", "multipliers"]
  let scale ← expectInt (field kvs "scale") "reply.scale"
  let sqs ← expectArr (field kvs "squares") "reply.squares" maxSquares
  let squares ← sqs.mapIdxM fun i s => do
    let w := s!"reply.squares[{i}]"
    let skv ← expectObj s w ["weight", "powers", "poly"]
    let weight ← expectInt (field skv "weight") s!"{w}.weight"
    let pws ← expectArr (field skv "powers") s!"{w}.powers" nIneqs
    unless pws.size == nIneqs do
      throw s!"{w}.powers: expected exactly {nIneqs} exponents (one per inequality), got {pws.size}"
    let powers ← pws.mapIdxM fun k e => expectNat e s!"{w}.powers[{k}]" maxExponent
    let poly ← decodePoly nAtoms (field skv "poly") s!"{w}.poly"
    return ({ weight, powers := powers.toList, poly } : Square)
  let ms ← expectArr (field kvs "multipliers") "reply.multipliers" nEqs
  unless ms.size == nEqs do
    throw s!"reply.multipliers: expected exactly {nEqs} (one per equality), got {ms.size}"
  let multipliers ← ms.mapIdxM fun i m => decodePoly nAtoms m s!"reply.multipliers[{i}]"
  return .cert { scale, squares := squares.toList, multipliers := multipliers.toList }

/-- The whole decoder, from raw bytes. -/
def decodeReply (bytes : ByteArray) (nAtoms nIneqs nEqs : Nat) : Except String Reply := do
  let some text := String.fromUTF8? bytes | throw "reply is not valid UTF-8"
  let colons ← prescan text
  let j ← match Json.parse text with
    | .ok j => pure j
    | .error e => throw s!"reply is not a single well-formed JSON value: {e}"
  unless fieldCount j == colons do
    throw "reply contains a duplicate object key"
  decodeValue j nAtoms nIneqs nEqs

/-! ### Rendering the certificate as source text -/

def intText (i : Int) : String := if i < 0 then "(" ++ toString i ++ ")" else toString i

def listText {α} (f : α → String) (l : List α) : String :=
  "[" ++ ", ".intercalate (l.map f) ++ "]"

def polyText (p : Poly) : String :=
  listText (fun (t : Mono × Int) => "(" ++ listText toString t.1 ++ ", " ++ intText t.2 ++ ")") p

def certText (c : Cert) : String :=
  "{ scale := " ++ intText c.scale ++
  ", squares := " ++ listText (fun (s : Square) =>
      "{ weight := " ++ intText s.weight ++ ", powers := " ++ listText toString s.powers ++
      ", poly := " ++ polyText s.poly ++ " }") c.squares ++
  ", multipliers := " ++ listText polyText c.multipliers ++ " }"

/-! ### The tactic -/

/-- `forge_cone? [(atoms := [a₀, …])] [h₁, …]` asks the external oracle
(`forge.oracle.cmd`) for a cone certificate, closes the goal with it through the
same kernel-checked path as `forge_cone`, and suggests the explicit
`forge_cone … using {…}` call to save. It fails -- never admits -- whenever the
oracle fails, times out, declines, or returns anything that does not decode or
does not check. -/
syntax (name := forgeConeOracle) "forge_cone?" (ppSpace atomsClause)? (ppSpace "[" term,* "]")? :
  tactic

def oracleFail (msg : MessageData) : TacticM α :=
  throwError m!"forge_cone?: {msg}"

elab_rules : tactic
  | `(tactic| forge_cone? $[(atoms := [$as,*])]? $[[$hs,*]]?) => do
    let ref ← getRef
    let opts ← getOptions
    let cmd := forge.oracle.cmd.get opts
    let timeoutMs := forge.oracle.timeoutMs.get opts
    let cap := forge.oracle.maxOutputBytes.get opts
    let goal ← getMainGoal
    let (seed, hyps, prob) ← goal.withContext do
      let seed ← elabAtoms ((as.map (·.getElems)).getD #[])
      let hyps ← elabHyps ((hs.map (·.getElems)).getD #[])
      let prob ← reifyProblem seed (← instantiateMVars (← goal.getType)) hyps
      return (seed, hyps, prob)
    let request := (requestJson prob).compress
    let res ← try runOracle cmd request timeoutMs cap
      catch e => oracleFail m!"could not run the oracle command `{cmd}`: {e.toMessageData}"
    if res.timedOut then
      oracleFail m!"the oracle `{cmd}` did not finish within {timeoutMs} ms and was killed"
    if res.overflow then
      oracleFail m!"the oracle `{cmd}` wrote more than {cap} bytes to stdout; \
        output rejected and process killed"
    let nA := prob.atoms.size
    let nI := prob.ineqs.size
    let nE := prob.eqs.size
    let decoded := decodeReply res.stdout nA nI nE
    let code := res.exitCode.getD 0
    let stderrNote : MessageData :=
      if res.stderr.isEmpty then m!"" else m!"\nstderr (first 2000 bytes):\n{res.stderr}"
    let cert ← match decoded with
      | .ok (.cert c) =>
        unless code == 0 do
          oracleFail m!"the oracle exited with code {code} although it printed a certificate; \
            rejected{stderrNote}"
        pure c
      | .ok (.declined status reason) =>
        oracleFail m!"the oracle returned status `{status}` (exit code {code}): {reason}"
      | .error e =>
        oracleFail m!"MALFORMED oracle reply rejected at the data boundary \
          (exit code {code}): {e}{stderrNote}"
    let size := checkSize cert (IExpr.toPoly prob.targetR.val)
      (prob.ineqs.map (fun h => IExpr.toPoly h.expr.val)).toList
      (prob.eqs.map (fun h => IExpr.toPoly h.expr.val)).toList
    if size > measuredCheckLimit then
      oracleFail m!"the oracle's certificate decoded, but its expanded identity has \
        {size} terms, above the {measuredCheckLimit} that `decide +kernel` was \
        MEASURED to check. It was NOT checked; this is not a verdict on the certificate."
    let text := certText cert
    let certStx ← match Parser.runParserCategory (← getEnv) `term text with
      | .ok s => pure s
      | .error e => oracleFail m!"internal: rendered certificate does not parse: {e}"
    let certTerm : Term := ⟨certStx⟩
    let t0 ← IO.monoMsNow
    try
      runForgeCone seed hyps certTerm
    catch e =>
      let msg ← e.toMessageData.toString
      if (msg.splitOn "could NOT BE CHECKED").length > 1 then
        oracleFail m!"the oracle's certificate DECODED but could NOT BE CHECKED \
          (a resource limit, not a verdict):\n{e.toMessageData}"
      oracleFail m!"the oracle's certificate DECODED but was REJECTED by the \
        kernel-checked path of forge_cone:\n{e.toMessageData}"
    let t1 ← IO.monoMsNow
    let tac ← `(tactic| forge_cone $[(atoms := [$as,*])]? $[[$hs,*]]? using $certTerm)
    Meta.Tactic.TryThis.addSuggestion ref tac (origSpan? := ref)
    if forge.oracle.reportTime.get opts then
      logInfo m!"forge_cone?: oracle {res.ms} ms ({res.stdout.size} bytes), \
        decide + proof term {t1 - t0} ms"

end Forge.Checker.Oracle
