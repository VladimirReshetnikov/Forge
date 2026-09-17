/-
  Forge.Checker.Affine -- the "Integral affine witness" family, checked in core Lean.

  WHAT THE PROTOTYPE CHECKS. `check_affine_witness(A, B, c, W, require_integral=True)`
  in prototype/forge/witness/affine.py, as called from prototype/forge/io/decode.py,
  returns True exactly when

    * A, B, c are nonempty and have the same number m of rows; every row of A has
      length k = len(A[0]) >= 1 and every row of B has length p = len(B[0]) >= 1;
    * W (`linear`) is a k x p matrix and d (`offset`) a vector of length k;
    * every entry of W and d is an integer (denominator 1), and
    * A W = B and A d = c, as exact rational identities.

  Its meaning as a Skolem witness: for EVERY x, the integer affine term
  w(x) = W x + d satisfies A w(x) = B x + c. So "for all x there is an integral w
  with A w = B x + c" holds, uniformly, with w an explicit affine function of x.

  HERE. Entries are `Int`, so integrality is not a runtime test but a property of
  the type: a certificate with a non-integral entry cannot be written down, and the
  exporter refuses to emit one (Python rejects it too). The bundle's A, B, c are
  integers, and the exporter refuses anything else. For integer entries the
  rational identities A W = B, A d = c hold iff the same identities hold in `Int`,
  since `Int -> Rat` is an injective ring homomorphism. So `AffineCert.check` below
  accepts exactly the inputs Python accepts, restricted to integer A, B, c.

  PROVED.
    * `AffineCert.sound`: check = true  ->  for all x, A (W x + d) = B x + c.
    * `AffineCert.check_iff`: check = true  <->  shape conditions  /\  that identity
      for all x. So the checker is not merely sound but exact: it accepts precisely
      the well-shaped certificates whose affine map is a solution for every x.

  Vectors are `List Int`; `dot` truncates at the shorter list, which is why the
  theorems need no hypothesis on the length of x (a short x reads as zero-padded,
  entries of x beyond p are ignored by every row of length p).
-/

namespace Forge.Checker.Lin

/-- Dot product; truncates at the shorter list. -/
def dot : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- Componentwise sum; truncates at the shorter list. -/
def vadd : List Int → List Int → List Int
  | a :: as, b :: bs => (a + b) :: vadd as bs
  | _, _ => []

def smul (c : Int) (v : List Int) : List Int := v.map (c * ·)

/-- Matrix (list of rows) times vector. -/
def mulVec (M : List (List Int)) (x : List Int) : List Int := M.map (fun r => dot r x)

/-- `comb p a W = Σ_j a_j • W_j`, the row combination of `W` with weights `a`,
as a vector of length `p`. This is row `a` of `A` times the matrix `W`:
its `t`-th entry is `Σ_j a_j * W[j][t]`, the sum Python compares with `B[i][t]`. -/
def comb (p : Nat) : List Int → List (List Int) → List Int
  | a :: as, w :: ws => vadd (smul a w) (comb p as ws)
  | _, _ => List.replicate p 0

theorem len_nil_cons {α β : Type} {b : β} {bs : List β}
    (h : ([] : List α).length = (b :: bs).length) : False := Nat.noConfusion h
theorem len_cons_nil {α β : Type} {a : α} {as : List α}
    (h : (a :: as).length = ([] : List β).length) : False := Nat.noConfusion h
theorem len_cons_cons {α β : Type} {a : α} {b : β} {as : List α} {bs : List β}
    (h : (a :: as).length = (b :: bs).length) : as.length = bs.length := Nat.succ.inj h

@[simp] theorem dot_nil_left (x : List Int) : dot [] x = 0 := by cases x <;> rfl
@[simp] theorem dot_nil_right (x : List Int) : dot x [] = 0 := by cases x <;> rfl
@[simp] theorem dot_cons_cons (a b : Int) (as bs : List Int) :
    dot (a :: as) (b :: bs) = a * b + dot as bs := rfl
@[simp] theorem vadd_cons_cons (a b : Int) (as bs : List Int) :
    vadd (a :: as) (b :: bs) = (a + b) :: vadd as bs := rfl
@[simp] theorem vadd_nil_left (x : List Int) : vadd [] x = [] := by cases x <;> rfl

theorem length_vadd (u v : List Int) (h : u.length = v.length) :
    (vadd u v).length = u.length := by
  induction u generalizing v with
  | nil => simp
  | cons a as ih =>
    cases v with
    | nil => exact (len_cons_nil h).elim
    | cons b bs => simp [ih bs (len_cons_cons h)]

theorem length_comb (p : Nat) (a : List Int) (W : List (List Int))
    (hW : ∀ w ∈ W, w.length = p) : (comb p a W).length = p := by
  induction a generalizing W with
  | nil => cases W <;> simp [comb]
  | cons x as ih =>
    cases W with
    | nil => simp [comb]
    | cons w ws =>
      have hw : w.length = p := hW w (by simp)
      have hws : ∀ v ∈ ws, v.length = p := fun v hv => hW v (by simp [hv])
      simp only [comb]
      rw [length_vadd _ _ (by simp [smul, hw, ih ws hws])]
      simp [smul, hw]

theorem dot_vadd (u v x : List Int) (h : u.length = v.length) :
    dot (vadd u v) x = dot u x + dot v x := by
  induction u generalizing v x with
  | nil => cases v with
    | nil => simp
    | cons _ _ => exact (len_nil_cons h).elim
  | cons a as ih =>
    cases v with
    | nil => exact (len_cons_nil h).elim
    | cons b bs =>
      have h := len_cons_cons h
      cases x with
      | nil => simp
      | cons y ys =>
        simp only [vadd_cons_cons, dot_cons_cons, ih bs ys h, Int.add_mul, Int.add_assoc,
          Int.add_left_comm (b * y) (dot as ys) (dot bs ys)]

theorem dot_smul (c : Int) (w x : List Int) : dot (smul c w) x = c * dot w x := by
  induction w generalizing x with
  | nil => simp [smul]
  | cons a as ih =>
    cases x with
    | nil => simp [smul]
    | cons y ys =>
      have := ih ys
      simp only [smul, List.map_cons] at this ⊢
      simp only [dot_cons_cons, this, Int.mul_add, Int.mul_assoc]

theorem dot_replicate_zero (p : Nat) (x : List Int) : dot (List.replicate p 0) x = 0 := by
  induction p generalizing x with
  | zero => simp
  | succ n ih => cases x with
    | nil => simp [List.replicate_succ]
    | cons y ys => simp [List.replicate_succ, ih]

theorem dot_comm (a b : List Int) : dot a b = dot b a := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih => cases b with
    | nil => simp
    | cons y ys => simp [ih, Int.mul_comm]

theorem dot_vadd_right (a u v : List Int) (h : u.length = v.length) :
    dot a (vadd u v) = dot a u + dot a v := by
  rw [dot_comm, dot_vadd _ _ _ h, dot_comm u, dot_comm v]

@[simp] theorem mulVec_cons (r : List Int) (M : List (List Int)) (x : List Int) :
    mulVec (r :: M) x = dot r x :: mulVec M x := rfl

@[simp] theorem mulVec_nil (x : List Int) : mulVec [] x = [] := rfl

@[simp] theorem length_mulVec (M : List (List Int)) (x : List Int) :
    (mulVec M x).length = M.length := by simp [mulVec]

/-- The one piece of linear algebra everything rests on:
`a · (W x) = (aᵀ W) · x`. -/
theorem dot_mulVec (p : Nat) (a : List Int) (W : List (List Int)) (x : List Int)
    (hW : ∀ w ∈ W, w.length = p) : dot a (mulVec W x) = dot (comb p a W) x := by
  induction a generalizing W with
  | nil => cases W <;> simp [comb, dot_replicate_zero]
  | cons c as ih =>
    cases W with
    | nil => simp [comb, mulVec, dot_replicate_zero]
    | cons w ws =>
      have hw : w.length = p := hW w (by simp)
      have hws : ∀ v ∈ ws, v.length = p := fun v hv => hW v (by simp [hv])
      simp only [comb, mulVec, List.map_cons, dot_cons_cons]
      rw [dot_vadd _ _ _ (by simp [smul, hw, length_comb p as ws hws]), dot_smul]
      have := ih ws hws
      simp only [mulVec] at this
      rw [this]

/-- Two vectors of the same length with the same dot product against every
vector are equal (test against unit vectors). -/
theorem eq_of_dot_eq (u v : List Int) (hl : u.length = v.length)
    (h : ∀ x, dot u x = dot v x) : u = v := by
  induction u generalizing v with
  | nil => cases v with
    | nil => rfl
    | cons _ _ => exact (len_nil_cons hl).elim
  | cons a as ih =>
    cases v with
    | nil => exact (len_cons_nil hl).elim
    | cons b bs =>
      have hab : a = b := by have := h [1]; simpa using this
      have hrest : as = bs := ih bs (len_cons_cons hl) (fun ys => by
        have := h (0 :: ys); simpa using this)
      rw [hab, hrest]

end Forge.Checker.Lin

namespace Forge.Checker.Affine
open Forge.Checker.Lin

/-- An integral affine witness `w(x) = linear * x + offset`. -/
structure AffineCert where
  linear : List (List Int)
  offset : List Int
  deriving Repr, DecidableEq

/-- The witness term evaluated at `x`: `W x + d`. -/
def AffineCert.apply (w : AffineCert) (x : List Int) : List Int :=
  vadd (mulVec w.linear x) w.offset

/-- Per-row identities: for each row `(a, b, cᵢ)` of `(A, B, c)`,
`a · d = cᵢ` and `aᵀ W = b`. Rows must run out together. -/
def rowsOK (p : Nat) (W : List (List Int)) (d : List Int) :
    List (List Int) → List (List Int) → List Int → Bool
  | a :: A, b :: B, ci :: c => (dot a d == ci && comb p a W == b) && rowsOK p W d A B c
  | [], [], [] => true
  | _, _, _ => false

/-- Python's `_shape` plus the witness-shape tests of `check_affine_witness`. -/
def shapeOK (A B : List (List Int)) (c : List Int) (w : AffineCert) : Bool :=
  let k := (A.headD []).length
  let p := (B.headD []).length
  !A.isEmpty && A.length == B.length && A.length == c.length
    && k != 0 && p != 0
    && A.all (·.length == k) && B.all (·.length == p)
    && w.linear.length == k && w.offset.length == k && w.linear.all (·.length == p)

/-- The checker. Total, `Bool`-valued, no search. -/
def AffineCert.check (A B : List (List Int)) (c : List Int) (w : AffineCert) : Bool :=
  shapeOK A B c w && rowsOK (B.headD []).length w.linear w.offset A B c

theorem rowsOK_sound (p : Nat) (W : List (List Int)) (d : List Int)
    (hW : ∀ w ∈ W, w.length = p) (hd : W.length = d.length) (x : List Int) :
    ∀ (A B : List (List Int)) (c : List Int), rowsOK p W d A B c = true →
      mulVec A (vadd (mulVec W x) d) = vadd (mulVec B x) c := by
  intro A
  induction A with
  | nil => intro B c h; cases B <;> cases c <;> first | rfl | exact Bool.noConfusion h
  | cons a A ih =>
    intro B c h
    cases B with
    | nil => cases c <;> simp [rowsOK] at h
    | cons b B => cases c with
      | nil => simp [rowsOK] at h
      | cons ci c =>
        simp only [rowsOK, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [mulVec_cons, mulVec_cons, vadd_cons_cons, ih B c h3,
          dot_vadd_right _ _ _ (by simp [hd]), dot_mulVec p a W x hW, h2, h1]

theorem rowsOK_complete (p : Nat) (W : List (List Int)) (d : List Int)
    (hW : ∀ w ∈ W, w.length = p) (hd : W.length = d.length) :
    ∀ (A B : List (List Int)) (c : List Int),
      A.length = B.length → A.length = c.length → (∀ b ∈ B, b.length = p) →
      (∀ x, mulVec A (vadd (mulVec W x) d) = vadd (mulVec B x) c) →
      rowsOK p W d A B c = true := by
  intro A
  induction A with
  | nil =>
    intro B c hB hc _ _
    cases B with
    | cons _ _ => exact (len_nil_cons hB).elim
    | nil => cases c with
      | cons _ _ => exact (len_nil_cons hc).elim
      | nil => rfl
  | cons a A ih =>
    intro B c hB hc hBl h
    cases B with
    | nil => exact (len_cons_nil hB).elim
    | cons b B => cases c with
      | nil => exact (len_cons_nil hc).elim
      | cons ci c =>
        have hrow : ∀ x, dot (comb p a W) x + dot a d = dot b x + ci ∧
            mulVec A (vadd (mulVec W x) d) = vadd (mulVec B x) c := by
          intro x
          have := h x
          simp only [mulVec_cons, vadd_cons_cons, List.cons.injEq] at this
          rw [dot_vadd_right _ _ _ (by simp [hd]), dot_mulVec p a W x hW] at this
          exact this
        have hdc : dot a d = ci := by
          have := (hrow []).1; simpa using this
        have hcomb : comb p a W = b := by
          apply eq_of_dot_eq
          · rw [length_comb p a W hW, hBl b (by simp)]
          · intro x; have := (hrow x).1; omega
        simp only [rowsOK, Bool.and_eq_true, beq_iff_eq]
        exact ⟨⟨hdc, hcomb⟩, ih B c (len_cons_cons hB) (len_cons_cons hc)
          (fun b hb => hBl b (by simp [hb])) (fun x => (hrow x).2)⟩

theorem shapeOK_facts {A B : List (List Int)} {c : List Int} {w : AffineCert}
    (h : shapeOK A B c w = true) :
    (∀ r ∈ w.linear, r.length = (B.headD []).length) ∧ w.linear.length = w.offset.length
      ∧ A.length = B.length ∧ A.length = c.length
      ∧ (∀ b ∈ B, b.length = (B.headD []).length) := by
  simp only [shapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, h2⟩, h3⟩, _⟩, _⟩, _⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨fun r hr => by simpa using h10 r hr, by omega, h2, h3, fun b hb => by simpa using h7 b hb⟩

/-- SOUNDNESS. If the check passes then, for every `x`, the integer vector
`w(x) = W x + d` solves `A w = B x + c`. -/
theorem AffineCert.sound (A B : List (List Int)) (c : List Int) (w : AffineCert)
    (h : w.check A B c = true) (x : List Int) :
    mulVec A (w.apply x) = vadd (mulVec B x) c := by
  simp only [AffineCert.check, Bool.and_eq_true] at h
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hW, hd, _, _, _⟩ := shapeOK_facts hs
  exact rowsOK_sound _ _ _ hW hd x A B c hr

/-- EXACTNESS. The checker accepts precisely the well-shaped certificates whose
affine map solves the system for every `x`. -/
theorem AffineCert.check_iff (A B : List (List Int)) (c : List Int) (w : AffineCert) :
    w.check A B c = true ↔
      shapeOK A B c w = true ∧ ∀ x, mulVec A (w.apply x) = vadd (mulVec B x) c := by
  constructor
  · intro h
    refine ⟨?_, AffineCert.sound A B c w h⟩
    simp only [AffineCert.check, Bool.and_eq_true] at h
    exact h.1
  · rintro ⟨hs, hx⟩
    obtain ⟨hW, hd, hB, hc, hBl⟩ := shapeOK_facts hs
    simp only [AffineCert.check, hs, Bool.true_and]
    exact rowsOK_complete _ _ _ hW hd A B c hB hc hBl hx

end Forge.Checker.Affine

#print axioms Forge.Checker.Lin.dot_mulVec
#print axioms Forge.Checker.Lin.eq_of_dot_eq
#print axioms Forge.Checker.Affine.AffineCert.sound
#print axioms Forge.Checker.Affine.AffineCert.check_iff
