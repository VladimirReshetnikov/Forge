/-
  Forge: the semantic induction principles the closure workers lower to.

  MERGED from the extension round. Five of the nine proposals independently
  wrote a `Reachable` inductive with the same invariant theorem, and five wrote
  a word-fold with the same preservation theorem; those are merged here once.
  The distinct additions are kept and attributed:

    reachable_invariant   e1, e2, e4, e6, e7, e8 -- six spellings, one theorem
    run, run_invariant    e3, e4, e5, e6, e9
    run_relation          e3, e4
    run_observation       e3
    run_map               e3 (run_map), e6 (simulateWord), e9 (run_simulation)
    observation_constant  e9
    foldl_preserves       e1
    close_ranked_calls    e7

  STATUS: this file elaborates against leanprover/lean4:v4.34.0 in the merge
  environment, and every theorem below reports no axiom dependencies. That is
  all it establishes. It is not a reflected checker, not a source reifier, and
  not an implementation of a `forge` tactic. None exists.
-/
import Lean
set_option autoImplicit false

namespace ForgeClosure

universe u v w z

/-- States reachable from an initial predicate by a step relation. -/
inductive Reachable {S : Type u} (Initial : S → Prop) (Step : S → S → Prop) : S → Prop
  | initial {s : S} : Initial s → Reachable Initial Step s
  | advance {s t : S} : Reachable Initial Step s → Step s t → Reachable Initial Step t

/--
  The target of every invariant certificate in this collection. Instantiating
  `P` with a finite conjunction of polynomial equations lowers either invariant
  family -- constant multipliers or bounded polynomial multipliers -- to this
  one induction. What the certificate supplies is `base` and `closed`.
-/
theorem reachable_invariant {S : Type u}
    {Initial : S → Prop} {Step : S → S → Prop} {P : S → Prop}
    (base : ∀ s, Initial s → P s)
    (closed : ∀ s t, P s → Step s t → P t)
    {s : S} (h : Reachable Initial Step s) : P s := by
  induction h with
  | initial hi => exact base _ hi
  | advance _ hstep ih => exact closed _ _ ih hstep

/-- Finite-word execution, with the first input symbol executed first. -/
def run {S : Type u} {A : Type v} (step : S → A → S) : S → List A → S
  | s, [] => s
  | s, a :: rest => run step (step s a) rest

/-- What an observable-space closure certificate discharges, once per action. -/
theorem run_invariant {S : Type u} {A : Type v}
    (step : S → A → S) (I : S → Prop)
    (preserve : ∀ s a, I s → I (step s a))
    (s : S) (hs : I s) (word : List A) : I (run step s word) := by
  induction word generalizing s with
  | nil => exact hs
  | cons a rest ih => exact ih (step s a) (preserve s a hs)

/--
  Two machines reading the same input. This is the shape an equivalence goal
  takes after the product construction: equal output needs neither equal
  internal states nor equal state dimensions.
-/
theorem run_relation {S : Type u} {T : Type v} {A : Type w}
    (left : S → A → S) (right : T → A → T) (R : S → T → Prop)
    (preserve : ∀ s t a, R s t → R (left s a) (right t a))
    (s : S) (t : T) (h : R s t) (word : List A) :
    R (run left s word) (run right t word) := by
  induction word generalizing s t with
  | nil => exact h
  | cons a rest ih => exact ih (left s a) (right t a) (preserve s t a h)

/-- Observation equality, from a relation that preserves both steps. -/
theorem run_observation {S : Type u} {T : Type v} {A : Type w} {O : Type z}
    (left : S → A → S) (right : T → A → T)
    (observeLeft : S → O) (observeRight : T → O) (R : S → T → Prop)
    (preserve : ∀ s t a, R s t → R (left s a) (right t a))
    (agree : ∀ s t, R s t → observeLeft s = observeRight t)
    (s : S) (t : T) (h : R s t) (word : List A) :
    observeLeft (run left s word) = observeRight (run right t word) :=
  agree _ _ (run_relation left right R preserve s t h word)

/--
  A commuting step map transports every finite execution. This is the source
  bridge in its generic form: `encode` is the summary, and `commute` is the
  per-constructor compatibility obligation that a finite table does NOT
  discharge by itself.
-/
theorem run_map {S : Type u} {T : Type v} {A : Type w}
    (source : S → A → S) (target : T → A → T) (encode : S → T)
    (commute : ∀ s a, encode (source s a) = target (encode s) a)
    (s : S) (word : List A) :
    encode (run source s word) = run target (encode s) word := by
  induction word generalizing s with
  | nil => rfl
  | cons a rest ih =>
    change encode (run source (source s a) rest) =
      run target (target (encode s) a) rest
    rw [ih, commute]

/--
  The observable-closure conclusion, assembled from `run_map`: a small certified
  state summarises a large one, and its observation is constant along it.
-/
theorem observation_constant {S : Type u} {T : Type v} {A : Type w} {O : Type z}
    (step : S → A → S) (small : T → A → T) (embed : T → S)
    (observe : S → O) (wanted : O) (initial : S) (seed : T)
    (hinit : initial = embed seed)
    (commute : ∀ t a, embed (small t a) = step (embed t) a)
    (hout : ∀ t, observe (embed t) = wanted) (word : List A) :
    observe (run step initial word) = wanted := by
  rw [hinit, ← run_map small step embed commute seed word]
  exact hout (run small seed word)

/-- The left-fold form, for a source function written with an accumulator. -/
theorem foldl_preserves {S : Type u} {A : Type v}
    (step : S → A → S) (I : S → Prop)
    (preserve : ∀ s a, I s → I (step s a)) :
    ∀ (xs : List A) (s : S), I s → I (xs.foldl step s) := by
  intro xs
  induction xs with
  | nil => intro s hs; exact hs
  | cons a rest ih => intro s hs; exact ih (step s a) (preserve s a hs)

/--
  What the cyclic-obligation compiler lowers to. The only recursive authority
  is the induction hypothesis supplied by the well-founded recursor: no node
  theorem is assumed while its component is being checked.

  A production compiler must still construct the tagged state `S`, the relation
  `r`, its well-foundedness proof, and `localProof`, in the original Lean
  context and with each edge's whole dependent telescope mapped.
-/
theorem close_ranked_calls {S : Sort u} (r : S → S → Prop)
    (wf : WellFounded r) (P : S → Prop)
    (localProof : ∀ s, (∀ t, r t s → P t) → P s) : ∀ s, P s :=
  fun s => wf.induction s localProof

#print axioms ForgeClosure.reachable_invariant
#print axioms ForgeClosure.run_invariant
#print axioms ForgeClosure.run_relation
#print axioms ForgeClosure.run_observation
#print axioms ForgeClosure.run_map
#print axioms ForgeClosure.observation_constant
#print axioms ForgeClosure.foldl_preserves
#print axioms ForgeClosure.close_ranked_calls

end ForgeClosure
