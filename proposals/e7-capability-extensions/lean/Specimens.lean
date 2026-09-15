/-
  Forge extension proof specimens — NOT COMPILED in the accompanying run.
  No `forge` tactic is implemented here. These are small proposed core lemmas
  for the integration gates in the article, not acceptance receipts.
-/
import Lean
set_option autoImplicit false

namespace ForgeExtensions
universe u v

def foldR {A : Type u} {R : Type v} (step : A → R → R) (base : R) : List A → R
  | [] => base
  | h :: xs => step h (foldR step base xs)

def indexAlgebra {A : Type u} (d h : A) (k : Int → A) (i : Int) : A :=
  if i < 0 then d else if i = 0 then h else k (i - 1)

def indexSpec {A : Type u} (d : A) : List A → Int → A
  | [] => fun _ => d
  | h :: xs => indexAlgebra d h (indexSpec d xs)

theorem foldR_index {A : Type u} (d : A) (xs : List A) :
    foldR (indexAlgebra d) (fun _ => d) xs = indexSpec d xs := by
  induction xs with
  | nil => rfl
  | cons h xs ih => exact congrArg (indexAlgebra d h) ih

abbrev Church (A : Type u) := (R : Type u) → (A → R → R) → R → R

def encode {A : Type u} (xs : List A) : Church A :=
  fun _ step base => foldR step base xs

def churchIndex {A : Type u} (d : A) (xs : Church A) : Int → A :=
  xs (Int → A) (indexAlgebra d) (fun _ => d)

theorem churchIndex_encode {A : Type u} (d : A) (xs : List A) :
    churchIndex d (encode xs) = indexSpec d xs :=
  foldR_index d xs

-- This theorem is explicitly about encodings of lists, not arbitrary values
-- inhabiting the impredicative-looking Church signature.

inductive Reachable {S : Type u} (Initial : S → Prop) (Step : S → S → Prop) : S → Prop
  | initial {s : S} : Initial s → Reachable Initial Step s
  | next {s t : S} : Reachable Initial Step s → Step s t → Reachable Initial Step t

theorem invariant_on_reachable {S : Type u} {Initial : S → Prop}
    {Step : S → S → Prop} (P : S → Prop)
    (base : ∀ s, Initial s → P s)
    (step : ∀ s t, Step s t → P s → P t)
    {s : S} (h : Reachable Initial Step s) : P s := by
  induction h with
  | initial hs => exact base _ hs
  | next _ hst ih => exact step _ _ hst ih

-- Instantiating P with a finite conjunction of polynomial equations lowers
-- either invariant certificate family to this same induction theorem.

theorem close_ranked_calls {S : Sort u} (r : S → S → Prop)
    (wf : WellFounded r) (P : S → Prop)
    (localProof : ∀ s, (∀ t, r t s → P t) → P s) : ∀ s, P s :=
  fun s => wf.induction s localProof

-- A production compiler must still construct the tagged state S, the relation
-- r, its well-foundedness proof, and localProof in the original Lean context.

#print axioms foldR_index
#print axioms churchIndex_encode
#print axioms invariant_on_reachable
#print axioms close_ranked_calls
end ForgeExtensions
