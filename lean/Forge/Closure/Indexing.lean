/-
  Forge: the fold-indexing specimen, and exactly where it stops.

  MERGED from e7-capability-extensions/lean/Specimens.lean (the Church half)
  and e8-invariant-ideals/lean/IndexingSketch.lean (the List/Int half). The two
  proposals wrote the same step algebra under different names and derived the
  same equation; it is proved once here, in the `List.foldr` spelling, and the
  Church statement is derived from it.

  STATUS: elaborates against leanprover/lean4:v4.34.0 with no axiom
  dependencies.

  WHAT THIS DOES NOT CLOSE, stated here because it is the claim most likely to
  be made on this file's behalf. `churchIndex_encode` is a theorem about
  `encode xs` for an ACTUAL FINITE LIST. It does not establish that every Lean
  value inhabiting the Church signature behaves as the encoding of a finite
  list; that needs a representation or parametricity hypothesis proved in the
  source theory. Nor is the source `Int` of a Haskell diagnostic automatically
  Lean's unbounded `Int`. Elaborating this file does not change what it says:
  it proves an equation between two ordinary-list definitions, and the original
  Church-encoded synthesis query remains open.
-/
import Lean
set_option autoImplicit false

namespace ForgeClosure

universe u v

/--
  The step algebra the contract forces: a three-way split on a signed index,
  with an ARBITRARY continuation `k`. Treating `k` as arbitrary is the decisive
  choice -- a candidate step may not exploit one guessed tail function that
  happens to fit a few examples.
-/
def indexStep {A : Type u} (d a : A) (k : Int → A) (i : Int) : A :=
  if i < 0 then d else if i = 0 then a else k (i - 1)

/-- The reference operation, written recursively. -/
def recursiveIndex {A : Type u} (d : A) : List A → Int → A
  | [], _ => d
  | a :: xs, i => indexStep d a (recursiveIndex d xs) i

/-- The same operation as a fold whose CARRIER is a function type. -/
def foldIndex {A : Type u} (d : A) (xs : List A) : Int → A :=
  xs.foldr (indexStep d) (fun _ => d)

theorem foldIndex_eq_recursiveIndex {A : Type u} (d : A) (xs : List A) :
    foldIndex d xs = recursiveIndex d xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    unfold foldIndex at ih ⊢
    change indexStep d a (xs.foldr (indexStep d) (fun _ => d)) =
      indexStep d a (recursiveIndex d xs)
    rw [ih]

abbrev Church (A : Type u) := (R : Type u) → (A → R → R) → R → R

def encode {A : Type u} (xs : List A) : Church A :=
  fun _ step base => xs.foldr step base

def churchIndex {A : Type u} (d : A) (c : Church A) : Int → A :=
  c (Int → A) (indexStep d) (fun _ => d)

/-- Holds for ENCODINGS OF LISTS. See the scope note at the top of this file. -/
theorem churchIndex_encode {A : Type u} (d : A) (xs : List A) :
    churchIndex d (encode xs) = recursiveIndex d xs :=
  foldIndex_eq_recursiveIndex d xs

#print axioms ForgeClosure.foldIndex_eq_recursiveIndex
#print axioms ForgeClosure.churchIndex_encode

end ForgeClosure
