/-
NOT COMPILED. A hand-written List/Int sketch theorem, not synthesis output and
not acceptance of Leant's original Church-encoded query. Transport to a Church
provider requires an explicit representation/fold law; see the article.
-/
import Lean
set_option autoImplicit false
set_option debug.skipKernelTC false
namespace ForgeExtensions
universe u

def indexStep {A : Type u} (d a : A) (k : Int → A) (i : Int) : A :=
  if i < 0 then d else if i = 0 then a else k (i - 1)

def recursiveIndex {A : Type u} (d : A) : List A → Int → A
  | [], _ => d
  | a :: xs, i => indexStep d a (recursiveIndex d xs) i

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

#print axioms ForgeExtensions.foldIndex_eq_recursiveIndex
end ForgeExtensions
