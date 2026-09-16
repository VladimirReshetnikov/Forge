/-
STATUS: NOT_RUN. This environment has no Lean or elan executable.
Target: leanprover/lean4:v4.34.0. Core Lean only.

This is a small proposed arithmetic/one-step lemma specimen, NOT a certificate
checker, source reifier, or implemented forge tactic. No successful compilation
or axiom inventory is claimed. There are no sorry/admit placeholders.
-/
import Lean
set_option autoImplicit false

namespace ForgeInfiniteSpecimen

def preScalar (consume produce target : Nat) : Nat :=
  consume + (target - produce)

theorem preScalar_iff (a z b x : Nat) :
    preScalar a z b ≤ x ↔ a ≤ x ∧ b ≤ x - a + z := by
  unfold preScalar
  omega

abbrev Vec (d : Nat) := Fin d → Nat

def VLe {d : Nat} (a b : Vec d) : Prop := ∀ i, a i ≤ b i

def preVector {d : Nat} (a z b : Vec d) : Vec d :=
  fun i => preScalar (a i) (z i) (b i)

def postVector {d : Nat} (a z x : Vec d) : Vec d :=
  fun i => x i - a i + z i

theorem preVector_iff {d : Nat} (a z b x : Vec d) :
    VLe (preVector a z b) x ↔ VLe a x ∧ VLe b (postVector a z x) := by
  constructor
  · intro h
    constructor
    · intro i
      exact ((preScalar_iff (a i) (z i) (b i) (x i)).mp (h i)).1
    · intro i
      exact ((preScalar_iff (a i) (z i) (b i) (x i)).mp (h i)).2
  · intro h i
    exact (preScalar_iff (a i) (z i) (b i) (x i)).mpr ⟨h.1 i, h.2 i⟩

def Hit {d : Nat} (basis : List (Vec d)) (x : Vec d) : Prop :=
  ∃ b, b ∈ basis ∧ VLe b x

/-- The local step needed by a backward-closed unsafe-region certificate.
    The complete certificate theorem must also check initial separation,
    original bad-set inclusion, and every original transition. -/
theorem avoid_step {d : Nat} (src dst : List (Vec d)) (a z x : Vec d)
    (closed : ∀ b, b ∈ dst → Hit src (preVector a z b))
    (enabled : VLe a x)
    (notHit : ¬ Hit src x) : ¬ Hit dst (postVector a z x) := by
  intro h
  obtain ⟨b, hb, hby⟩ := h
  have hp : VLe (preVector a z b) x :=
    (preVector_iff a z b x).mpr ⟨enabled, hby⟩
  obtain ⟨c, hc, hcp⟩ := closed b hb
  exact notHit ⟨c, hc, fun i => Nat.le_trans (hcp i) (hp i)⟩

#print axioms preScalar_iff
#print axioms preVector_iff
#print axioms avoid_step
end ForgeInfiniteSpecimen
