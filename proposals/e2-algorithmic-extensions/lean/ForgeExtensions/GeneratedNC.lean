/- Generated ordinary proof scripts. NOT_COMPILED in this run. -/
import Mathlib
set_option autoImplicit false
namespace ForgeExtensions

theorem commuting_idempotent_join {R : Type*} [Ring R] (a b : R)
    (h0 : ((-(a)) + (a * a)) = 0)
    (h1 : ((-(b)) + (b * b)) = 0)
    (h2 : ((a * b) + (-(b * a))) = 0)
    : ((-(a)) + (a * a) + (-(a * a * b)) + ((2 : R) * (a * b)) + (-(a * b * a)) + (a * b * a * b) + (-(a * b * b)) + (-(b)) + (b * a) + (-(b * a * b)) + (b * b)) = 0 := by
  calc
    _ = (((1 : R) * ((-(a)) + (a * a)) * (1 : R)) + ((1 : R) * ((-(b)) + (b * b)) * (1 : R)) + (-((1 : R) * ((-(a)) + (a * a)) * (b))) + (-((b) * ((-(a)) + (a * a)) * (1 : R))) + (-((a) * ((-(b)) + (b * b)) * (1 : R))) + (-((1 : R) * ((a * b) + (-(b * a))) * (a))) + ((b) * ((-(a)) + (a * a)) * (b)) + ((1 : R) * ((a * b) + (-(b * a))) * (a * b))) := by noncomm_ring
    _ = 0 := by simp only [h0, h1, h2, mul_zero, zero_mul, add_zero, zero_add, neg_zero]

theorem weyl_commutator_4 {R : Type*} [Ring R] (a b : R)
    (h0 : ((-(1 : R)) + (a * b) + (-(b * a))) = 0)
    : ((a * b * b * b * b) + ((-4 : R) * (b * b * b)) + (-(b * b * b * b * a))) = 0 := by
  calc
    _ = (((1 : R) * ((-(1 : R)) + (a * b) + (-(b * a))) * (b * b * b)) + ((b) * ((-(1 : R)) + (a * b) + (-(b * a))) * (b * b)) + ((b * b) * ((-(1 : R)) + (a * b) + (-(b * a))) * (b)) + ((b * b * b) * ((-(1 : R)) + (a * b) + (-(b * a))) * (1 : R))) := by noncomm_ring
    _ = 0 := by simp only [h0, mul_zero, zero_mul, add_zero, zero_add, neg_zero]

end ForgeExtensions
#print axioms ForgeExtensions.commuting_idempotent_join
#print axioms ForgeExtensions.weyl_commutator_4
