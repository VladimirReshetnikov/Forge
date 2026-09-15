/-
Generated from exact certificates that passed the Python checker.
STATUS: NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No `sorry`, extra axiom, `native_decide`, or external solver is used here.
Compilation with the reader's compatible Lean/Mathlib installation is required.
-/
import Mathlib

namespace ForgeArtifacts

def acc_power_0 : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_power_0 n (a + (((1 : ℚ))))

theorem invariant_power_0 (n : ℕ) (a : ℚ) :
    acc_power_0 n a = (((1 : ℚ) * (a)) + ((1 : ℚ) * ((n : ℚ)))) := by
  induction n generalizing a with
  | zero => norm_num [acc_power_0]
  | succ n ih =>
    rw [acc_power_0, ih]
    push_cast <;> ring

def acc_power_1 : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_power_1 n (a + (((1 : ℚ) * ((n : ℚ)))))

theorem invariant_power_1 (n : ℕ) (a : ℚ) :
    acc_power_1 n a = (((1 : ℚ) * (a)) + (((-1 : ℚ) / 2) * ((n : ℚ))) + (((1 : ℚ) / 2) * ((n : ℚ)) ^ 2)) := by
  induction n generalizing a with
  | zero => norm_num [acc_power_1]
  | succ n ih =>
    rw [acc_power_1, ih]
    push_cast <;> ring

def acc_power_2 : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_power_2 n (a + (((1 : ℚ) * ((n : ℚ)) ^ 2)))

theorem invariant_power_2 (n : ℕ) (a : ℚ) :
    acc_power_2 n a = (((1 : ℚ) * (a)) + (((1 : ℚ) / 6) * ((n : ℚ))) + (((-1 : ℚ) / 2) * ((n : ℚ)) ^ 2) + (((1 : ℚ) / 3) * ((n : ℚ)) ^ 3)) := by
  induction n generalizing a with
  | zero => norm_num [acc_power_2]
  | succ n ih =>
    rw [acc_power_2, ih]
    push_cast <;> ring

def acc_power_3 : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_power_3 n (a + (((1 : ℚ) * ((n : ℚ)) ^ 3)))

theorem invariant_power_3 (n : ℕ) (a : ℚ) :
    acc_power_3 n a = (((1 : ℚ) * (a)) + (((1 : ℚ) / 4) * ((n : ℚ)) ^ 2) + (((-1 : ℚ) / 2) * ((n : ℚ)) ^ 3) + (((1 : ℚ) / 4) * ((n : ℚ)) ^ 4)) := by
  induction n generalizing a with
  | zero => norm_num [acc_power_3]
  | succ n ih =>
    rw [acc_power_3, ih]
    push_cast <;> ring

def acc_power_4 : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_power_4 n (a + (((1 : ℚ) * ((n : ℚ)) ^ 4)))

theorem invariant_power_4 (n : ℕ) (a : ℚ) :
    acc_power_4 n a = (((1 : ℚ) * (a)) + (((-1 : ℚ) / 30) * ((n : ℚ))) + (((1 : ℚ) / 3) * ((n : ℚ)) ^ 3) + (((-1 : ℚ) / 2) * ((n : ℚ)) ^ 4) + (((1 : ℚ) / 5) * ((n : ℚ)) ^ 5)) := by
  induction n generalizing a with
  | zero => norm_num [acc_power_4]
  | succ n ih =>
    rw [acc_power_4, ih]
    push_cast <;> ring

def acc_power_5 : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_power_5 n (a + (((1 : ℚ) * ((n : ℚ)) ^ 5)))

theorem invariant_power_5 (n : ℕ) (a : ℚ) :
    acc_power_5 n a = (((1 : ℚ) * (a)) + (((-1 : ℚ) / 12) * ((n : ℚ)) ^ 2) + (((5 : ℚ) / 12) * ((n : ℚ)) ^ 4) + (((-1 : ℚ) / 2) * ((n : ℚ)) ^ 5) + (((1 : ℚ) / 6) * ((n : ℚ)) ^ 6)) := by
  induction n generalizing a with
  | zero => norm_num [acc_power_5]
  | succ n ih =>
    rw [acc_power_5, ih]
    push_cast <;> ring

def acc_power_6 : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_power_6 n (a + (((1 : ℚ) * ((n : ℚ)) ^ 6)))

theorem invariant_power_6 (n : ℕ) (a : ℚ) :
    acc_power_6 n a = (((1 : ℚ) * (a)) + (((1 : ℚ) / 42) * ((n : ℚ))) + (((-1 : ℚ) / 6) * ((n : ℚ)) ^ 3) + (((1 : ℚ) / 2) * ((n : ℚ)) ^ 5) + (((-1 : ℚ) / 2) * ((n : ℚ)) ^ 6) + (((1 : ℚ) / 7) * ((n : ℚ)) ^ 7)) := by
  induction n generalizing a with
  | zero => norm_num [acc_power_6]
  | succ n ih =>
    rw [acc_power_6, ih]
    push_cast <;> ring

def acc_power_7 : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_power_7 n (a + (((1 : ℚ) * ((n : ℚ)) ^ 7)))

theorem invariant_power_7 (n : ℕ) (a : ℚ) :
    acc_power_7 n a = (((1 : ℚ) * (a)) + (((1 : ℚ) / 12) * ((n : ℚ)) ^ 2) + (((-7 : ℚ) / 24) * ((n : ℚ)) ^ 4) + (((7 : ℚ) / 12) * ((n : ℚ)) ^ 6) + (((-1 : ℚ) / 2) * ((n : ℚ)) ^ 7) + (((1 : ℚ) / 8) * ((n : ℚ)) ^ 8)) := by
  induction n generalizing a with
  | zero => norm_num [acc_power_7]
  | succ n ih =>
    rw [acc_power_7, ih]
    push_cast <;> ring

def acc_power_8 : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_power_8 n (a + (((1 : ℚ) * ((n : ℚ)) ^ 8)))

theorem invariant_power_8 (n : ℕ) (a : ℚ) :
    acc_power_8 n a = (((1 : ℚ) * (a)) + (((-1 : ℚ) / 30) * ((n : ℚ))) + (((2 : ℚ) / 9) * ((n : ℚ)) ^ 3) + (((-7 : ℚ) / 15) * ((n : ℚ)) ^ 5) + (((2 : ℚ) / 3) * ((n : ℚ)) ^ 7) + (((-1 : ℚ) / 2) * ((n : ℚ)) ^ 8) + (((1 : ℚ) / 9) * ((n : ℚ)) ^ 9)) := by
  induction n generalizing a with
  | zero => norm_num [acc_power_8]
  | succ n ih =>
    rw [acc_power_8, ih]
    push_cast <;> ring

def acc_quadratic_increment : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_quadratic_increment n (a + (((1 : ℚ)) + ((2 : ℚ) * ((n : ℚ)))))

theorem invariant_quadratic_increment (n : ℕ) (a : ℚ) :
    acc_quadratic_increment n a = (((1 : ℚ) * (a)) + ((1 : ℚ) * ((n : ℚ)) ^ 2)) := by
  induction n generalizing a with
  | zero => norm_num [acc_quadratic_increment]
  | succ n ih =>
    rw [acc_quadratic_increment, ih]
    push_cast <;> ring

def acc_signed_cubic : ℕ → ℚ → ℚ
  | 0, a => a
  | n + 1, a => acc_signed_cubic n (a + (((7 : ℚ)) + ((-5 : ℚ) * ((n : ℚ))) + ((3 : ℚ) * ((n : ℚ)) ^ 3)))

theorem invariant_signed_cubic (n : ℕ) (a : ℚ) :
    acc_signed_cubic n a = (((1 : ℚ) * (a)) + (((19 : ℚ) / 2) * ((n : ℚ))) + (((-7 : ℚ) / 4) * ((n : ℚ)) ^ 2) + (((-3 : ℚ) / 2) * ((n : ℚ)) ^ 3) + (((3 : ℚ) / 4) * ((n : ℚ)) ^ 4)) := by
  induction n generalizing a with
  | zero => norm_num [acc_signed_cubic]
  | succ n ih =>
    rw [acc_signed_cubic, ih]
    push_cast <;> ring

end ForgeArtifacts
