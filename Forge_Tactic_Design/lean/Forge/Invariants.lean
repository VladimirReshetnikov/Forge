/- Generated from exact Python certificates.
   STATUS: source exported, NOT compiled or kernel-checked in this environment.
   No Forge search tactic is implemented in this directory. -/
import Mathlib

namespace ForgeReplay

def orbit {α : Type} (T : α → α) (s₀ : α) : Nat → α
  | 0 => s₀
  | n + 1 => T (orbit T s₀ n)

theorem orbit_invariant {α : Type} (T : α → α) (s₀ : α)
    (I : α → ℝ) (hbase : I s₀ = 0) (hstep : ∀ s, I (T s) = I s) :
    ∀ n, I (orbit T s₀ n) = 0 := by
  intro n
  induction n with
  | zero => simpa only [orbit] using hbase
  | succ n ih => simpa only [orbit, hstep] using ih

def state_power_0 := ((0 : ℝ), (0 : ℝ))
def step_power_0 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2)))
def invariant_power_0 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + (-1 : ℝ) * (s.1))
theorem preserved_power_0 (n : Nat) :
    invariant_power_0 (orbit step_power_0 state_power_0 n) = 0 := by
  apply orbit_invariant step_power_0 state_power_0 invariant_power_0
  · norm_num [invariant_power_0, state_power_0]
  · intro s
    dsimp [invariant_power_0, step_power_0]
    ring

def state_power_1 := ((0 : ℝ), (0 : ℝ))
def step_power_1 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + (1 : ℝ) * (s.1)))
def invariant_power_1 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + ((-1 : ℝ) / 2) * (s.1) + ((-1 : ℝ) / 2) * (s.1) ^ 2)
theorem preserved_power_1 (n : Nat) :
    invariant_power_1 (orbit step_power_1 state_power_1 n) = 0 := by
  apply orbit_invariant step_power_1 state_power_1 invariant_power_1
  · norm_num [invariant_power_1, state_power_1]
  · intro s
    dsimp [invariant_power_1, step_power_1]
    ring

def state_power_2 := ((0 : ℝ), (0 : ℝ))
def step_power_2 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + (2 : ℝ) * (s.1) + (1 : ℝ) * (s.1) ^ 2))
def invariant_power_2 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + ((-1 : ℝ) / 6) * (s.1) + ((-1 : ℝ) / 2) * (s.1) ^ 2 + ((-1 : ℝ) / 3) * (s.1) ^ 3)
theorem preserved_power_2 (n : Nat) :
    invariant_power_2 (orbit step_power_2 state_power_2 n) = 0 := by
  apply orbit_invariant step_power_2 state_power_2 invariant_power_2
  · norm_num [invariant_power_2, state_power_2]
  · intro s
    dsimp [invariant_power_2, step_power_2]
    ring

def state_power_3 := ((0 : ℝ), (0 : ℝ))
def step_power_3 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + (3 : ℝ) * (s.1) + (3 : ℝ) * (s.1) ^ 2 + (1 : ℝ) * (s.1) ^ 3))
def invariant_power_3 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + ((-1 : ℝ) / 4) * (s.1) ^ 2 + ((-1 : ℝ) / 2) * (s.1) ^ 3 + ((-1 : ℝ) / 4) * (s.1) ^ 4)
theorem preserved_power_3 (n : Nat) :
    invariant_power_3 (orbit step_power_3 state_power_3 n) = 0 := by
  apply orbit_invariant step_power_3 state_power_3 invariant_power_3
  · norm_num [invariant_power_3, state_power_3]
  · intro s
    dsimp [invariant_power_3, step_power_3]
    ring

def state_power_4 := ((0 : ℝ), (0 : ℝ))
def step_power_4 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + (4 : ℝ) * (s.1) + (6 : ℝ) * (s.1) ^ 2 + (4 : ℝ) * (s.1) ^ 3 + (1 : ℝ) * (s.1) ^ 4))
def invariant_power_4 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + ((1 : ℝ) / 30) * (s.1) + ((-1 : ℝ) / 3) * (s.1) ^ 3 + ((-1 : ℝ) / 2) * (s.1) ^ 4 + ((-1 : ℝ) / 5) * (s.1) ^ 5)
theorem preserved_power_4 (n : Nat) :
    invariant_power_4 (orbit step_power_4 state_power_4 n) = 0 := by
  apply orbit_invariant step_power_4 state_power_4 invariant_power_4
  · norm_num [invariant_power_4, state_power_4]
  · intro s
    dsimp [invariant_power_4, step_power_4]
    ring

def state_power_5 := ((0 : ℝ), (0 : ℝ))
def step_power_5 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + (5 : ℝ) * (s.1) + (10 : ℝ) * (s.1) ^ 2 + (10 : ℝ) * (s.1) ^ 3 + (5 : ℝ) * (s.1) ^ 4 + (1 : ℝ) * (s.1) ^ 5))
def invariant_power_5 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + ((1 : ℝ) / 12) * (s.1) ^ 2 + ((-5 : ℝ) / 12) * (s.1) ^ 4 + ((-1 : ℝ) / 2) * (s.1) ^ 5 + ((-1 : ℝ) / 6) * (s.1) ^ 6)
theorem preserved_power_5 (n : Nat) :
    invariant_power_5 (orbit step_power_5 state_power_5 n) = 0 := by
  apply orbit_invariant step_power_5 state_power_5 invariant_power_5
  · norm_num [invariant_power_5, state_power_5]
  · intro s
    dsimp [invariant_power_5, step_power_5]
    ring

def state_power_6 := ((0 : ℝ), (0 : ℝ))
def step_power_6 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + (6 : ℝ) * (s.1) + (15 : ℝ) * (s.1) ^ 2 + (20 : ℝ) * (s.1) ^ 3 + (15 : ℝ) * (s.1) ^ 4 + (6 : ℝ) * (s.1) ^ 5 + (1 : ℝ) * (s.1) ^ 6))
def invariant_power_6 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + ((-1 : ℝ) / 42) * (s.1) + ((1 : ℝ) / 6) * (s.1) ^ 3 + ((-1 : ℝ) / 2) * (s.1) ^ 5 + ((-1 : ℝ) / 2) * (s.1) ^ 6 + ((-1 : ℝ) / 7) * (s.1) ^ 7)
theorem preserved_power_6 (n : Nat) :
    invariant_power_6 (orbit step_power_6 state_power_6 n) = 0 := by
  apply orbit_invariant step_power_6 state_power_6 invariant_power_6
  · norm_num [invariant_power_6, state_power_6]
  · intro s
    dsimp [invariant_power_6, step_power_6]
    ring

def state_power_7 := ((0 : ℝ), (0 : ℝ))
def step_power_7 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + (7 : ℝ) * (s.1) + (21 : ℝ) * (s.1) ^ 2 + (35 : ℝ) * (s.1) ^ 3 + (35 : ℝ) * (s.1) ^ 4 + (21 : ℝ) * (s.1) ^ 5 + (7 : ℝ) * (s.1) ^ 6 + (1 : ℝ) * (s.1) ^ 7))
def invariant_power_7 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + ((-1 : ℝ) / 12) * (s.1) ^ 2 + ((7 : ℝ) / 24) * (s.1) ^ 4 + ((-7 : ℝ) / 12) * (s.1) ^ 6 + ((-1 : ℝ) / 2) * (s.1) ^ 7 + ((-1 : ℝ) / 8) * (s.1) ^ 8)
theorem preserved_power_7 (n : Nat) :
    invariant_power_7 (orbit step_power_7 state_power_7 n) = 0 := by
  apply orbit_invariant step_power_7 state_power_7 invariant_power_7
  · norm_num [invariant_power_7, state_power_7]
  · intro s
    dsimp [invariant_power_7, step_power_7]
    ring

def state_power_8 := ((0 : ℝ), (0 : ℝ))
def step_power_8 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + (8 : ℝ) * (s.1) + (28 : ℝ) * (s.1) ^ 2 + (56 : ℝ) * (s.1) ^ 3 + (70 : ℝ) * (s.1) ^ 4 + (56 : ℝ) * (s.1) ^ 5 + (28 : ℝ) * (s.1) ^ 6 + (8 : ℝ) * (s.1) ^ 7 + (1 : ℝ) * (s.1) ^ 8))
def invariant_power_8 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + ((1 : ℝ) / 30) * (s.1) + ((-2 : ℝ) / 9) * (s.1) ^ 3 + ((7 : ℝ) / 15) * (s.1) ^ 5 + ((-2 : ℝ) / 3) * (s.1) ^ 7 + ((-1 : ℝ) / 2) * (s.1) ^ 8 + ((-1 : ℝ) / 9) * (s.1) ^ 9)
theorem preserved_power_8 (n : Nat) :
    invariant_power_8 (orbit step_power_8 state_power_8 n) = 0 := by
  apply orbit_invariant step_power_8 state_power_8 invariant_power_8
  · norm_num [invariant_power_8, state_power_8]
  · intro s
    dsimp [invariant_power_8, step_power_8]
    ring

def state_random_0 := ((0 : ℝ), (-1 : ℝ))
def step_random_0 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((1 : ℝ) / 2) + (1 : ℝ) * (s.2) + (2 : ℝ) * (s.1) ^ 2 + ((4 : ℝ) / 5) * (s.1) ^ 3 + ((3 : ℝ) / 4) * (s.1) ^ 4 + (-5 : ℝ) * (s.1) ^ 5))
def invariant_random_0 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) + (1 : ℝ) * (s.2) + ((-97 : ℝ) / 120) * (s.1) + ((23 : ℝ) / 60) * (s.1) ^ 2 + ((-31 : ℝ) / 60) * (s.1) ^ 3 + ((271 : ℝ) / 120) * (s.1) ^ 4 + ((-53 : ℝ) / 20) * (s.1) ^ 5 + ((5 : ℝ) / 6) * (s.1) ^ 6)
theorem preserved_random_0 (n : Nat) :
    invariant_random_0 (orbit step_random_0 state_random_0 n) = 0 := by
  apply orbit_invariant step_random_0 state_random_0 invariant_random_0
  · norm_num [invariant_random_0, state_random_0]
  · intro s
    dsimp [invariant_random_0, step_random_0]
    ring

def state_random_1 := ((0 : ℝ), (-1 : ℝ))
def step_random_1 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((4 : ℝ) / 5) + (1 : ℝ) * (s.2) + ((3 : ℝ) / 5) * (s.1) + ((-7 : ℝ) / 4) * (s.1) ^ 2 + ((5 : ℝ) / 3) * (s.1) ^ 3))
def invariant_random_1 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) + (1 : ℝ) * (s.2) + ((-5 : ℝ) / 24) * (s.1) + ((-191 : ℝ) / 120) * (s.1) ^ 2 + ((17 : ℝ) / 12) * (s.1) ^ 3 + ((-5 : ℝ) / 12) * (s.1) ^ 4)
theorem preserved_random_1 (n : Nat) :
    invariant_random_1 (orbit step_random_1 state_random_1 n) = 0 := by
  apply orbit_invariant step_random_1 state_random_1 invariant_random_1
  · norm_num [invariant_random_1, state_random_1]
  · intro s
    dsimp [invariant_random_1, step_random_1]
    ring

def state_random_2 := ((0 : ℝ), (5 : ℝ))
def step_random_2 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-3 : ℝ) / 5) + (1 : ℝ) * (s.2)))
def invariant_random_2 (s : ℝ × ℝ) : ℝ :=
  ((-5 : ℝ) + (1 : ℝ) * (s.2) + ((3 : ℝ) / 5) * (s.1))
theorem preserved_random_2 (n : Nat) :
    invariant_random_2 (orbit step_random_2 state_random_2 n) = 0 := by
  apply orbit_invariant step_random_2 state_random_2 invariant_random_2
  · norm_num [invariant_random_2, state_random_2]
  · intro s
    dsimp [invariant_random_2, step_random_2]
    ring

def state_random_3 := ((0 : ℝ), (-1 : ℝ))
def step_random_3 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((-2 : ℝ) + (1 : ℝ) * (s.2)))
def invariant_random_3 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) + (1 : ℝ) * (s.2) + (2 : ℝ) * (s.1))
theorem preserved_random_3 (n : Nat) :
    invariant_random_3 (orbit step_random_3 state_random_3 n) = 0 := by
  apply orbit_invariant step_random_3 state_random_3 invariant_random_3
  · norm_num [invariant_random_3, state_random_3]
  · intro s
    dsimp [invariant_random_3, step_random_3]
    ring

def state_random_4 := ((0 : ℝ), (5 : ℝ))
def step_random_4 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-1 : ℝ) / 2) + (1 : ℝ) * (s.2) + (-1 : ℝ) * (s.1) + (-1 : ℝ) * (s.1) ^ 2 + ((-1 : ℝ) / 2) * (s.1) ^ 3 + ((1 : ℝ) / 3) * (s.1) ^ 4))
def invariant_random_4 (s : ℝ × ℝ) : ℝ :=
  ((-5 : ℝ) + (1 : ℝ) * (s.2) + ((8 : ℝ) / 45) * (s.1) + ((1 : ℝ) / 8) * (s.1) ^ 2 + ((-1 : ℝ) / 36) * (s.1) ^ 3 + ((7 : ℝ) / 24) * (s.1) ^ 4 + ((-1 : ℝ) / 15) * (s.1) ^ 5)
theorem preserved_random_4 (n : Nat) :
    invariant_random_4 (orbit step_random_4 state_random_4 n) = 0 := by
  apply orbit_invariant step_random_4 state_random_4 invariant_random_4
  · norm_num [invariant_random_4, state_random_4]
  · intro s
    dsimp [invariant_random_4, step_random_4]
    ring

def state_random_5 := ((0 : ℝ), (-5 : ℝ))
def step_random_5 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((-6 : ℝ) + (1 : ℝ) * (s.2)))
def invariant_random_5 (s : ℝ × ℝ) : ℝ :=
  ((5 : ℝ) + (1 : ℝ) * (s.2) + (6 : ℝ) * (s.1))
theorem preserved_random_5 (n : Nat) :
    invariant_random_5 (orbit step_random_5 state_random_5 n) = 0 := by
  apply orbit_invariant step_random_5 state_random_5 invariant_random_5
  · norm_num [invariant_random_5, state_random_5]
  · intro s
    dsimp [invariant_random_5, step_random_5]
    ring

def state_random_6 := ((0 : ℝ), (5 : ℝ))
def step_random_6 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((6 : ℝ) + (1 : ℝ) * (s.2) + ((1 : ℝ) / 2) * (s.1)))
def invariant_random_6 (s : ℝ × ℝ) : ℝ :=
  ((-5 : ℝ) + (1 : ℝ) * (s.2) + ((-23 : ℝ) / 4) * (s.1) + ((-1 : ℝ) / 4) * (s.1) ^ 2)
theorem preserved_random_6 (n : Nat) :
    invariant_random_6 (orbit step_random_6 state_random_6 n) = 0 := by
  apply orbit_invariant step_random_6 state_random_6 invariant_random_6
  · norm_num [invariant_random_6, state_random_6]
  · intro s
    dsimp [invariant_random_6, step_random_6]
    ring

def state_random_7 := ((0 : ℝ), (0 : ℝ))
def step_random_7 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-5 : ℝ) / 4) + (1 : ℝ) * (s.2) + ((7 : ℝ) / 3) * (s.1) + (5 : ℝ) * (s.1) ^ 3 + ((4 : ℝ) / 3) * (s.1) ^ 4 + ((-2 : ℝ) / 5) * (s.1) ^ 5 + (-2 : ℝ) * (s.1) ^ 6))
def invariant_random_7 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + ((3161 : ℝ) / 1260) * (s.1) + ((-49 : ℝ) / 20) * (s.1) ^ 2 + ((31 : ℝ) / 18) * (s.1) ^ 3 + ((-5 : ℝ) / 12) * (s.1) ^ 4 + ((8 : ℝ) / 15) * (s.1) ^ 5 + ((-14 : ℝ) / 15) * (s.1) ^ 6 + ((2 : ℝ) / 7) * (s.1) ^ 7)
theorem preserved_random_7 (n : Nat) :
    invariant_random_7 (orbit step_random_7 state_random_7 n) = 0 := by
  apply orbit_invariant step_random_7 state_random_7 invariant_random_7
  · norm_num [invariant_random_7, state_random_7]
  · intro s
    dsimp [invariant_random_7, step_random_7]
    ring

def state_random_8 := ((0 : ℝ), (-5 : ℝ))
def step_random_8 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((5 : ℝ) + (1 : ℝ) * (s.2) + (-7 : ℝ) * (s.1) + (-7 : ℝ) * (s.1) ^ 2 + (2 : ℝ) * (s.1) ^ 3 + (2 : ℝ) * (s.1) ^ 4))
def invariant_random_8 (s : ℝ × ℝ) : ℝ :=
  ((5 : ℝ) + (1 : ℝ) * (s.2) + ((-109 : ℝ) / 15) * (s.1) + ((-1 : ℝ) / 2) * (s.1) ^ 2 + ((8 : ℝ) / 3) * (s.1) ^ 3 + ((1 : ℝ) / 2) * (s.1) ^ 4 + ((-2 : ℝ) / 5) * (s.1) ^ 5)
theorem preserved_random_8 (n : Nat) :
    invariant_random_8 (orbit step_random_8 state_random_8 n) = 0 := by
  apply orbit_invariant step_random_8 state_random_8 invariant_random_8
  · norm_num [invariant_random_8, state_random_8]
  · intro s
    dsimp [invariant_random_8, step_random_8]
    ring

def state_random_9 := ((0 : ℝ), (-1 : ℝ))
def step_random_9 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((3 : ℝ) + (1 : ℝ) * (s.2) + (7 : ℝ) * (s.1) + (-1 : ℝ) * (s.1) ^ 2))
def invariant_random_9 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) + (1 : ℝ) * (s.2) + ((2 : ℝ) / 3) * (s.1) + (-4 : ℝ) * (s.1) ^ 2 + ((1 : ℝ) / 3) * (s.1) ^ 3)
theorem preserved_random_9 (n : Nat) :
    invariant_random_9 (orbit step_random_9 state_random_9 n) = 0 := by
  apply orbit_invariant step_random_9 state_random_9 invariant_random_9
  · norm_num [invariant_random_9, state_random_9]
  · intro s
    dsimp [invariant_random_9, step_random_9]
    ring

def state_random_10 := ((0 : ℝ), (0 : ℝ))
def step_random_10 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((2 : ℝ) + (1 : ℝ) * (s.2) + (-6 : ℝ) * (s.1) + (1 : ℝ) * (s.1) ^ 2 + (1 : ℝ) * (s.1) ^ 3 + ((-4 : ℝ) / 3) * (s.1) ^ 4))
def invariant_random_10 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) * (s.2) + ((-469 : ℝ) / 90) * (s.1) + ((13 : ℝ) / 4) * (s.1) ^ 2 + ((11 : ℝ) / 18) * (s.1) ^ 3 + ((-11 : ℝ) / 12) * (s.1) ^ 4 + ((4 : ℝ) / 15) * (s.1) ^ 5)
theorem preserved_random_10 (n : Nat) :
    invariant_random_10 (orbit step_random_10 state_random_10 n) = 0 := by
  apply orbit_invariant step_random_10 state_random_10 invariant_random_10
  · norm_num [invariant_random_10, state_random_10]
  · intro s
    dsimp [invariant_random_10, step_random_10]
    ring

def state_random_11 := ((0 : ℝ), (3 : ℝ))
def step_random_11 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-6 : ℝ) / 5) + (1 : ℝ) * (s.2) + ((5 : ℝ) / 3) * (s.1) + (1 : ℝ) * (s.1) ^ 2))
def invariant_random_11 (s : ℝ × ℝ) : ℝ :=
  ((-3 : ℝ) + (1 : ℝ) * (s.2) + ((28 : ℝ) / 15) * (s.1) + ((-1 : ℝ) / 3) * (s.1) ^ 2 + ((-1 : ℝ) / 3) * (s.1) ^ 3)
theorem preserved_random_11 (n : Nat) :
    invariant_random_11 (orbit step_random_11 state_random_11 n) = 0 := by
  apply orbit_invariant step_random_11 state_random_11 invariant_random_11
  · norm_num [invariant_random_11, state_random_11]
  · intro s
    dsimp [invariant_random_11, step_random_11]
    ring

def state_random_12 := ((0 : ℝ), (-5 : ℝ))
def step_random_12 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((7 : ℝ) / 4) + (1 : ℝ) * (s.2) + ((-6 : ℝ) / 5) * (s.1) + ((-5 : ℝ) / 2) * (s.1) ^ 2 + (-6 : ℝ) * (s.1) ^ 3 + ((3 : ℝ) / 5) * (s.1) ^ 4 + ((7 : ℝ) / 2) * (s.1) ^ 5))
def invariant_random_12 (s : ℝ × ℝ) : ℝ :=
  ((5 : ℝ) + (1 : ℝ) * (s.2) + ((-287 : ℝ) / 150) * (s.1) + ((137 : ℝ) / 120) * (s.1) ^ 2 + ((-71 : ℝ) / 30) * (s.1) ^ 3 + ((41 : ℝ) / 120) * (s.1) ^ 4 + ((163 : ℝ) / 100) * (s.1) ^ 5 + ((-7 : ℝ) / 12) * (s.1) ^ 6)
theorem preserved_random_12 (n : Nat) :
    invariant_random_12 (orbit step_random_12 state_random_12 n) = 0 := by
  apply orbit_invariant step_random_12 state_random_12 invariant_random_12
  · norm_num [invariant_random_12, state_random_12]
  · intro s
    dsimp [invariant_random_12, step_random_12]
    ring

def state_random_13 := ((0 : ℝ), (-3 : ℝ))
def step_random_13 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-1 : ℝ) / 2) + (1 : ℝ) * (s.2) + ((1 : ℝ) / 5) * (s.1)))
def invariant_random_13 (s : ℝ × ℝ) : ℝ :=
  ((3 : ℝ) + (1 : ℝ) * (s.2) + ((3 : ℝ) / 5) * (s.1) + ((-1 : ℝ) / 10) * (s.1) ^ 2)
theorem preserved_random_13 (n : Nat) :
    invariant_random_13 (orbit step_random_13 state_random_13 n) = 0 := by
  apply orbit_invariant step_random_13 state_random_13 invariant_random_13
  · norm_num [invariant_random_13, state_random_13]
  · intro s
    dsimp [invariant_random_13, step_random_13]
    ring

def state_random_14 := ((0 : ℝ), (4 : ℝ))
def step_random_14 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((-2 : ℝ) + (1 : ℝ) * (s.2)))
def invariant_random_14 (s : ℝ × ℝ) : ℝ :=
  ((-4 : ℝ) + (1 : ℝ) * (s.2) + (2 : ℝ) * (s.1))
theorem preserved_random_14 (n : Nat) :
    invariant_random_14 (orbit step_random_14 state_random_14 n) = 0 := by
  apply orbit_invariant step_random_14 state_random_14 invariant_random_14
  · norm_num [invariant_random_14, state_random_14]
  · intro s
    dsimp [invariant_random_14, step_random_14]
    ring

def state_random_15 := ((0 : ℝ), (-5 : ℝ))
def step_random_15 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((4 : ℝ) + (1 : ℝ) * (s.2) + (-1 : ℝ) * (s.1) + (-4 : ℝ) * (s.1) ^ 2 + ((-7 : ℝ) / 5) * (s.1) ^ 3 + ((-7 : ℝ) / 2) * (s.1) ^ 4))
def invariant_random_15 (s : ℝ × ℝ) : ℝ :=
  ((5 : ℝ) + (1 : ℝ) * (s.2) + ((-79 : ℝ) / 20) * (s.1) + ((-23 : ℝ) / 20) * (s.1) ^ 2 + ((9 : ℝ) / 5) * (s.1) ^ 3 + ((-7 : ℝ) / 5) * (s.1) ^ 4 + ((7 : ℝ) / 10) * (s.1) ^ 5)
theorem preserved_random_15 (n : Nat) :
    invariant_random_15 (orbit step_random_15 state_random_15 n) = 0 := by
  apply orbit_invariant step_random_15 state_random_15 invariant_random_15
  · norm_num [invariant_random_15, state_random_15]
  · intro s
    dsimp [invariant_random_15, step_random_15]
    ring

def state_random_16 := ((0 : ℝ), (-2 : ℝ))
def step_random_16 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((-2 : ℝ) + (1 : ℝ) * (s.2) + ((-1 : ℝ) / 5) * (s.1) + (2 : ℝ) * (s.1) ^ 2 + ((-7 : ℝ) / 5) * (s.1) ^ 3))
def invariant_random_16 (s : ℝ × ℝ) : ℝ :=
  ((2 : ℝ) + (1 : ℝ) * (s.2) + ((47 : ℝ) / 30) * (s.1) + ((29 : ℝ) / 20) * (s.1) ^ 2 + ((-41 : ℝ) / 30) * (s.1) ^ 3 + ((7 : ℝ) / 20) * (s.1) ^ 4)
theorem preserved_random_16 (n : Nat) :
    invariant_random_16 (orbit step_random_16 state_random_16 n) = 0 := by
  apply orbit_invariant step_random_16 state_random_16 invariant_random_16
  · norm_num [invariant_random_16, state_random_16]
  · intro s
    dsimp [invariant_random_16, step_random_16]
    ring

def state_random_17 := ((0 : ℝ), (4 : ℝ))
def step_random_17 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((2 : ℝ) / 5) + (1 : ℝ) * (s.2) + ((1 : ℝ) / 3) * (s.1)))
def invariant_random_17 (s : ℝ × ℝ) : ℝ :=
  ((-4 : ℝ) + (1 : ℝ) * (s.2) + ((-7 : ℝ) / 30) * (s.1) + ((-1 : ℝ) / 6) * (s.1) ^ 2)
theorem preserved_random_17 (n : Nat) :
    invariant_random_17 (orbit step_random_17 state_random_17 n) = 0 := by
  apply orbit_invariant step_random_17 state_random_17 invariant_random_17
  · norm_num [invariant_random_17, state_random_17]
  · intro s
    dsimp [invariant_random_17, step_random_17]
    ring

def state_random_18 := ((0 : ℝ), (-4 : ℝ))
def step_random_18 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((2 : ℝ) + (1 : ℝ) * (s.2)))
def invariant_random_18 (s : ℝ × ℝ) : ℝ :=
  ((4 : ℝ) + (1 : ℝ) * (s.2) + (-2 : ℝ) * (s.1))
theorem preserved_random_18 (n : Nat) :
    invariant_random_18 (orbit step_random_18 state_random_18 n) = 0 := by
  apply orbit_invariant step_random_18 state_random_18 invariant_random_18
  · norm_num [invariant_random_18, state_random_18]
  · intro s
    dsimp [invariant_random_18, step_random_18]
    ring

def state_random_19 := ((0 : ℝ), (-4 : ℝ))
def step_random_19 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + ((-3 : ℝ) / 2) * (s.1) + ((5 : ℝ) / 2) * (s.1) ^ 2))
def invariant_random_19 (s : ℝ × ℝ) : ℝ :=
  ((4 : ℝ) + (1 : ℝ) * (s.2) + ((-13 : ℝ) / 6) * (s.1) + (2 : ℝ) * (s.1) ^ 2 + ((-5 : ℝ) / 6) * (s.1) ^ 3)
theorem preserved_random_19 (n : Nat) :
    invariant_random_19 (orbit step_random_19 state_random_19 n) = 0 := by
  apply orbit_invariant step_random_19 state_random_19 invariant_random_19
  · norm_num [invariant_random_19, state_random_19]
  · intro s
    dsimp [invariant_random_19, step_random_19]
    ring

def state_random_20 := ((0 : ℝ), (-1 : ℝ))
def step_random_20 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-3 : ℝ) / 2) + (1 : ℝ) * (s.2) + ((-5 : ℝ) / 2) * (s.1) + ((7 : ℝ) / 4) * (s.1) ^ 2))
def invariant_random_20 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) + (1 : ℝ) * (s.2) + ((-1 : ℝ) / 24) * (s.1) + ((17 : ℝ) / 8) * (s.1) ^ 2 + ((-7 : ℝ) / 12) * (s.1) ^ 3)
theorem preserved_random_20 (n : Nat) :
    invariant_random_20 (orbit step_random_20 state_random_20 n) = 0 := by
  apply orbit_invariant step_random_20 state_random_20 invariant_random_20
  · norm_num [invariant_random_20, state_random_20]
  · intro s
    dsimp [invariant_random_20, step_random_20]
    ring

def state_random_21 := ((0 : ℝ), (-4 : ℝ))
def step_random_21 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-3 : ℝ) / 2) + (1 : ℝ) * (s.2) + (-4 : ℝ) * (s.1) ^ 2 + ((1 : ℝ) / 5) * (s.1) ^ 3 + ((-1 : ℝ) / 2) * (s.1) ^ 4))
def invariant_random_21 (s : ℝ × ℝ) : ℝ :=
  ((4 : ℝ) + (1 : ℝ) * (s.2) + ((43 : ℝ) / 20) * (s.1) + ((-41 : ℝ) / 20) * (s.1) ^ 2 + ((8 : ℝ) / 5) * (s.1) ^ 3 + ((-3 : ℝ) / 10) * (s.1) ^ 4 + ((1 : ℝ) / 10) * (s.1) ^ 5)
theorem preserved_random_21 (n : Nat) :
    invariant_random_21 (orbit step_random_21 state_random_21 n) = 0 := by
  apply orbit_invariant step_random_21 state_random_21 invariant_random_21
  · norm_num [invariant_random_21, state_random_21]
  · intro s
    dsimp [invariant_random_21, step_random_21]
    ring

def state_random_22 := ((0 : ℝ), (5 : ℝ))
def step_random_22 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((2 : ℝ) / 3) + (1 : ℝ) * (s.2) + ((3 : ℝ) / 2) * (s.1) + (3 : ℝ) * (s.1) ^ 2 + (-2 : ℝ) * (s.1) ^ 3 + ((6 : ℝ) / 5) * (s.1) ^ 4 + ((-3 : ℝ) / 5) * (s.1) ^ 5 + (2 : ℝ) * (s.1) ^ 6))
def invariant_random_22 (s : ℝ × ℝ) : ℝ :=
  ((-5 : ℝ) + (1 : ℝ) * (s.2) + ((-297 : ℝ) / 700) * (s.1) + ((6 : ℝ) / 5) * (s.1) ^ 2 + ((-31 : ℝ) / 15) * (s.1) ^ 3 + ((27 : ℝ) / 20) * (s.1) ^ 4 + ((-77 : ℝ) / 50) * (s.1) ^ 5 + ((11 : ℝ) / 10) * (s.1) ^ 6 + ((-2 : ℝ) / 7) * (s.1) ^ 7)
theorem preserved_random_22 (n : Nat) :
    invariant_random_22 (orbit step_random_22 state_random_22 n) = 0 := by
  apply orbit_invariant step_random_22 state_random_22 invariant_random_22
  · norm_num [invariant_random_22, state_random_22]
  · intro s
    dsimp [invariant_random_22, step_random_22]
    ring

def state_random_23 := ((0 : ℝ), (3 : ℝ))
def step_random_23 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((7 : ℝ) + (1 : ℝ) * (s.2) + ((3 : ℝ) / 2) * (s.1) + ((1 : ℝ) / 3) * (s.1) ^ 2 + (-6 : ℝ) * (s.1) ^ 3 + (2 : ℝ) * (s.1) ^ 4 + (1 : ℝ) * (s.1) ^ 5))
def invariant_random_23 (s : ℝ × ℝ) : ℝ :=
  ((-3 : ℝ) + (1 : ℝ) * (s.2) + ((-1123 : ℝ) / 180) * (s.1) + (1 : ℝ) * (s.1) ^ 2 + ((-34 : ℝ) / 9) * (s.1) ^ 3 + ((25 : ℝ) / 12) * (s.1) ^ 4 + ((1 : ℝ) / 10) * (s.1) ^ 5 + ((-1 : ℝ) / 6) * (s.1) ^ 6)
theorem preserved_random_23 (n : Nat) :
    invariant_random_23 (orbit step_random_23 state_random_23 n) = 0 := by
  apply orbit_invariant step_random_23 state_random_23 invariant_random_23
  · norm_num [invariant_random_23, state_random_23]
  · intro s
    dsimp [invariant_random_23, step_random_23]
    ring

def state_random_24 := ((0 : ℝ), (-5 : ℝ))
def step_random_24 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((-5 : ℝ) + (1 : ℝ) * (s.2) + (2 : ℝ) * (s.1) + ((-7 : ℝ) / 3) * (s.1) ^ 2 + ((-3 : ℝ) / 2) * (s.1) ^ 3 + ((-2 : ℝ) / 5) * (s.1) ^ 4 + ((-3 : ℝ) / 2) * (s.1) ^ 5 + ((4 : ℝ) / 5) * (s.1) ^ 6))
def invariant_random_24 (s : ℝ × ℝ) : ℝ :=
  ((5 : ℝ) + (1 : ℝ) * (s.2) + ((20023 : ℝ) / 3150) * (s.1) + ((-23 : ℝ) / 12) * (s.1) ^ 2 + ((53 : ℝ) / 180) * (s.1) ^ 3 + ((4 : ℝ) / 5) * (s.1) ^ 4 + ((-107 : ℝ) / 100) * (s.1) ^ 5 + ((13 : ℝ) / 20) * (s.1) ^ 6 + ((-4 : ℝ) / 35) * (s.1) ^ 7)
theorem preserved_random_24 (n : Nat) :
    invariant_random_24 (orbit step_random_24 state_random_24 n) = 0 := by
  apply orbit_invariant step_random_24 state_random_24 invariant_random_24
  · norm_num [invariant_random_24, state_random_24]
  · intro s
    dsimp [invariant_random_24, step_random_24]
    ring

def state_random_25 := ((0 : ℝ), (4 : ℝ))
def step_random_25 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-7 : ℝ) / 3) + (1 : ℝ) * (s.2) + ((2 : ℝ) / 3) * (s.1) + ((2 : ℝ) / 3) * (s.1) ^ 2))
def invariant_random_25 (s : ℝ × ℝ) : ℝ :=
  ((-4 : ℝ) + (1 : ℝ) * (s.2) + ((23 : ℝ) / 9) * (s.1) + ((-2 : ℝ) / 9) * (s.1) ^ 3)
theorem preserved_random_25 (n : Nat) :
    invariant_random_25 (orbit step_random_25 state_random_25 n) = 0 := by
  apply orbit_invariant step_random_25 state_random_25 invariant_random_25
  · norm_num [invariant_random_25, state_random_25]
  · intro s
    dsimp [invariant_random_25, step_random_25]
    ring

def state_random_26 := ((0 : ℝ), (-4 : ℝ))
def step_random_26 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((7 : ℝ) / 4) + (1 : ℝ) * (s.2) + (2 : ℝ) * (s.1) + (-2 : ℝ) * (s.1) ^ 2))
def invariant_random_26 (s : ℝ × ℝ) : ℝ :=
  ((4 : ℝ) + (1 : ℝ) * (s.2) + ((-5 : ℝ) / 12) * (s.1) + (-2 : ℝ) * (s.1) ^ 2 + ((2 : ℝ) / 3) * (s.1) ^ 3)
theorem preserved_random_26 (n : Nat) :
    invariant_random_26 (orbit step_random_26 state_random_26 n) = 0 := by
  apply orbit_invariant step_random_26 state_random_26 invariant_random_26
  · norm_num [invariant_random_26, state_random_26]
  · intro s
    dsimp [invariant_random_26, step_random_26]
    ring

def state_random_27 := ((0 : ℝ), (2 : ℝ))
def step_random_27 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((7 : ℝ) / 5) + (1 : ℝ) * (s.2) + ((-3 : ℝ) / 5) * (s.1) + (3 : ℝ) * (s.1) ^ 2))
def invariant_random_27 (s : ℝ × ℝ) : ℝ :=
  ((-2 : ℝ) + (1 : ℝ) * (s.2) + ((-11 : ℝ) / 5) * (s.1) + ((9 : ℝ) / 5) * (s.1) ^ 2 + (-1 : ℝ) * (s.1) ^ 3)
theorem preserved_random_27 (n : Nat) :
    invariant_random_27 (orbit step_random_27 state_random_27 n) = 0 := by
  apply orbit_invariant step_random_27 state_random_27 invariant_random_27
  · norm_num [invariant_random_27, state_random_27]
  · intro s
    dsimp [invariant_random_27, step_random_27]
    ring

def state_random_28 := ((0 : ℝ), (-4 : ℝ))
def step_random_28 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((-1 : ℝ) + (1 : ℝ) * (s.2) + ((5 : ℝ) / 3) * (s.1) + ((-7 : ℝ) / 2) * (s.1) ^ 2 + ((4 : ℝ) / 3) * (s.1) ^ 3))
def invariant_random_28 (s : ℝ × ℝ) : ℝ :=
  ((4 : ℝ) + (1 : ℝ) * (s.2) + ((29 : ℝ) / 12) * (s.1) + ((-35 : ℝ) / 12) * (s.1) ^ 2 + ((11 : ℝ) / 6) * (s.1) ^ 3 + ((-1 : ℝ) / 3) * (s.1) ^ 4)
theorem preserved_random_28 (n : Nat) :
    invariant_random_28 (orbit step_random_28 state_random_28 n) = 0 := by
  apply orbit_invariant step_random_28 state_random_28 invariant_random_28
  · norm_num [invariant_random_28, state_random_28]
  · intro s
    dsimp [invariant_random_28, step_random_28]
    ring

def state_random_29 := ((0 : ℝ), (-4 : ℝ))
def step_random_29 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-1 : ℝ) / 3) + (1 : ℝ) * (s.2) + (1 : ℝ) * (s.1) + (-7 : ℝ) * (s.1) ^ 2 + ((-7 : ℝ) / 4) * (s.1) ^ 3 + ((7 : ℝ) / 4) * (s.1) ^ 5))
def invariant_random_29 (s : ℝ × ℝ) : ℝ :=
  ((4 : ℝ) + (1 : ℝ) * (s.2) + (2 : ℝ) * (s.1) + ((-41 : ℝ) / 12) * (s.1) ^ 2 + ((35 : ℝ) / 24) * (s.1) ^ 3 + ((-7 : ℝ) / 24) * (s.1) ^ 4 + ((7 : ℝ) / 8) * (s.1) ^ 5 + ((-7 : ℝ) / 24) * (s.1) ^ 6)
theorem preserved_random_29 (n : Nat) :
    invariant_random_29 (orbit step_random_29 state_random_29 n) = 0 := by
  apply orbit_invariant step_random_29 state_random_29 invariant_random_29
  · norm_num [invariant_random_29, state_random_29]
  · intro s
    dsimp [invariant_random_29, step_random_29]
    ring

def state_random_30 := ((0 : ℝ), (-4 : ℝ))
def step_random_30 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((-3 : ℝ) + (1 : ℝ) * (s.2) + ((-1 : ℝ) / 3) * (s.1) + ((-1 : ℝ) / 4) * (s.1) ^ 2))
def invariant_random_30 (s : ℝ × ℝ) : ℝ :=
  ((4 : ℝ) + (1 : ℝ) * (s.2) + ((23 : ℝ) / 8) * (s.1) + ((1 : ℝ) / 24) * (s.1) ^ 2 + ((1 : ℝ) / 12) * (s.1) ^ 3)
theorem preserved_random_30 (n : Nat) :
    invariant_random_30 (orbit step_random_30 state_random_30 n) = 0 := by
  apply orbit_invariant step_random_30 state_random_30 invariant_random_30
  · norm_num [invariant_random_30, state_random_30]
  · intro s
    dsimp [invariant_random_30, step_random_30]
    ring

def state_random_31 := ((0 : ℝ), (3 : ℝ))
def step_random_31 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-3 : ℝ) / 4) + (1 : ℝ) * (s.2) + ((-3 : ℝ) / 5) * (s.1) + ((7 : ℝ) / 3) * (s.1) ^ 2 + ((4 : ℝ) / 5) * (s.1) ^ 4 + ((4 : ℝ) / 3) * (s.1) ^ 5 + ((-5 : ℝ) / 4) * (s.1) ^ 6))
def invariant_random_31 (s : ℝ × ℝ) : ℝ :=
  ((-3 : ℝ) + (1 : ℝ) * (s.2) + ((1481 : ℝ) / 12600) * (s.1) + ((71 : ℝ) / 45) * (s.1) ^ 2 + ((-451 : ℝ) / 360) * (s.1) ^ 3 + ((-7 : ℝ) / 45) * (s.1) ^ 4 + ((679 : ℝ) / 600) * (s.1) ^ 5 + ((-61 : ℝ) / 72) * (s.1) ^ 6 + ((5 : ℝ) / 28) * (s.1) ^ 7)
theorem preserved_random_31 (n : Nat) :
    invariant_random_31 (orbit step_random_31 state_random_31 n) = 0 := by
  apply orbit_invariant step_random_31 state_random_31 invariant_random_31
  · norm_num [invariant_random_31, state_random_31]
  · intro s
    dsimp [invariant_random_31, step_random_31]
    ring

def state_random_32 := ((0 : ℝ), (3 : ℝ))
def step_random_32 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((4 : ℝ) / 3) + (1 : ℝ) * (s.2) + ((-7 : ℝ) / 5) * (s.1) + (1 : ℝ) * (s.1) ^ 2 + ((5 : ℝ) / 2) * (s.1) ^ 3 + (-1 : ℝ) * (s.1) ^ 6))
def invariant_random_32 (s : ℝ × ℝ) : ℝ :=
  ((-3 : ℝ) + (1 : ℝ) * (s.2) + ((-457 : ℝ) / 210) * (s.1) + ((23 : ℝ) / 40) * (s.1) ^ 2 + ((3 : ℝ) / 4) * (s.1) ^ 3 + ((-5 : ℝ) / 8) * (s.1) ^ 4 + ((1 : ℝ) / 2) * (s.1) ^ 5 + ((-1 : ℝ) / 2) * (s.1) ^ 6 + ((1 : ℝ) / 7) * (s.1) ^ 7)
theorem preserved_random_32 (n : Nat) :
    invariant_random_32 (orbit step_random_32 state_random_32 n) = 0 := by
  apply orbit_invariant step_random_32 state_random_32 invariant_random_32
  · norm_num [invariant_random_32, state_random_32]
  · intro s
    dsimp [invariant_random_32, step_random_32]
    ring

def state_random_33 := ((0 : ℝ), (2 : ℝ))
def step_random_33 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) * (s.2) + (-1 : ℝ) * (s.1) + ((-2 : ℝ) / 5) * (s.1) ^ 2 + ((-1 : ℝ) / 5) * (s.1) ^ 3 + (6 : ℝ) * (s.1) ^ 4 + ((-2 : ℝ) / 5) * (s.1) ^ 5))
def invariant_random_33 (s : ℝ × ℝ) : ℝ :=
  ((-2 : ℝ) + (1 : ℝ) * (s.2) + ((-7 : ℝ) / 30) * (s.1) + ((19 : ℝ) / 60) * (s.1) ^ 2 + ((-59 : ℝ) / 30) * (s.1) ^ 3 + ((193 : ℝ) / 60) * (s.1) ^ 4 + ((-7 : ℝ) / 5) * (s.1) ^ 5 + ((1 : ℝ) / 15) * (s.1) ^ 6)
theorem preserved_random_33 (n : Nat) :
    invariant_random_33 (orbit step_random_33 state_random_33 n) = 0 := by
  apply orbit_invariant step_random_33 state_random_33 invariant_random_33
  · norm_num [invariant_random_33, state_random_33]
  · intro s
    dsimp [invariant_random_33, step_random_33]
    ring

def state_random_34 := ((0 : ℝ), (-1 : ℝ))
def step_random_34 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + ((7 : ℝ) / 4) * (s.1) + ((7 : ℝ) / 4) * (s.1) ^ 2 + (-1 : ℝ) * (s.1) ^ 3 + ((7 : ℝ) / 2) * (s.1) ^ 4 + (1 : ℝ) * (s.1) ^ 5))
def invariant_random_34 (s : ℝ × ℝ) : ℝ :=
  ((1 : ℝ) + (1 : ℝ) * (s.2) + ((-3 : ℝ) / 10) * (s.1) + ((1 : ℝ) / 3) * (s.1) ^ 2 + ((-9 : ℝ) / 4) * (s.1) ^ 3 + ((19 : ℝ) / 12) * (s.1) ^ 4 + ((-1 : ℝ) / 5) * (s.1) ^ 5 + ((-1 : ℝ) / 6) * (s.1) ^ 6)
theorem preserved_random_34 (n : Nat) :
    invariant_random_34 (orbit step_random_34 state_random_34 n) = 0 := by
  apply orbit_invariant step_random_34 state_random_34 invariant_random_34
  · norm_num [invariant_random_34, state_random_34]
  · intro s
    dsimp [invariant_random_34, step_random_34]
    ring

def state_random_35 := ((0 : ℝ), (-5 : ℝ))
def step_random_35 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) * (s.2) + ((-5 : ℝ) / 3) * (s.1) + ((7 : ℝ) / 2) * (s.1) ^ 2))
def invariant_random_35 (s : ℝ × ℝ) : ℝ :=
  ((5 : ℝ) + (1 : ℝ) * (s.2) + ((-17 : ℝ) / 12) * (s.1) + ((31 : ℝ) / 12) * (s.1) ^ 2 + ((-7 : ℝ) / 6) * (s.1) ^ 3)
theorem preserved_random_35 (n : Nat) :
    invariant_random_35 (orbit step_random_35 state_random_35 n) = 0 := by
  apply orbit_invariant step_random_35 state_random_35 invariant_random_35
  · norm_num [invariant_random_35, state_random_35]
  · intro s
    dsimp [invariant_random_35, step_random_35]
    ring

def state_random_36 := ((0 : ℝ), (2 : ℝ))
def step_random_36 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-5 : ℝ) / 3) + (1 : ℝ) * (s.2) + ((-7 : ℝ) / 3) * (s.1)))
def invariant_random_36 (s : ℝ × ℝ) : ℝ :=
  ((-2 : ℝ) + (1 : ℝ) * (s.2) + ((1 : ℝ) / 2) * (s.1) + ((7 : ℝ) / 6) * (s.1) ^ 2)
theorem preserved_random_36 (n : Nat) :
    invariant_random_36 (orbit step_random_36 state_random_36 n) = 0 := by
  apply orbit_invariant step_random_36 state_random_36 invariant_random_36
  · norm_num [invariant_random_36, state_random_36]
  · intro s
    dsimp [invariant_random_36, step_random_36]
    ring

def state_random_37 := ((0 : ℝ), (-5 : ℝ))
def step_random_37 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((-2 : ℝ) / 5) + (1 : ℝ) * (s.2) + ((2 : ℝ) / 3) * (s.1) + ((7 : ℝ) / 2) * (s.1) ^ 2 + (4 : ℝ) * (s.1) ^ 3 + (-3 : ℝ) * (s.1) ^ 4 + ((2 : ℝ) / 3) * (s.1) ^ 5))
def invariant_random_37 (s : ℝ × ℝ) : ℝ :=
  ((5 : ℝ) + (1 : ℝ) * (s.2) + ((1 : ℝ) / 20) * (s.1) + ((17 : ℝ) / 36) * (s.1) ^ 2 + ((11 : ℝ) / 6) * (s.1) ^ 3 + ((-25 : ℝ) / 9) * (s.1) ^ 4 + ((14 : ℝ) / 15) * (s.1) ^ 5 + ((-1 : ℝ) / 9) * (s.1) ^ 6)
theorem preserved_random_37 (n : Nat) :
    invariant_random_37 (orbit step_random_37 state_random_37 n) = 0 := by
  apply orbit_invariant step_random_37 state_random_37 invariant_random_37
  · norm_num [invariant_random_37, state_random_37]
  · intro s
    dsimp [invariant_random_37, step_random_37]
    ring

def state_random_38 := ((0 : ℝ), (3 : ℝ))
def step_random_38 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), (((4 : ℝ) / 3) + (1 : ℝ) * (s.2) + (-2 : ℝ) * (s.1) + (-2 : ℝ) * (s.1) ^ 2 + ((1 : ℝ) / 4) * (s.1) ^ 3 + ((-3 : ℝ) / 5) * (s.1) ^ 4))
def invariant_random_38 (s : ℝ × ℝ) : ℝ :=
  ((-3 : ℝ) + (1 : ℝ) * (s.2) + ((-101 : ℝ) / 50) * (s.1) + ((-1 : ℝ) / 16) * (s.1) ^ 2 + ((119 : ℝ) / 120) * (s.1) ^ 3 + ((-29 : ℝ) / 80) * (s.1) ^ 4 + ((3 : ℝ) / 25) * (s.1) ^ 5)
theorem preserved_random_38 (n : Nat) :
    invariant_random_38 (orbit step_random_38 state_random_38 n) = 0 := by
  apply orbit_invariant step_random_38 state_random_38 invariant_random_38
  · norm_num [invariant_random_38, state_random_38]
  · intro s
    dsimp [invariant_random_38, step_random_38]
    ring

def state_random_39 := ((0 : ℝ), (5 : ℝ))
def step_random_39 (s : ℝ × ℝ) : ℝ × ℝ :=
  (((1 : ℝ) + (1 : ℝ) * (s.1)), ((1 : ℝ) + (1 : ℝ) * (s.2) + (1 : ℝ) * (s.1) + (1 : ℝ) * (s.1) ^ 2 + (1 : ℝ) * (s.1) ^ 3))
def invariant_random_39 (s : ℝ × ℝ) : ℝ :=
  ((-5 : ℝ) + (1 : ℝ) * (s.2) + ((-2 : ℝ) / 3) * (s.1) + ((-1 : ℝ) / 4) * (s.1) ^ 2 + ((1 : ℝ) / 6) * (s.1) ^ 3 + ((-1 : ℝ) / 4) * (s.1) ^ 4)
theorem preserved_random_39 (n : Nat) :
    invariant_random_39 (orbit step_random_39 state_random_39 n) = 0 := by
  apply orbit_invariant step_random_39 state_random_39 invariant_random_39
  · norm_num [invariant_random_39, state_random_39]
  · intro s
    dsimp [invariant_random_39, step_random_39]
    ring

end ForgeReplay
