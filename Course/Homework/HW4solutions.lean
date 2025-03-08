import Course.Common
import Course.LectureNotes.Week4
import Mathlib.Data.Nat.Prime.Basic

/-

Homework sheet 4
Due March 6 10am

All problems are mandatory unless stated otherwise.

Optional: Do all the problems in MIL Ch. 5.2

-/

namespace HW4

-- Fill in all `sorry`s
-- Unless otherwise stated, you may use any tactics
section

open Function

variable {α : Type*} {f : α → α} {x : α}

#check iterate_succ
#check comp_apply

-- Solve this example using only `rw` and `rfl` (`simp` not allowed!)
example (h : f x = x) (k : ℕ) : f^[k] x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ, comp_apply, h, ih]

open Course.Week4

#check Nat.factorial
#check fac

#check Nat.factorial_succ

/- Let's show that the factorial defined in class is the same as Mathlib's factorial function -/
example : fac = Nat.factorial := by
  ext n -- Two functions are the same iff they take the same values for each input
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fac_succ, Nat.factorial_succ, ih]

end

section

open Finset

example (n : ℕ) : ∑ i ∈ range n, i = ((n : ℝ) - 1) * n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    push_cast at ih
    rw [sum_range_succ, ih]
    field_simp
    ring

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) : ∑ i ∈ range (n + 1), a * r^i = (a * r ^ (n + 1) - a) / (r - 1) := by
  have h := sub_ne_zero.mpr h
  induction n with
  | zero =>
    rw [range_one, sum_singleton, pow_zero, mul_one, zero_add, pow_one]
    field_simp
    ring
  | succ n ih =>
    rw [sum_range_succ, ih]
    field_simp
    ring

example {n : ℕ} {x : ℝ} (h : x ≠ 1) : ∏ i ∈ range n, (1 + x ^ (2 ^ i)) = (1 - x ^ (2 ^ n)) / (1 - x) := by
  have h := sub_ne_zero.mpr h.symm
  induction n with
  | zero => simp [h]
  | succ n ih =>
    rw [prod_range_succ, ih]
    field_simp
    ring

end

-- Consider the following recursive definition
def a : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n

example : a 2 = 5 := by
  rfl

-- Solve this using strong induction
example (n : ℕ) : a n = 2 ^ n + (-1 : ℤ) ^ n := by
  induction n using Nat.strongRecOn with
  | ind n ih => match n with
    | 0 => rfl
    | 1 => rfl
    | n+2 =>
      rw [a.eq_def]
      dsimp
      push_cast
      rw [ih (n + 1) (by simp), ih n (by simp)]
      ring

section

example {p q : ℚ} : (p : ℝ) = 2 * q ↔ q = p / 2 := by
  constructor
  · intro h
    norm_cast at h
    rw [h]
    ring
  · intro h
    rw [h]
    norm_cast
    ring

example {n m : ℕ} (h : (n : ℚ) = m ^ 2 + 1) : (n : ℝ) - 1 = m ^ 2 := by
  norm_cast at h
  rw [h]
  push_cast
  ring

end

end HW4
