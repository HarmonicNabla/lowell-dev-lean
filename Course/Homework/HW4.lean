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
  | zero => sorry
  | succ k ih => sorry

open Course.Week4

#check Nat.factorial
#check fac

#check Nat.factorial_succ

/- Let's show that the factorial defined in class is the same as Mathlib's factorial function -/
example : fac = Nat.factorial := by
  ext n -- Two functions are the same iff they take the same values for each input
  sorry

end

section

open Finset

example (n : ℕ) : ∑ i ∈ range n, i = ((n : ℝ) - 1) * n / 2 := by
  sorry

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) : ∑ i ∈ range (n + 1), a * r^i = (a * r ^ (n + 1) - a) / (r - 1) := by
  have h := sub_ne_zero.mpr h
  sorry

example {n : ℕ} {x : ℝ} (h : x ≠ 1) : ∏ i ∈ range n, (1 + x ^ (2 ^ i)) = (1 - x ^ (2 ^ n)) / (1 - x) := by
  sorry

end

-- Consider the following recursive definition
def a : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n

example : a 2 = 5 := by
  sorry

-- Solve this using strong induction
example (n : ℕ) : a n = 2 ^ n + (-1 : ℤ) ^ n := by
  sorry

section

example {p q : ℚ} : (p : ℝ) = 2 * q ↔ q = p / 2 := by
  sorry

example {n m : ℕ} (h : (n : ℚ) = m ^ 2 + 1) : (n : ℝ) - 1 = m ^ 2 := by
  sorry

end

end HW4
