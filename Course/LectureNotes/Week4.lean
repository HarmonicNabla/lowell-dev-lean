import Course.Common

set_option linter.unusedTactic false

/-
Today: Induction, Finset, Coercions

Recommended reading: MIL Ch. 5, especially 5.2; TPL Ch. 8

-/

namespace Course.Week4

section

#check Nat

example {n : ℕ} : n ≤ 2^n := by
  induction n with    -- `induction` tactic applies induction to a given variable that has an inductive type (`Nat` is an inductive type)
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ 2^n + 1 := by gcongr -- `gcongr` is a very useful tactic for proving inequalities;
                               -- it tries to match both sides of the inequality to the same pattern
      _ ≤ 2^n + 2^n := by sorry
      _ = 2^(n+1) := by sorry

-- Variant: `induction'`

variable {α : Type*}

-- We can give recursive definitions
def iterate (f: α → α) (k : ℕ) (x : α) :=
  match k with
  | 0 => x
  | k + 1 => iterate f k (f x)  -- Lean knows how to determine that the recursion terminates

#eval iterate (fun n ↦ 2*n) 1 4

variable {f : α → α} {x : α} {n m k : ℕ}

/- We can prove some lemmas to work with `iterate` -/
lemma iterate_zero : iterate f 0 x = x := by rfl

lemma iterate_one : iterate f 1 x = f x := by rfl

lemma iterate_succ : iterate f (k + 1) x = iterate f k (f x) := by rfl

lemma iterate_add : iterate f (n + m) x = iterate f n (iterate f m x) := by
  -- Here there are two parameters we can induct over; one may be more convenient than the other
  induction m with -- `generalizing x` gives us a universal quantifier over `x` in the inductive hypothesis
  | zero => sorry
  | succ m ih =>
    sorry

/- `iterate` also exists in Mathlib -/
#check Nat.iterate
#check f^[k]

/- Our version of iterate is equivalent to the Mathlib version -/
example : Nat.iterate f k x = iterate f k x := by
  sorry

end

/- # Strong induction -/

section

def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 3 * a (n + 1) - 2 * a n

#check a.eq_def

/- Sometimes we need the inductive hypothesis
  not just for `n` but for all `m < n + 1` -/
#check Nat.strong_induction_on

lemma a_eq (n : ℕ) : a n = 2 ^ n := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => sorry
  | 1 => sorry
  | n + 2 => sorry

-- Alternative
#check Nat.strongRecOn

end

/- # Finite sums and products -/

section

#check Finset
#check Fintype

#check Finset.univ

variable {α β ι : Type*}

variable {s : Finset ι}

variable {f : ι → ℝ}

#check Finset.sum s f
#check ∑ x ∈ s, f x -- Type `\sum`
#check Finset.prod s f
#check ∏ x ∈ s, f x -- Type `\prod`

variable {n : ℕ}

#check Finset.range n
#check Fin n

open Finset

#check range_zero
#check sum_range_succ

example (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => sorry
  | succ n ih =>
    sorry

example (n : ℕ) : ∏ i ∈ range n, 2 ^ (2 * i + 1) = 2 ^ (n ^ 2) := by
  sorry

example (n : ℕ) : ∏ k ∈ range n, ((k + 1) : ℝ) / (k + 2) = 1 / (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih]
    field_simp -- can deal with division; tries to clear divisions, so that one can apply `ring`
    ring

end

/- # Casts and coercions -/

section

-- Lean distinguishes many types of numbers
#check ℕ
#check ℤ
#check ℚ
#check ℝ
#check ℂ

#check 5  -- the natural number `5`
#check (5 : ℝ) -- the real number `5`
#check (5 : ℝ → ℝ) -- the constant function `5`

#check 5 / 6 -- natural number division: result is the natural number `0`
#check (5 : ℚ) / 6 -- result is the rational number 5 / 6
#check (5 : ℝ) / 6

-- Careful with junk values for subtraction and division
#eval 3 - 5
#eval (3 : ℤ) - 5
#eval (2 : ℚ) / 0

variable {n : ℕ}

#check (n : ℚ)  -- `n` is coerced to a rational number: type `↑` with `\u`
#check (n : ℝ)

#check (n : ℝ) - 1

-- Each number type comes with its own arithmetic operations and these are not def. eq.
example (x y : ℚ): (((x + y) : ℚ) : ℝ) = (x : ℝ) + (y : ℝ) := by
  norm_cast -- `norm_cast` will pull coercions out of an expression
            -- `↑x + ↑y` becomes `↑(x + y)`

example (x y : ℚ): (((x * y) : ℚ) : ℝ) = (x : ℝ) * (y : ℝ) := by
  push_cast -- `push_cast` will push coercions into an expression
            -- `↑(x * y)` becomes `↑x * ↑y`
  rfl

-- Careful with coercing past subtraction / division in natural numbers
example (n m : ℕ) : (n : ℚ) - (m : ℚ) = (((n - m) : ℕ) : ℚ)  := by
  -- norm_cast -- doesn't work; the result is only true if `m ≤ n`!
  sorry

example (n m : ℕ) (h : (n : ℝ) = m + 1) : (n : ℚ) * (n : ℚ) = (m + 1) ^ 2 := by
  -- rw [h] -- doesn't work directly!
  sorry

end

end Course.Week4
