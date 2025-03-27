import Course.Common

-- Week 4
/-
Induction
  - induction tactic
  - 'generalizing'
  - alternate induction principles (strong induction)

Working with Finset, sums and products

-/

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
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring
