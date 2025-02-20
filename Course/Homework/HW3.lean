import Course.Common
import Mathlib.Data.Nat.Prime.Basic

/-

Homework sheet 3
Due Feb 27 10am

All problems are mandatory unless stated otherwise.

Optional: Do all the problems in MIL Ch. 4.1, 4.2

-/

namespace HW

/- # Sets -/

open Set Function

variable {α : Type*} {s t : Set α}

/- In this exercise you are not allowed to use `simp`, `simp_all`, `tauto`, `aesop` -/
example : (t ∩ s) ∪ s = s := by
  sorry

/- In the following you can use any tactic -/
example : (t ∪ s)ᶜ = sᶜ ∩ tᶜ := by
  sorry

/- In the following you can use any tactic  -/
example (h : s ∩ t = ∅) : (s \ t) ∪ (t \ s) = s ∪ t := by
  sorry

/- In this exercise you are not allowed to use `simp`, `simp_all`, `tauto`, `aesop` -/
#check Nat.not_odd_iff_even

example : {n | Even n} ∩ {n : ℕ | Odd n} = ∅ := by
  sorry

/- In the following you can use any tactic
  Hint: Use `exact?` at the right time to find the lemma that prime numbers not equal to two are odd
-/
example : {n | Nat.Prime n} ⊆ {n | n = 2 ∨ Odd n} := by
  sorry

/- # Functions -/

variable {β : Type*} {f : α → β} {x : α} {u : Set β}

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example : s ⊆ f ⁻¹' u ↔ f '' s ⊆ u := by
  sorry

#check image_mono

example (f : α → α) (h : f '' s ⊆ s) : f '' (f '' s) ⊆ s := by
  sorry

open Real

#check abs_nonneg
#check abs_of_nonneg

example : range (fun x : ℝ ↦ |x|) = {y | 0 ≤ y} := by
  sorry

variable {f g : ℝ → ℝ}

#check f∘g    -- Type `∘` using `\o` (composition of functions)
#check Icc
#check range_comp_subset_range
#check range_sin
#check subset_antisymm_iff

example : range (sin ∘ cos) ⊆ Icc (-1) 1 :=
  sorry

end HW
