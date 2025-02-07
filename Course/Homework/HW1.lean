import Course.Common

/-

Homework sheet 1
Due Feb 13 10am

All problems are mandatory unless stated otherwise.

I strongly recommend to also do all the problems in MIL Ch. 2.1, 2.2, 2.3
(clone the MIL repository from `https://github.com/leanprover-community/mathematics_in_lean`)
They come with solutions.

-/

namespace HW

/- # Rewriting practice -/

#check sub_zero

/- Solve this example using only the tactic `rw`. -/
example (a b c : ℝ) (h : a + b + c = 0) (h' : b - c = 0) (h'' : c = 0) : a = 0 := by
  sorry

/- Do it again, this time you are allowed to use `linarith`. -/
example (a b c : ℝ) (h : a + b + c = 0) (h' : b - c = 0) (h'' : c = 0) : a = 0 := by
  sorry

#check pow_one
#check pow_two
#check pow_succ
#check two_mul
#check sub_add
#check sub_sub
#check sub_mul
#check mul_sub

/- Here is an example using a `calc` block. Fill in the missing `sorry`s without using `ring` -/
example (a b : ℝ) : (a - b)^2 = a^2 - 2*a*b + b^2 := by
  calc
    _ = (a - b) * (a - b) := by rw [pow_succ, pow_one]
    _ = (a - b) * a - (a - b) * b := by sorry
    _ = a * a - b * a - (a - b) * b := by sorry
    _ = a * a - b * a - a * b + b * b := by sorry
    _ = a^2 - a * b - a * b + b^2 := by sorry -- rw [← pow_two, ← pow_two, mul_comm b a, ]
    _ = _ := by sorry -- rw [sub_sub, ← two_mul, mul_assoc]

#check pow_add
#check sub_self
#check sub_zero

/- Solve this example without using `ring` -/
example (a b : ℝ): a^4 - b^4 = (a^2 - b^2) * (a^2 + b^2) := by
  sorry

/- Solve this, but this time you can use any tactic. -/
example (a b : ℝ): a^8 - b^8 = (a^4 + b^4) * (a^2 + b^2) * (a + b) * (a - b) := by
  sorry

/- # Proving inequalities -/

/- Type `≤` using `\le`.
   There is also `≥`, but the convention in Lean is to always write inequalities using `≤`. -/

/- `≤` is characterized by the following familiar properties -/
#check le_refl
#check le_antisymm
#check le_trans

/- There is also strict inequality `<` -/
#check le_of_lt -- note the naming convention: conclusion comes first and then assumptions separated by `of`
                -- so this name tells us that the conclusion proves something involving `le`
                -- and the assumption involves `lt`
#check lt_of_le_of_ne -- this lemma has two assumptions, one involving `le` and one involving `ne`
#check lt_of_lt_of_le

/- Read MIL Ch. 2.3 for examples and more details. -/

/- `calc` can be used for chaining any transitive relations, not just `=`;
   and we can mix different transitive relations. -/
example (a b c d : ℝ) (h : a ≤ b) (h' : b < c) (h'' : c = d) : a < d := by
  calc
    a ≤ b := h
    _ < c := h'
    _ = d := h''

/-- Alternatively we can apply the transitivity lemmas manually. -/
example (a b c d : ℝ) (h : a ≤ b) (h' : b < c) (h'' : c = d) : a < d := by
  apply lt_of_le_of_lt h -- read more about `apply` in MIL Ch. 2.3
  apply lt_of_lt_of_eq h' h''

/-- Another way of writing it, using `exact` -/
example (a b c d : ℝ) (h : a ≤ b) (h' : b < c) (h'' : c = d) : a < d := by
  exact lt_of_le_of_lt h (lt_of_lt_of_eq h' h'')

/-- Yet another way using a proof term directly instead of tactics -/
example (a b c d : ℝ) (h : a ≤ b) (h' : b < c) (h'' : c = d) : a < d :=
  lt_of_le_of_lt h (lt_of_lt_of_eq h' h'')

/- `linarith` can deal with linear inequalities. Solve this example: -/
example (a b c d : ℝ) (h : a ≤ 4 * c + b) (h' : c < 2 * d) (h'' : b = 3 * d) : a < 11 * d := by
  sorry

#check add_le_add

/- Let us solve this using `calc`. Fill in the `sorry`s without using `linarith`. -/
example (a b c d : ℝ) (h : a ≤ 4 * c + b) (h' : c ≤ 2 * d) (h'' : b = 3 * d) : a ≤ 11 * d := by
  calc
    _ ≤ 4 * c + b := sorry
    _ = 4 * c + 3 * d := sorry
    _ ≤ 8 * d + 3 * d := by linarith -- Optional challenge: do this without `linarith`
                                     -- and using only tactics we learned so far
    _ = 11 * d := sorry

end HW
