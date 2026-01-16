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
#check add_zero

/- *Was stuck so copied provided solution added comments to explain what is going on to best of my understanding.* -/
/- Solve this example using only the tactic `rw`. -/
example (a b c : ℝ) (h : a + b + c = 0) (h' : b - c = 0) (h'' : c = 0) : a = 0 := by
  rw [h'', sub_zero] at h'
  -- Rewrite h' using the substitution of the sub_zero tactic and the assumption from h''
  -- The order matters here, we are saying that rw [x, y] uses assumption x, and tactic y on h'.
  -- Now we have a + b + c = 0, b = 0, c = 0 as our state.
  rw [h', h'', add_zero] at h
  -- Expanded it out a bit for increased readability. Now we are saying that
  -- By applying the modified states of h' and h'' to h, and by twice using the add_zero lemma, we can see that a = 0
  rw [add_zero] at h
  -- At this point we have already extracted that a = 0, b = 0, c = 0 materially,
  -- now we need to convince lean that a = 0 resolves the goal that a = 0

  -- Originally this was rw[h] but not entirely following that, so replaced it with an exact.
  -- I am curious why the rw above on line 32 didn't resolve the goal already?
  exact h

/- Do it again, this time you are allowed to use `linarith`. -/
example (a b c : ℝ) (h : a + b + c = 0) (h' : b - c = 0) (h'' : c = 0) : a = 0 := by
  linarith

#check pow_one
#check pow_two
#check pow_succ
#check two_mul
#check sub_add
#check sub_sub
#check sub_mul
#check mul_sub


-- Did NOT check/copy solution for this one
/- Here is an example using a `calc` block. Fill in the missing `sorry`s without using `ring` -/
example (a b : ℝ) : (a - b)^2 = a^2 - 2*a*b + b^2 := by
  calc
    _ = (a - b) * (a - b) := by rw [pow_succ, pow_one]
    -- In this step, we take the LHS and rewrite it by reducing its power, and applying the ^1 rule.

    -- #eval

    _ = (a - b) * a - (a - b) * b := by rw[mul_sub]
    -- Now we claim something (in particular, the LHS) is of this form, and we prove that by this rw.

    _ = a * a - b * a - (a - b) * b := by rw[sub_mul, sub_mul]
    -- Similar to above we continue to multiply out using the multiplication RWs.
    -- In particular, we have two items of the form (a-b) * c

    _ = a * a - b * a - a * b + b * b := by rw[sub_mul, sub_add]
    -- We remove the last one of the form (a-b) * c, and then

    _ = a^2 - a * b - a * b + b^2 := by  rw [← pow_two, ← pow_two, mul_comm b a]
    -- <- pow_two ends up putting a*a into a^2. We need this again for b^2a. Finally, we want to show  - b * a - a * b = - a*b - a*b

    _ = _ := by rw [sub_sub, ← two_mul, mul_assoc]
    --Combines last term into one additon term, then backs out of that a multiple of two, then puts paranthesis on target goal to claim completeness.


#check pow_add
#check sub_self
#check sub_zero

/- Solve this example without using `ring` -/
example (a b : ℝ): a^4 - b^4 = (a^2 - b^2) * (a^2 + b^2) := by
   -- Had to copy solution again. My initial solution was halfway there
   -- but wasn't fully getting backing out with ← at the time,
   -- though I think I get it now.
   -- I did notice linarith worked on this, but seemed against the spirit.
   rw [mul_add]
   rw [sub_mul]
   rw [sub_mul]
   rw [add_sub]
   rw [← pow_add]
   rw [← pow_add]
   rw [mul_comm]
   rw [sub_add ]
   rw [sub_self]
   rw [sub_zero]

/- Solve this, but this time you can use any tactic. -/
example (a b : ℝ): a^8 - b^8 = (a^4 + b^4) * (a^2 + b^2) * (a + b) * (a - b) := by
  ring

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
  linarith

#check add_le_add

/- Let us solve this using `calc`. Fill in the `sorry`s without using `linarith`. -/
example (a b c d : ℝ) (h : a ≤ 4 * c + b) (h' : c ≤ 2 * d) (h'' : b = 3 * d) : a ≤ 11 * d := by
  calc
    _ ≤ 4 * c + b := h
    _ = 4 * c + 3 * d := by rw[h'']
    -- ^Had to check for solution on this specific line,
    -- I was missing the 'by'. Did not read rest of solution.
    -- So I was attempting with rw[h'']
    _ ≤ 8 * d + 3 * d := by linarith -- Optional challenge: do this without `linarith`
                                     -- and using only tactics we learned so far
    _ = 11 * d := by rw [← add_mul]; norm_num
    -- Used solution on this part as well, I attempted a few to see if they would generalize,
    -- but I didn't see an add_mul tactic to use in HW so far.
    -- Was trying to only use existing tools and not linarith.
    -- A little unclear on how this ; and norm_num works formally,
    -- But I am guessing it is doing the addition of 8 and 3 and then applying a rfl?

end HW
