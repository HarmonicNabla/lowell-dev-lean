import Course.Common

/- Week 2: Feb 13 -/

/-
Today: Logic

Recommended reading: MIL Ch. 3

-/

/- There are various logical quantifiers and connectives
that we need to be able to handle:
  - Implications `→` (type `\to`)
  - Universal quantifiers `∀` (type `\forall`)
  - Existential quantifiers `∃` (type `\ex`)
  - Conjunctions `∧` (type `\and`)
  - Disjunctions `∨` (type `\or`)
  - Negations `¬` (type `\not`)

We need to learn how to deal when each of these
appears in the goal or in a hypothesis
(introduction and elimination rules).

-/

/- We already learned that implications in Lean
  are modeled as function types -/

/- To make progress if the target is a function type, we
use the tactic `intro` -/

example (n m : ℕ) : n = m → m = n := by
  sorry

/- Universal quantifiers are modeled in Lean using
  *dependent function types*: in a dependent function type
  the *type* of the ouput depends on the *value* of the input -/

#check ∀ (n : ℕ), 2 + n^2 = n * n + 2

example : ∀ (n : ℕ), 2 + n^2 = n * n + 2 := by
  intro n
  ring

/- Existential quantifiers -/

#check ∃ n, n + 5 = 7
#check Exists -- `Exists` is defined using an inductive type

example : ∀ m : ℤ, ∃ n, n - m = 3 := by
  intro m
  use m + 3
  ring

/- Junk values: Careful with subtraction in `ℕ` -/
#eval 3-5
#eval (3:ℤ)-5

-- In Lean every arithmetic operations are defined
-- for all inputs using `junk values`
-- when the operation is undefined
#eval 1/0


-- To be continued
