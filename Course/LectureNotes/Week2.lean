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

We need to learn how to deal with each of these
when they appear in the goal or in a hypothesis
(introduction and elimination rules).

-/

/- # Implications, universal quantifiers -/

/- We already learned that implications in Lean
  are modeled as function types -/

/- To make progress if the target is a function type, we
use the tactic `intro` -/

example (n m : ℕ) : n = m → m = n := by
  intro h
  -- simp [h]
  symm
  exact h

/- Universal quantifiers are modeled in Lean using
  *dependent function types*: in a dependent function type
  the *type* of the ouput depends on the *value* of the input -/

#check ∀ (n : ℕ), 2 + n^2 = n * n + 2

example : ∀ (n : ℕ), 2 + n^2 = n * n + 2 := by
  intro n
  ring

example (h : ∀ n, n = n + 1) : 0 = 1 := by
  exact h 0

/- # Existential quantifiers -/

#check ∃ n, n + 5 = 7
#check Exists -- `Exists` is defined using an inductive type

example : ∀ m : ℤ, ∃ n, n - m = 3 := by
  intro m
  use m + 3   -- `use` introduces an existential quantifiers
  ring

/- Junk values: Careful with subtraction in `ℕ` -/
#eval 3-5
#eval (3:ℤ)-5

-- In Lean arithmetic operations are defined
-- for all inputs using `junk values`
-- when the operation is undefined
#eval 1/0

example : ∃ n, n = 0 := by? -- `by?` shows us the full proof term
  use 0

example : ∃ n, n = 0 := Exists.intro 0 (Eq.refl 0)

#check Exists.intro
#check Exists.choose
#check Exists.choose_spec

#print Even
#print Odd

example (n : ℕ) : Even n → Odd (n + 1) := by
  intro h
  unfold Even at h   -- `unfold` is used to unfold definitions - it can often be commented out since Lean does certain unfolding automatically
  -- unfold Odd
  cases h with -- `cases` eliminates an inductive type in a hypothesis and splits into subgoals for each constructor
  | intro k hk =>
    use k
    rw [hk]
    ring
  -- Alternative syntax:
  -- cases h
  -- case intro k hk =>
  --   use k
  --   rw [hk]
  --   ring


/- As usual there are many ways to do the same thing in Lean -/
example (n : ℕ) : Even n → Odd (n + 1) := by
  intro h
  unfold Even at h
  -- Type  `⟨` using `\<` and `⟩` using `\>`
  obtain ⟨r, hr⟩ := h -- succinct alternative to `cases`
  -- This is the same as using
  -- rcases h with ⟨k, hk⟩      -- `rcases` is like `cases` except it is more powerful (it can apply `cases` recursively)
  -- Here `⟨k, hk⟩` is a pattern extracting the two arguments of the `Exists.intro` constructor
  unfold Odd
  use r
  -- rw [hr]
  -- ring
  simp [hr, two_mul] -- `simp` tries to simplify the goal (and sometimes manages to finish) using the provided lemmas and "simp" lemmas

/- # Conjunction -/

#check And -- `And` is realized as a `structure` in Lean; this is like an inductive type with a single constructor

#check And.intro
#check And.left
#check And.right

example (n : ℕ) : Even (2*n) ∧ Even (2*n + 2) := by
  apply And.intro
  · unfold Even       -- Focus on top-most subgoal, type using `\.`
    use n
    rw [two_mul]
  · unfold Even
    use n + 1
    ring

example (n m : ℕ) (h : Even n ∧ Odd m) : Odd (n + m) := by
  -- have h₁ := h.1 -- or `h.left` -- `have` is used to introduce new hypotheses
  -- obtain ⟨k, hk⟩ := h₁  -- Can also skip the `have` and write `h.1` directly here
  -- have h₂ := h.2
  -- obtain ⟨l, hl⟩ := h₂
  -- We can also do it all that at once with one line of `obtain`
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := h
  use l + k
  --linarith
  rw [hk, hl]
  ring


/- # Disjunction -/

#check Or -- `Or` is an inductive type with two constructors
#check Or.inl -- `inl` can be thought of as short for `intro_left`
#check Or.inr

example (n m : ℕ) (h : Even n ∨ Even m) : Odd (n*m + 1) := by
  obtain h|h := h
  · obtain ⟨k, hk⟩ := h
    -- Want r such that: 2*k*m+1 = 2*r + 1
    use k * m
    rw [hk]
    ring
  · sorry -- Same argument

example (n : ℕ) : Even n ∨ Odd n := by
  by_cases h : Even n -- `by_cases` creates a case distinction
  · left -- Applies `Or.inl`
    assumption
  · right -- Applies `Or.inr`
    -- use `exact?` to search library for a lemma that will close the goal
    exact Nat.not_even_iff_odd.mp h
    -- there is also `apply?` to search for a lemma that will make progress (sometimes works, sometimes not)

/- # Negation -/

#check Not -- `Not` is defined as a function type mapping to `False`

variable {α : Type} (P : α → Prop) -- `P` is a predicate

example (h : ∀ x, P x) : ¬ ∃ x, ¬ P x := by
  intro h'
  obtain ⟨x, hx⟩ := h'
  have hx' := h x
  contradiction -- tries to find a contradiction to close the goal (not very clever, but works here)
  -- exact hx hx' -- This works because `hx` is a function that maps a proof of `P x` into `False` and `hx'` is a proof of `P x`

/- Let's do it a different way -/
example (h : ∀ x, P x) : ¬ ∃ x, ¬ P x := by
  push_neg -- pushes negation into conclusions
  assumption -- closes goal if goal found among local hypotheses

example (h : ∀ x, P x) : ¬ ∃ x, ¬ P x := by
  tauto -- automates proofs of tautologies

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x := by
  push_neg at h
  assumption

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x := by
  -- `tauto` fails here
  aesop -- `Automated Extensible Search for Obvious Proofs`
        -- tries to prove the goal automatically using various methods (it's good at proving tautologies)
