import Course.Common

/-

Quick overview of tactics we learned so far.

-/

/-
rfl         -- Prove a goal of type `a=a`
exact       -- Prove a goal that exactly matches given type
assumption  -- Closes goal if it is found among local hypotheses
trivial     -- Proves a small number of `trivial` goals
rw, rewrite, nth_rewrite    -- Rewrite goal/hypothesis using provided hypotheses (left to right!)
calc        -- Initiate a structured calculation
ring        -- Attempt to prove goal using properties of a ring
linarith    -- Proves linear equations/inequalities using linear equations/inequalities in hypotheses
norm_num    -- Numerical `normalization` -- can perform some numerical simplification
simp        -- Simplify goal using `simp`-lemmas and provided additional lemmas
apply       -- Apply a hypothesis/lemma

intro       -- Introduce hypothis/function parameter; use when the goal is an implication or a universal quantifier
symm        -- Apply symmetry when goal type is a symmetric relation
use         -- Introduce an existential quantifier - when your goal is an existential quantifier
cases       -- Split into subgoals according to an inductive type definition
rcases      -- Apply `cases` recursively
obtain      -- Similar to `rcases` -- you can use this to eliminate hypotheses involving existential quantifiers, conjunctions, disjunctions
constructor -- Use when goal is an inductive type.
have        -- Introduce a new local hypothesis
left        -- Change goal to the left part of a disjunction (apply `Or.inl`)
right       -- Change goal to the right part of a disjunction (apply `Or.inl`)
by_cases    -- Create two subgoals with additional assumption that a given proposition is true or false
unfold      -- Unfold a definition
push_neg    -- Push logical negation into conclusion
contradiction -- Tries to close goal by deriving a contradiction from hypotheses
tauto       -- Tries to prove logical tautologies
aesop       -- Tries to prove goal automatically using various methods (good for tautologies)


-/
