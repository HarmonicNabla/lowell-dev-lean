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

ext         -- Use the principle of extensionality
rintro      -- A recursive version of `intro`, similar to `rcases`
dsimp       -- Definitional simplifier; simplifies only using certain facts that are true by `rfl`
change      -- Change the goal to a given definitionally equal expression
simp_all    -- Iteratively applies `simp * at *` until no more progress is made

induction   -- Apply an induction principle
induction'  -- Alternate syntax for the induction tactic
gcongr      -- Useful for inequalities; tries to match the same pattern on both sides recursively
field_simp  -- Can deal with division, tries to clear denominators; often useful before using `ring`
norm_cast   -- Tries to normalize casts (coercions) by pulling them out of expressions
push_cast   -- Tries push coercions into expressions.

infer_instance -- Synthesize a typeclass instance using typeclass inference

positivity    -- Tries to prove a goal of the form `0 < _` or `0 ≤ _`
filter_upwards -- Applies filter properties and hypotheses to make progress on proving filter membership goals.

refine        -- Like `exact` except one can use `?_` for missing terms resulting in corresponding subgoals
convert       -- Like `refine`, `exact`, except provided term doesn't have to match goal exactly; attempts to create subgoals by pattern matching
fun_prop      -- Automatically proves some function properties, e.g. continuity, differentiability
rotate_left, rotate_right -- Change current goal.
all_goals     -- Apply tactics to all goals.

-/
