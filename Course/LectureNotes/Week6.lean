import Course.Common
import Mathlib

set_option linter.unusedTactic false

/-
Today: Limits and filters

Recommended reading: MIL Ch. 10.1

-/

namespace Course.Week6

section

/- # Limits -/

/- There are many different notions of limit -/

def seqHasLimitAtInf (a : ℕ → ℝ) (L : ℝ) : Prop := sorry

/- Consider a function -/
variable {f : ℝ → ℝ}

def fctHasLimitAt (f : ℝ → ℝ) (x0 : ℝ) (L : ℝ) : Prop := sorry

/-

There are many other slightly different definitions of limits we may want to talk about:

- Limit as `x → ± ∞`
- Limit as `x → x₀`
- One-sided limits at a point (only approaching from the left or right) "as `x → x₀-`"
- Limits tending to `± ∞` instead of a real number
- Limits with the side condition `x ≠ x₀`
- Limits in more general settings than sequences or functions on the real numbers

All these variations would require lots of different definitions each with their own set of slightly different lemmas
as well as lemmas to translate between notions appropriately.

Obviously we don't want to do it that way.

Instead, Lean uses *filters*

 -/

variable {α β : Type*}

/- A Filter is a collection of sets on a type α with the following properties:
  - `Set.univ` belongs to the filter
  - If a set belongs to the filter, all subsets belong to the filter.
  - If two sets belong to the filter, then their intersection belongs to the filter.
-/
#check Filter α

/- You should think of this as an abstraction and generalization of the notion of `all neighborhoods of a point`. -/

#check Filter ℝ
#check Filter ℕ

open Filter Set Function Topology

variable {x₀ L : ℝ}
#check 𝓝 x₀ -- `neighborhood filter` at `x₀` consisting of all open sets containing `x₀`
             -- type using `\nb`

#check (atTop : Filter ℝ) -- filter "at `∞`" consisting of all sets of the form `{ x | x ≥ y }` for some `y`
#check (atBot : Filter ℝ) -- filter "at `-∞`"

variable {F F' : Filter α}

-- Filters are ordered by (reverse) inclusion
#check F ≤ F'

-- Filters can be pushed from one type onto another along a given map via forming preimages
example (T : α → β) : Filter α → Filter β := fun F : Filter α ↦ Filter.map T F

-- This allows us to define limits
#check Tendsto

#check Tendsto f (𝓝 x₀) (𝓝 L)   -- `lim_{x → x₀} f = L`

#check Tendsto f atTop (𝓝 L) -- Limit at infinity: `lim_{x → ∞} f = L`

#check Tendsto f (𝓝 x₀) atTop -- Limit tending to infinity: `lim_{x → x₀} f = ∞`

#check Tendsto f (𝓝[≤] x₀) (𝓝 L) -- Left-sided limit: `lim_{x → x₀-} f = L`

#check 𝓝[<] x₀
#check 𝓝[>] x₀
#check 𝓝[≠] x₀

example (a : ℕ → ℝ) : Tendsto a atTop atTop ↔ ∀ M, ∃ N, ∀ n ≥ N, a n ≥ M := by
  sorry

example (a : ℕ → ℝ) (L : ℝ) : Tendsto a atTop (𝓝 L) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε := by
  sorry

-- Recall metric spaces
#check MetricSpace

#synth MetricSpace ℕ
#synth MetricSpace ℝ

#synth Dist ℝ
example (x y : ℝ) : dist x y = |x - y| := by rfl

#synth Dist ℕ

#check Metric.tendsto_atTop

example : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (1 + n)) atTop (𝓝 0) := by
  sorry

variable {a : ℕ → ℝ}

-- Filters are also used to implement to notion of `Eventually`

#check Filter.Eventually

example : (∀ᶠ n in atTop, a n ≥ 10) ↔ ∃ N, ∀ n ≥ N, a n ≥ 10 := by
  sorry

variable {b : ℕ → ℝ}

example (h1 : ∀ᶠ n in atTop, a n ≥ b n + 3) (h2 : ∀ᶠ n in atTop, b n ≥ 7) : ∀ᶠ n in atTop, a n ≥ 10 := by
  -- Attempting to follow the proof we might write on paper we would do something like this:
  apply eventually_atTop.mpr
  sorry

#check Eventually.of_forall -- From `Filter.univ`
#check Eventually.mono -- Compare with `Filter.sets_of_superset`
#check Eventually.and -- Compare with `Filter.inter_sets`

example (h1 : ∀ᶠ n in atTop, a n ≥ b n + 3) (h2 : ∀ᶠ n in atTop, b n ≥ 7) : ∀ᶠ n in atTop, a n ≥ 10 := by
  -- Instead we should try to work directly with properties of filters
  sorry

-- `filter_upwards` tactic
example (h1 : ∀ᶠ n in atTop, a n ≥ b n + 3) (h2 : ∀ᶠ n in atTop, b n ≥ 7) : ∀ᶠ n in atTop, a n ≥ 10 := by
  sorry

-- We can also formalize expressions such as `arbitrarily large` or `infinitely often` using filters
#check Filter.Frequently -- Written using `∃ᶠ`

-- "There exist arbitrarily large `n` such that `a n ≥ 10`" or "There are infinitely many `n` such that `a n ≥ 10`"
example : (∃ᶠ n in atTop, a n ≥ 10) ↔ ∀ N, ∃ n ≥ N, a n ≥ 10 := by
  sorry

end

end Course.Week6
