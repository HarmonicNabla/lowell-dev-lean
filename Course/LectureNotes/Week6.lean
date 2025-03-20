import Course.Common

set_option linter.unusedTactic false

/-
Today: Limits and filters

Recommended reading: MIL Ch. 10.1

-/

namespace Course.Week6

section

/- # Limits -/

/- There are many different notions of limit -/

/- Let's define `lim_{n → ∞} a n = L` -/
/- E.g. `lim_{n → ∞} 1 / n = 0` -/
def seqHasLimitAtInf (a : ℕ → ℝ) (L : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

variable {f : ℝ → ℝ}

/- lim_{x → x₀} f(x) = L -/
def fctHasLimitAt (f : ℝ → ℝ) (x₀ : ℝ) (L : ℝ) : Prop := ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - L| < ε

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

Instead, Lean uses *filters* to unify all these slightly different definitions

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

#check Tendsto f (𝓝 x₀) (𝓝 L)   -- `lim_{x → x₀} f(x) = L`

#check Tendsto f atTop (𝓝 L) -- Limit at infinity: `lim_{x → ∞} f(x) = L`

#check Tendsto f (𝓝 x₀) atTop -- Limit tending to infinity: `lim_{x → x₀} f(x) = ∞`

#check Tendsto f (𝓝[≤] x₀) (𝓝 L) -- Left-sided limit: `lim_{x → x₀-} f(x) = L`

#check 𝓝[<] x₀
#check 𝓝[>] x₀
#check 𝓝[≠] x₀

/- lim_{n → ∞} a n = ∞ -/
example (a : ℕ → ℝ) : Tendsto a atTop atTop ↔ ∀ M, ∃ N, ∀ n ≥ N, a n ≥ M := by
  exact tendsto_atTop_atTop

/- lim_{n → ∞} a n = L -/
example (a : ℕ → ℝ) (L : ℝ) : Tendsto a atTop (𝓝 L) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε := by
  exact Metric.tendsto_atTop

-- Recall metric spaces
#check MetricSpace

#synth MetricSpace ℕ
#synth MetricSpace ℝ

#synth Dist ℝ
example (x y : ℝ) : dist x y = |x - y| := by rfl

#synth Dist ℕ
example (n m : ℕ) : dist n m = |(n : ℝ) - m| := by rfl

#check Metric.tendsto_atTop

#check Nat.floor

/- Let's prove that `lim_{n → ∞} 1 / (1 + n) = 0` -/
example : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (1 + n)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε -- Let `ε > 0`.
  -- Want: `1 / (1 + N) < ε` -> Want `N > 1 / ε - 1` <-> `N ≥ 1 / ε`
  let N := ⌊1 / ε⌋₊ -- Let `N = ⌊1 / ε⌋₊`
  use N -- Nat.floor type using `\lfloor`, `\rfloor`
  intro n hn -- Let `n ≥ N`
  calc
    _ = (1 : ℝ) / (1 + n) := by
      simp
      positivity -- `positivity` tries to use assumptions and lemmas to prove goals of the form `0 < _`, `0 ≤ _`
    _ ≤ 1 / (1 + N) := by gcongr
    _ < 1 / (1 / ε) := by gcongr; rw [add_comm]; exact Nat.lt_floor_add_one (1 / ε)
    _ = ε := by simp

-- #loogle Nat.cast (Nat.floor _)

variable {a : ℕ → ℝ}

-- Filters are also used to implement to notion of `Eventually`

#check Filter.Eventually

-- For `sufficiently large n` we have `a n ≥ 10`
example : (∀ᶠ n in atTop, a n ≥ 10) ↔ ∃ N, ∀ n ≥ N, a n ≥ 10 := by
  exact eventually_atTop

variable {b : ℕ → ℝ}

example (h1 : ∀ᶠ n in atTop, a n ≥ b n + 3) (h2 : ∀ᶠ n in atTop, b n ≥ 7) : ∀ᶠ n in atTop, a n ≥ 10 := by
  -- Attempting to follow the proof we might write on paper we would do something like this:
  apply eventually_atTop.mpr
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp h1 -- Let `N₁` be such that for `n ≥ N₁`: `a n ≥ b n + 3`
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp h2 -- Let `N₂` be such that for `n ≥ N₂`: `b n ≥ 7`
  use max N₁ N₂
  intro n hn -- Let `n ≥ max N₁ N₂`
  have h₁ := hN₁ n (le_of_max_le_left hn)
  have h₂ := hN₂ n (le_of_max_le_right hn)
  -- could use `calc` here, or:
  linarith only [h₁, h₂]

#check Eventually.of_forall -- From `Filter.univ`
#check Eventually.mono -- Compare with `Filter.sets_of_superset`
#check Eventually.and -- Compare with `Filter.inter_sets`

example (h1 : ∀ᶠ n in atTop, a n ≥ b n + 3) (h2 : ∀ᶠ n in atTop, b n ≥ 7) : ∀ᶠ n in atTop, a n ≥ 10 := by
  -- The argument above is much shorter if we work directly with properties of filters
  apply (h1.and h2).mono
  rintro n ⟨h₁, h₂⟩
  linarith only [h₁, h₂]

-- The `filter_upwards` tactic can apply filter properties for us
example (h1 : ∀ᶠ n in atTop, a n ≥ b n + 3) (h2 : ∀ᶠ n in atTop, b n ≥ 7) : ∀ᶠ n in atTop, a n ≥ 10 := by
  filter_upwards [h1, h2] with n h₁ h₂
  linarith only [h₁, h₂]


-- We can also formalize expressions such as `arbitrarily large` or `infinitely often` using filters
#check Filter.Frequently -- Written using `∃ᶠ`

-- "There exist arbitrarily large `n` such that `a n ≥ 10`" or "There are infinitely many `n` such that `a n ≥ 10`"
example : (∃ᶠ n in atTop, a n ≥ 10) ↔ ∀ N, ∃ n ≥ N, a n ≥ 10 := by
  exact frequently_atTop

end

end Course.Week6
