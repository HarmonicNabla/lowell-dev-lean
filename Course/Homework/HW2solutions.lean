import Course.Common
import Mathlib.Data.Nat.Prime.Basic

/-

Homework sheet 2
Due Feb 20 10am

All problems are mandatory unless stated otherwise.

Optional: Do all the problems in MIL Ch. 3.1-3.5

-/

namespace HW

/- Eliminate all `sorry`s -/
example : ∀ n : ℕ, (∃ m, m > n) ∨ 0 = 1 := by
  intro n
  left
  use n + 1
  simp

/- Divisibility:
  `a ∣ b` means `∃ k, b = k * a`
  Type `∣` using `\|`
 -/
example (a b c : ℕ) (h : a ∣ b) (h' : a ∣ c) : a^2 ∣ b * c := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := h' -- remove from here
  use k * l
  rw [hk, hl]
  ring

example (n : ℕ) : 1 ∣ n ∧ n ∣ n := by
  constructor -- makes progress when goal is an inductive type (such as `And`)
  · -- Solve this using one `exact` (hint: guess or search for the right lemma using `exact?`)
    exact Nat.one_dvd n
  · -- Solve this using one `exact`
    exact Nat.dvd_refl n

/- If and only if -/
#check Iff

-- Type `↔` using `\iff`
example (n : ℕ) : 2 ∣ n ↔ Even n := by
  constructor <;>
  { intro h
    obtain ⟨k, hk⟩ := h
    use k
    rw [hk, two_mul]
  }

#check Iff.mp
#check Iff.mpr
#check Nat.dvd_refl
#check Nat.le_of_dvd

example (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (h : ∀ d, d ∣ n ↔ d ∣ m) : n = m := by
  apply le_antisymm
  · exact Nat.le_of_dvd hm <| (h n).mp <| Nat.dvd_refl n -- imagine `<|` like an opening bracket `(` with the matching closing bracket places as far right as possible
  · exact Nat.le_of_dvd hn <| (h m).mpr <| Nat.dvd_refl m

/- Check the mathlib definition of a prime number -/
#check Nat.Prime

/- Hint: `norm_num` can prove primality of small primes  -/
example : ∃ p, Nat.Prime p ∧ p > 10 ∧ p < 20 := by
  use 11
  constructor
  · norm_num
  · simp

#check Nat.prime_def

example (p d : ℕ) (h : Nat.Prime p) : d ∣ p → (d = 1 ∨ d = p) := by
  exact (Nat.prime_def.mp h).2 d

#check sq_eq_one_iff
#check neg_inj

example (x y : ℝ) : (x + y)^2 = 1 → 1 = x + y ∨ 1 = -x - y := by
  intro h
  obtain h'|h' := sq_eq_one_iff.mp h
  · left
    exact h'.symm
  · right
    apply neg_inj.mp
    rw [← h']
    ring

#check le_antisymm
#check sq_nonneg

example : ∀ x : ℝ, (∃ y, y^2 = x ∧ x = -y^2) → x = 0 := by
  -- intro x
  -- intro h
  -- obtain ⟨y, hy, hy'⟩ := h
  -- or using `rintro`
  rintro x ⟨y, hy, hy'⟩
  apply le_antisymm
  · rw [hy']
    apply Left.neg_nonpos_iff.mpr
    exact sq_nonneg _
  · rw [← hy]
    exact sq_nonneg _

/- Let's prove the *drinker's principle* - a well-known logical tautology that seems counterintive/paradoxical:
   Assume we're in a non-empty bar where every person is either drinking or not drinking. Then the following is true:
   "There exists a person such that if that person drinks, then everybody drinks."
 -/
variable {β : Type*} [Nonempty β]

lemma drinkers_principle (drinks : β → Prop) : ∃ a, drinks a → ∀ b, drinks b := by
  -- Either everybody drinks, or not.
  by_cases h : ∀ b, drinks b
  · -- Assume everybody drinks.
    -- Let `b` be anyone (an element of `β` exists because `β` is nonempty)
    obtain b : β := Classical.choice inferInstance
    use b
    -- Assume that `b` drinks.
    intro hb
    -- Everybody drinks by assumption.
    assumption
  · -- Assume not everybody drinks.
    -- Then there exists someone that doesn't drink
    push_neg at h
    -- Let `b` be someone that doesn't drink.
    obtain ⟨b, hb⟩ := h
    use b
    -- Since `b` doesn't drink, the desired implication is true by the `principle of explosion` (also known as `ex falso quodlibet`).
    -- Hint: Use the `contradiction` tactic.
    intro hb'
    contradiction

end HW
