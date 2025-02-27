import Course.Common

set_option linter.unusedTactic false

/-
Today: Induction

Recommended reading: MIL Ch. 5, especially 5.2; TPL Ch. 8

-/

namespace Course

#check Nat

example {n : ℕ} : n ≤ 2^n := by
  induction n with    -- `induction` tactic applies induction to a given variable that has an inductive type (`Nat` is an inductive type)
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ 2^n + 1 := by gcongr -- `gcongr` is a very useful tactic for proving inequalities;
                               -- it tries to match both sides of the inequality to the same pattern
      _ ≤ 2^n + 2^n := by sorry
      _ = 2^(n+1) := by sorry

-- Variant: `induction'`

variable {α : Type*}

def iterate (f: α → α) (k : ℕ) (x : α) :=
  match k with
  | 0 => x
  | k + 1 => iterate f k (f x)    -- recursive function definition

#eval iterate (fun n ↦ 2*n) 1 4

variable {f : α → α} {x : α} {n m k : ℕ}

lemma iterate_zero : iterate f 0 x = x := by rfl

lemma iterate_one : iterate f 1 x = f x := by rfl

lemma iterate_succ : iterate f (k + 1) x = iterate f k (f x) := by rfl

lemma iterate_add : iterate f (n + m) x = iterate f n (iterate f m x) := by
  -- Here there are two parameters we can induct over
  induction m with -- `generalizing x` gives us a universal quantifier over `x` in the inductive hypothesis
  | zero => sorry
  | succ m ih =>
    sorry

#check Nat.iterate
#check f^[k]

example : Nat.iterate f k x = iterate f k x := by
  sorry

-- To be continued

end Course
