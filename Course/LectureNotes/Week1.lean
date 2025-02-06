import Course.Common

/- Week 1: Feb 6 -/

/-
Today:
* installing Lean, working with git
* interacting with Lean
* some basic tactics

Recommended reading: MIL Ch. 1 and 2

-/

/- # Introduction -/

/- In Lean every expression has a *type*.
   We can display the type of an expression using `#check`.
 -/

#check 2+5
#check (2:ℝ)+5
#check ℕ
#check Type
#check Type 1

variable (n : ℕ)

#check ℤ
#check ℝ
#check ℂ
#check String

#check "Hello World"

/- To print the definition of a type we can use `#print` -/

#print Nat

/- `#eval` -/

#eval 2^4

/- In mathematics we essentially do just two different things: introduce definitions and prove theorems about them -/

/- Definitions can be made using `def` -- identifiers must be unique within a `namespace` -/
/- Type ∃ using `\ex` -/

namespace Lowell

def Even (n : ℕ) : Prop := ∃ k, n = 2 * k

def Modulo (n r m : ℕ) : Prop := ∃ k, n = m * k + r

#check Even

end Lowell

#check Even
#check Lowell.Even

section MySection

open Lowell

#check Even
#check Modulo

end MySection

/- Definitions can use recursion -/

def MyFactorial (n : ℕ) : ℕ :=
  if n = 0 then 1
  else n * MyFactorial (n-1)

#eval MyFactorial 4

/- One can also use a `match` expression (somewhat preferable here) -/

def Factorial (n : ℕ) : ℕ :=
  match n with
  | Nat.zero => 1
  | Nat.succ n => (n + 1) * Factorial n

#eval Factorial 4

/- Theorems can be introduced using `theorem` -/

theorem myTheorem (n : ℕ) : n = n := by rfl

example (n : ℕ): n = n := by rfl

/- Type ∀ using `\forall` -/

#check ∀ n : ℕ, n = n

/- Theorem statements are types. Proving a theorem means providing an instance of that type (a `proof term`) -/

variable (A B : Prop)
/-Type subscripts using e.g. `\_1` -/

/- Implications are modeled as function types -/

#check A → B

theorem modus_ponens (h₁ : A) (h₂ : A → B) : B := h₂ h₁

/- Curry-Howard isomorphism -/

/- Tactics -/

#check mul_zero

/- In Lean function application is denoted without brackets:
To apply function `f` to parameter `a`, write `f a` (not `f(a)` as in many other programming languages)
 -/

#check mul_zero n

example (n : ℕ) : n * 0 = 0 := by
  exact mul_zero n

example (n : ℕ) : n * 0 = 0 := by
  exact mul_zero _ -- `_` asks Lean to fill in the parameter using type inference

#check zero_mul

/- # Proving identities -/

/- Rewriting -/

#check mul_assoc
#check add_assoc
#check mul_comm

example (a b c : ℝ) : a * b * c = a * c * b := by
  rw [mul_assoc]
  rw [mul_assoc]
  rw [mul_comm b]

  -- -- We can introduce new hypotheses:
  -- have hbc: b * c = c * b := by rw [mul_comm]
  -- rw [mul_assoc]
  -- rw [hbc]
  -- rw [mul_assoc]

/- Calculation -/

#check add_zero
#check mul_one

example (a b : ℝ) : a^2 * 1 * b + 0 = b * a^2 := by
  calc
    _ = a^2 * 1 * b := by exact add_zero _
    _ = a^2 * b := by rw [mul_one] -- `rw` is short for `rewrite` and `rfl`
    _ = b * a^2 := by exact mul_comm _ _


/- Ring -/

#print Ring

example (a b : ℝ) : a^2 * 1 * b + 0 = b * a^2 := by ring

example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by ring

example (a b : ℝ) : (a+b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3 := by ring

/- Linarith -/

example (a b c d : ℝ) (h : a + b = c) (h' : 2 * b + d = a) (h'': d + a = a + c) : b = 0 := by linarith

-- In longer proofs we can create our own auxiliary lemmas
--@[local simp] -- we can register our own `simp` lemmas
lemma two_plus_one_eq_three : (2:ℝ) + 1 = 3 := by norm_num -- closes goals involving numerical computation

--ring

-- Let's try this without `linarith`
example (a b c : ℝ) (h : a + b = c) (h' : 2 * b + c = a) : b = 0 := by
  rw [← h'] at h -- use `at h` to rewrite hypothesis `h` instead of the main goal
                 -- use `←` to use a lemma backwards
  rw [add_comm] at h
  rw [← add_assoc] at h
  nth_rewrite 1 [← one_mul b] at h -- `nth_rewrite` tells Lean to only rewrite at specificed positions
  rw [← add_mul] at h
  rw [add_comm 1] at h
  norm_num at h
  --trivial
  --rw [h]
  exact h

  -- simp at h   -- `simp` tries to simplify the goal or a hypothesis
  -- rw [two_plus_one_eq_three] at h   -- we can use our own lemmas in rewrite


#check add_mul

/- Algebraic structures in mathlib -/

#print Group
#print Ring
#print CommRing
#print Field

#check mul_inv_cancel
