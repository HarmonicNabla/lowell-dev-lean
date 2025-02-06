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
#check ℕ

/- To print the definition of a type we can use `#print` -/

#print Nat

/- `#eval` -/

/- In mathematics we essentially do just two different things: introduce definitions and prove theorems about them -/

/- Definitions can be made using `def` -- identifiers must be unique within a `namespace` -/

--def Even : Prop := sorry

/- Definitions can use recursion -/

--def Factorial : ℕ := sorry

/- Theorems can be introduced using `theorem` -/


--theorem myTheorem

example (n : ℕ): n = n := sorry

/- Theorem statements are types. Proving a theorem means providing an instance of that type (a `proof term`) -/

variable (A B : Prop)

theorem modus_ponens (h₁ : A) (h₂ : A → B) : B := sorry

/- Tactics -/

example (n : ℕ) : n * 0 = 0 := sorry

/- # Proving identities -/

/- Rewriting -/

#check mul_assoc
#check mul_comm

example (a b c : ℝ) : a * b * c = a * c * b := sorry

/- Calculation -/


/- Ring -/

example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := sorry

example (a b : ℝ) : (a+b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3 := sorry

/- Linarith -/

example (a b c : ℝ) (h : a + b = c) (h' : 2*b + c = a) : b = 0 := sorry


/- Algebraic structures in mathlib -/

#print Group
#print Ring

#check mul_inv_cancel
