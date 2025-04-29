import Course.Common
import Lean

/-
Today: Macros and monads

Lean can be used to extend its own syntax and semantics.
In fact, much of Lean is written in Lean itself. Mathlib tactics are written in Lean.
We can only scratch the surface of metaprogramming -- this is only meant to give you a first flavor.

Recommended reading:
*Metaprogramming in Lean 4*: https://leanprover-community.github.io/lean4-metaprogramming-book
Most relevant for today are Ch. 2, 5, 6

-/

namespace Course.Week10

open Lean Meta Elab Tactic

/- # Defining new notation -/

-- We can define our own notation in Lean
namespace Test1

#check_failure 𝕂

scoped notation "𝕂" => ℝ

#check 𝕂

variable {a b : ℝ × ℝ}

def my_prod : ℝ × ℝ := ⟨a.2 * b.1, a.1 * b.2⟩

notation "≪" a "," b "≫" => my_prod (a := a) (b := b)

#check ≪a,b≫

-- We can also define custom operators

infix:65 " ⊕ " => HAdd.hAdd   -- `65` indicates operator precedence
-- `infixl` or `infixr` can be used to indicate left or right associativity (left is the default)

#check a ⊕ b
#check a + b

example : a + b = a ⊕ b := by rfl

end Test1


/- A first overview of the Lean compilation process -/

-- Step 1: Parsing
-- Passing from source code strings to Syntax objects
#check Syntax -- represents a piece of Lean syntax
-- Macros operate at the level of syntax. You can think of a macro as a map `Syntax → Syntax`.

-- Step 2: Elaboration
-- This is where syntax is assigned meaning. Elaboration means to translate `Syntax` objects into `Expr` objects
#check Expr
-- The `elab` command allows us to define custom elaborators (we'll see this later)

-- Step 3: Evaluation
-- This where Lean expressions are compiled into native C code that a C compiler can understand. Less relevant if we're only interested in proving theorems.

-- Delaboration: The InfoView in VS Code lets us look at Lean expressions (`Expr`), to display these in a convenient form ("pretty printing"), `Expr` must be converted back into `Syntax` (delaboration).
-- These are then turned into strings.

namespace Test2
-- `notation` and `infix`, etc. are themselves implemented using
-- `syntax` and `macro_rules`

syntax "𝕂" : term -- Used to introduce new syntax elements `term` is the *syntax category* for all Lean terms

-- While the syntax has been introduced, it doesn't have a meaning yet: no *elaborator* has been defined
#check_failure 𝕂

-- We can define an elaborator
macro_rules | `(term|𝕂) => `(term|ℝ)    -- Note the backticks `

#check 𝕂

-- A shortcut for `syntax` + `macro_rules` is `macro`
macro "𝔽" : term => `(term|ℝ)

#check 𝔽

end Test2


namespace TacticTest

/- The simplest way to define new tactics is using macros.  -/

macro "my_sorry" : tactic => `(tactic|sorry) -- `tactic` is the syntax category for tactics

example : 1 ≠ 1 := by
  my_sorry

-- Axioms can be introduced with `axiom`
axiom evilAxiom : False

macro "cheat" : tactic => `(tactic|exact False.elim evilAxiom)

def myTheorem: 1 ≠ 1 := by
  cheat

#print axioms myTheorem

syntax "my_tactic" : tactic

-- example : 1 = 1 := by
--   my_tactic -- 'not implemented' error

macro_rules | `(tactic|my_tactic) => `(tactic|rfl)

example : 1 = 1 := by
  my_tactic

-- We can define multiple `macro_rules`
macro_rules | `(tactic|my_tactic) => `(tactic|assumption)

example {P : Prop} (h : P) : P := by
  my_tactic

-- Macros are allowed to be recursive

macro_rules | `(tactic|my_tactic) => `(tactic|intro; my_tactic)

example {α : Type} : ∀ x : α, x = x := by
  my_tactic

macro_rules | `(tactic|my_tactic) => `(tactic|constructor; my_tactic)

example {α : Type} : ∀ x y : α, x = x ∧ y = y := by
  my_tactic

macro "continuous_integrable" : tactic => `(tactic|focus (apply ContinuousOn.intervalIntegrable; fun_prop))

open intervalIntegral Real in
example : IntervalIntegrable (fun x : ℝ ↦ Real.sin (x ^ 2)) length 0 1 := by
  continuous_integrable

end TacticTest


/- # Programming in Lean -/

/- One can use Lean as a general-purpose programming language, including the possibility
of writing code in a more imperative style. It is also possible to compile Lean code to executable files.

A basic issue is that in pure functional programming languages (such as Lean) functions can't have
*side-effects*, that is, any behavior other than returning a value of specified type for every
set of (correctly typed) inputs.
Side-effects are essential to general-purpose programming: think of error handling, exceptions,
logging, reading/writing to memory, interactions with the file system, the user, the internet, etc.

The solution is to use a functional programming pattern called a *monad*.
(The name derives from category theory and is consistent with the mathematical meaning, but it's not
important for a first understanding of how to use monads.)

There are lots of different monads to allow different kinds of side effects.
-/

-- `IO` is a (very complicated) example of a monad that (among other things) provides access to lots of input/output functionality.
#check IO -- Monads always have type `Type → Type`

-- Let us write a Lean version of the C program `void main() { printf("Hello World!"); }`
def main : IO Unit := do -- `do` notation is used to enter `imperative mode`
  IO.println "Hello World!"
  -- return

#eval main

-- an example with monadic return value
def printAndReturnSum (a b : ℕ) : IO ℕ := do
  let result := a + b
  IO.println s!"The sum of a={a} and b={b} equals {result}" -- String formatting
  return result

#eval printAndReturnSum 1 5

run_cmd do -- `run_cmd` can be used to execute code
  -- `logInfo` can be used to print a message in InfoView
  logInfo "Hello World!"
  -- `let` is used to introduce local variables
  let my_string := "Test"
  -- use `mut` to create a mutable local variable
  let mut my_mutable_string := "A"
  my_mutable_string := my_mutable_string ++ "BC"
  logInfo my_mutable_string
  -- `dbg_trace` is another way to log a message used for debugging
  dbg_trace my_mutable_string
  -- to "unpack" a monadic value use `←`
  let result := printAndReturnSum 7 10 -- `result` is not of type `ℕ`, but of type `IO ℕ`
  -- use `←` to unpack the monadic value and get the value of type `ℕ`
  let result' ← result
  logInfo s!"result = {result'}"


/- In Lean, `Monad` is a typeclass that looks something like this: -/
namespace MyMonad

-- For every monad `m` and every type `α` there is a "monadic type" `m α`.
-- You can roughly think of values of type `m α` as bundling values of type `α`
-- with information about the "current state" that encapsulates side-effects
class Monad (m : Type → Type) where
  -- Describes how to wrap a "pure" value of type `α` into a "monadic value" of type `m α`
  pure {α : Type} : α → m α

  -- Think of this as the operation that takes a "monadic value", applies a given function to it
  -- and returns a monadic output value.
  bind {α β : Type} : m α → (α → m β) → m β

end MyMonad

#check Monad -- The actual implementation of the Monad typeclass is a bit more technical

/-
Roughly speaking, every kind of side-effect comes with a monad type class
that can be used to make ordinary output types `monadic`, i.e. bundling them with side-effect data.
-/

-- Some important examples of monads:
#check Option -- Wraps a value, or absence of a value ("none")

#check Option.some 1
#check Option.none

#check Except String -- Monad for exception handling
#check Id -- Identity monad that doesn't do anything, but allows us to use monadic API
#check IO -- IO monad
-- Metaprogramming monadic hierarchy
#check CoreM -- Base monad for metaprogramming: gives access to Lean environment + IO
#check MetaM -- CoreM + access to metavariables
#check TacticM -- Most advanced -- can do everything needed to write tactics

-- A good overview of Lean's monadic hierarchy is here:
-- https://github.com/leanprover-community/mathlib4/wiki/Monad-map

-- As an example let us write a program that sums reciprocals of a list of natural numbers throwing an error when any of the numbers is zero

def divide (n : ℕ) : Except String ℚ := -- Return `1 / n` or error when `n = 0`
  match n with
  | 0 => .error "Division by zero!"
  | n + 1 => .ok (1 / (n + 1))

-- `Except String` is a monad, so we can also use `do` notation to write this in imperative style
def divide' (n : ℕ) : Except String ℚ := do
  if n = 0 then
    throw "Division by zero!"
  return 1 / n

#eval divide 0
#eval divide' 5

def sum_reciprocal (lst : List ℕ) : Except String ℚ := do
  let mut total : ℚ := 0
  for k in lst do
    total := total + (← divide k)
  return total

#eval sum_reciprocal [1, 2, 3, 4]
#eval sum_reciprocal [1, 0, 3, 4]

end Course.Week10
