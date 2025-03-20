import Course.Common
import Course.LectureNotes.Week5

/-

Homework sheet 5
Due March 20 10am

All problems are mandatory unless stated otherwise.

Optional: Do all the problems in MIL Ch. 6.1, 6.2, 7.1

-/

namespace HW5

open Course.Week5

section Point3

#check Point2

@[ext]
structure Point3 (α : Type*) where
  x : α
  y : α
  z : α

example : Point3 ℕ := ⟨1, 2, 3⟩

variable {α : Type*}

example (a b : Point3 α) (h : a.x = b.x ∧ a.y = b.y ∧ a.z = b.z) : a = b := by
  ext
  · exact h.1
  · exact h.2.1
  · exact h.2.2

-- Define addition on `Point3 α` by componentwise addition in `α`
-- The instance parameter `[Add α]` makes sure that there is an addition in `α` that can be referred to using `+`
def add [Add α] : Point3 α → Point3 α → Point3 α := fun a b ↦ ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3⟩

-- Define an appropriate zero element
def zero [Zero α] : Point3 α := ⟨0, 0, 0⟩

-- Finish the following definition of additive commutative monoids
class AddCommMonoid' (M : Type*) extends Add M, Zero M where
  add_assoc : ∀ a b c : M, a + b + c = a + (b + c)
  add_zero : ∀ a : M, a + 0 = a
  add_comm : ∀ a b : M, a + b = b + a

export AddCommMonoid' (add_assoc add_zero add_comm) -- Make names of axioms available in current namespace

#check AddCommMonoid

-- Show that if `α` is an `AddCommMonoid'`, then so is `Point3 α`
instance [AddCommMonoid' α] : AddCommMonoid' (Point3 α) where
  add := add
  zero := zero
  add_assoc := by
    #check AddCommMonoid'.add_assoc
    intros; ext <;> exact add_assoc _ _ _
  add_zero := by intro; ext <;> exact add_zero _
  add_comm := by intros; ext <;> exact add_comm _ _

end Point3

section

-- Recall the `CommMonoid'` typeclass defined in class
#check CommMonoid'

-- Compare this to the Mathlib definition
#check CommMonoid

variable {M : Type*}

-- Show that if we have a Mathlib `CommMonoid`, we also have a `CommMonoid'`
instance [CommMonoid M] : CommMonoid' M where
  one' := 1
  mul' := fun a b ↦ a * b
  mul_assoc' := mul_assoc
  mul_one' := mul_one
  mul_comm' := mul_comm

end

section

-- Let's define metric spaces in Lean
class MetricSpace' (X : Type*) where
  d : X → X → ℝ -- Every two points `x y : X` are assigned a *distance* `d x y`
  d_nonneg : ∀ x y : X, 0 ≤ d x y -- Distances are nonnegative
  d_symm : ∀ x y : X, d x y = d y x -- Distances are symmetric
  d_eq_zero_iff : ∀ x y : X, d x y = 0 ↔ x = y -- The only way distance can be `0` is if the two points are equal
  d_triangle : ∀ x y z : X, d x z ≤ d x y + d y z -- The triangle ienquality: distance from `x` to `z` can't be greater than distance
                                                  -- of `x` to `y` plus distance from `y` to `x`

export MetricSpace' (d d_nonneg d_eq_zero_iff d_triangle)

-- Compare this to the Mathlib definition
#check MetricSpace


-- Let's define a metric space structure on the real numbers.
-- It's okay to use `simp`-like tactics, but as an extra challenge you can try to avoid it.
#check abs_sub_comm
#check abs_eq_zero
#check eq_of_sub_eq_zero
instance : MetricSpace' ℝ where
  d := fun x y ↦ |x - y|
  d_nonneg := fun _ _ ↦ abs_nonneg _
  d_symm := fun _ _ ↦ abs_sub_comm _ _
  d_eq_zero_iff := by
    intro x y
    constructor
    · intro h
      exact eq_of_sub_eq_zero (abs_eq_zero.mp h)
    · intro h
      dsimp
      rw [h, sub_self, abs_zero]
  d_triangle := by
    intro x y z
    calc
      _ = |(x - y) + (y - z)| := by group
      _ ≤ _ := abs_add _ _

variable {X : Type*}

lemma d_self [MetricSpace' X] (x : X) : d x x = 0 := by
  simp [d_eq_zero_iff]

open Finset

-- Show the following by induction on `N` using the triangle inequality `d_triangle` in the induction step.
example [MetricSpace' X] (a : ℕ → X) (N : ℕ) : d (a 0) (a N) ≤ ∑ n ∈ range N, d (a n) (a (n + 1)) := by
  induction N with
  | zero => simp [d_self]
  | succ N ih =>
    calc
      _ ≤ d (a 0) (a N) + d (a N) (a (N + 1)) := d_triangle _ _ _
      _ ≤ _ := by rw [sum_range_succ]; gcongr

end

end HW5
