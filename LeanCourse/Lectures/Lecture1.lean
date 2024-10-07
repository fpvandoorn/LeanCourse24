import LeanCourse.Common
import Mathlib.Algebra.Order.Floor
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Irrational
open Real BigOperators
noncomputable section

















/-
# Example

A sequence `u` of numbers converges to a number `l` if
`∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| < ε`
and a function `f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ ⇒ |f(x) - f(x₀)| < ε`

Fact: if `f` is continuous at `x₀` and `u` converges to `x₀` then
`f ∘ u : n ↦ f(u_n)` converges to `f(x₀)`.
-/


/-- The sequence `u` of real numbers converges to `l`. -/
def SequenceHasLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - l| < ε

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hu : SequenceHasLimit u x₀) (hf : ContinuousAtPoint f x₀) :
    SequenceHasLimit (f ∘ u) (f x₀) := by {
    intro ε hε
    obtain ⟨δ : ℝ, hδ : δ > 0, h2f : ∀ x, |x - x₀| < δ → |f x - f x₀| < ε⟩ := hf ε hε
    obtain ⟨N : ℕ, hN : ∀ n ≥ N, |u n - x₀| < δ⟩ := hu δ hδ
    use N
    intro (n : ℕ) (hn : n ≥ N)
    have : |u n - x₀| < δ := hN n hn
    have : |f (u n) - f x₀| < ε := h2f (u n) this
    assumption
    }













/-!
# How does Lean help you?

* Requires details
* Displays tactic state
* Keep a proof organized

# How does it help mathematicians?

* Check mathematics
* Create mathematics
* Explore mathematics

# General context

Proof assistants software exist since the early 70s.

There is currently a lot of momentum in formalized mathematics. I'm setting up a research group in Bonn on formalized mathematics.

Lean exists since 2013, and has a rapidly growing mathematical library since 6 years.
-/









/- Lean is a calculator and programming language -/
#eval 2 + 3

#eval 2 ^ 3 + 4 * 5 - 6

-- compute the sum `0 + 1 + ⋯ + 100`
#eval Id.run do
  let mut i := 0
  -- `List.range 101 = [0, 1, ..., 100]`
  for j in List.range 101 do
    i := i + j
  return i

-- compute the sum `0 + 1 + ⋯ + 100` again
-- `Finset.range 101 = {0, 1, ..., 100}`
#eval ∑ i in Finset.range 101, i ^ 2





/- That is not what this course is about.
We want to write proofs.

How does Lean check these proofs?

Answer: By giving a type to every mathematical object.

The `#check` command asks Lean to display the type of an object.
Note the colon that means "has type" or "having type".
-/

#check 1

#check fun x : ℝ ↦ x^2
#check fun n : ℤ ↦ n^2


/- We can write our own definitions. -/
def u : ℕ → ℝ := fun n ↦ 1/n


/-
The most basic protection against error is type checking: mathematical objects
must be combined according to their type.

`u` has type `ℕ → ℝ`, hence it expects natural numbers as inputs, and produces
real numbers as outputs.

Hence `u 1` is ok and has type `ℝ`.
-/

#check u 1
#check u (1 + 2)
#check (u 1) + 2
#check u (1 + 2)

/-
But `u π` is not ok, we say it doesn't type-check.
-/

-- #check u π
-- #check u u


/- The type `Prop` contains all statements

Unfortunate clash in terminology:
* In math: "Proposition" means
    useful proven statement (less important than a theorem)
* In logic: "Proposition" means
    any statement that can be either true or false.
-/

#check 2 + 2 = 4
#check 3 < π

#check 2 + 2 = 5

def Statement1 : Prop :=
  ∃ p, Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)

def Statement2 : Prop :=
  ∀ n : ℕ, ∃ p ≥ n, Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)

def Statement3 : Prop :=
  ∀ n : ℕ, ∃ p ≥ n, Prime p ∧ Prime (p + 2)




/- Nat.Prime is a predicate on natural numbers, so it has type `ℕ → Prop`. -/

#check (Nat.Prime)

/- What is the type of the factorial function? -/
#check (Nat.factorial)

/- What is the type of the predicate stating that a natural number is at least 2? -/
#check (Nat.AtLeastTwo)

#check (differentiable)



/- If we have a statement `A : Prop`, we can prove `A` using *tactics*. -/

example : 2 + 2 = 4 := by rfl


example : 2 + 2 ≠ 5 := by simp
