import LeanCourse.Common
import Mathlib.Algebra.Order.Floor
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Irrational

open Real BigOperators
noncomputable section








/-
# Practical remarks
* Register on both Basis and eCampus for the course
* Link to the course repository:
  https://github.com/fpvandoorn/LeanCourse24
* Follow the instruction on that page
  to install Lean and download the repository.
* Do this at home, and ask for help on Friday if you get stuck.
* No homework due next week.
* Link to Mathematics in Lean:
  https://leanprover-community.github.io/mathematics_in_lean/
-/










/-
# Example

A sequence `u` of numbers converges to a number `l` if
`∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| < ε`
and a function `f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ ⇒ |f(x) - f(x₀)| < ε`

Fact: if `f` is continuous at `x₀` and `u` converges to `x₀` then
`f ∘ u : n ↦ f(u_n)` converges to `f(x₀)`.
-/
-- This is a single-line comment
/-
This is a multi-line
comment
`\R` becomes ℝ
-/

/-- The sequence `u` of real numbers converges to `l`. -/
def SequenceHasLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - l| < ε

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ →
  |f (x) - f (x₀)| < ε




lemma first_proof (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (u_lim : SequenceHasLimit u x₀)
    (f_cont : ContinuousAtPoint f x₀) :
    SequenceHasLimit (f ∘ u) (f x₀) := by {
  unfold SequenceHasLimit
  -- Let ε > 0 be arbitrary
  intro (ε : ℝ) (hε : ε > 0)
  -- Since `f` is continuous, we can pick a `δ > 0` such that
  -- for all `x`, `|x - x₀| < δ → |f(x) - f(x₀)| < ε`.
  unfold ContinuousAtPoint at f_cont
  obtain ⟨δ, hδ, f_prop⟩ := f_cont ε (by assumption)
  -- Since `u` converges to `x₀`, we can pick a `N` such that
  -- for all `n ≥ N`, `|u_n - x₀| < δ`.
  obtain ⟨N, u_prop⟩ := u_lim δ hδ
  -- We pick this `N` to show that `f ∘ u` has limit `f(x₀)`.
  use N
  -- If `n ≥ N` we have `|u_n - x₀| < δ`,
  intro n hn
  specialize u_prop n hn
  -- hence `|f(u_n) - f(x₀)| < ε`.
  specialize f_prop (u n) u_prop
  -- This finishes the proof.
  assumption
  }













/-!
# How does Lean help you?

* You can use Lean to verify *all* the details of a proof.
* Lean helps you during a proof by
  - displaying all information in the tactic state
  - keeping a proof organized
  - proving parts automatically using AI
* You can explore mathematics using
  Lean's mathematical library `Mathlib`

# General context

Proof assistants software exist since the early 70s.

There is currently a lot of momentum in formalized mathematics, especially Lean:
- AlphaProof
- Terrence Tao has started a few formalization projects
- A proof by Peter Scholze in condensed mathematics was verified in Lean.

Lean exists since 2013, and its mathematical library Mathlib since 2017.
-/









/- Lean is a calculator and programming language -/
#eval 2 + 3
#eval 2 ^ 5 * 7 - 3

-- compute the sum `0 + 1 + ⋯ + 100`
-- `List.range 101 = [0, 1, ..., 100]`
#eval Id.run do
  let mut sum := 0
  for i in List.range 101 do
    sum := sum + i
  return sum

/- We can also define our own function. -/

def fib : ℕ → ℕ
| 0     => 1
| 1     => 1
| n + 2 => fib n + fib (n + 1)

/- To apply a function `f` to an argument `x`,
you **cannot** write `f(x)` without a space!
You have to write `f (x)`,
with a space between the function and the argument.
You can omit the parentheses in case `x` is a variable: `f x`
-/
#eval fib (6)
#eval fib 13
#eval fib (fib 6)

#eval fib (5) + 5
#eval fib (5 + 5)
#eval fib 5 + 5





/- However, programming is not what this course is about.
We want to write proofs.

How does Lean check these proofs?

Answer: By giving a type to every mathematical object,
and checking that each function is applied
to an argument with the correct type.

The `#check` command asks Lean to display the type of an object.
Note the colon that means "has type" or "having type"
(think of it as "∈").
-/

#check fib

-- We can also define a function without giving it a name using `fun`.
#check fun x : ℝ ↦ x ^ 3
#check fun n : ℤ ↦ n ^ 3


#check 2
#check (2 : ℝ)
#check (5 / 2 : ℝ)
#eval (5 / 2 : ℚ)

/-
`fib` has type `ℕ → ℕ`, hence it expects natural numbers as inputs,
and produces natural numbers as outputs.

Hence `fib 1` is ok and has type `ℕ`.
-/

#check fib 1

/-
But `fib π` is not ok, we say it doesn't type-check.
-/

-- #check fib π
-- #check fib fib


/- There is a designated type `Prop` that contains all statements.

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

#check Nat.Prime
#check (Nat.Prime)
#check Nat.Prime 3
#check Nat.Prime 4

/- What is the type of the following definitions? -/

def add_complex_i (y : ℂ) : ℂ := y + Complex.I

#check add_complex_i

def less_than_pi (x : ℝ) : Prop := x < π

#check less_than_pi




/- Notice the difference between the following two types. -/

def less_than (x y : ℝ) : Prop :=
  x < y

-- ℝ → (ℝ → Prop)
#check (less_than)

def differentiable (f : ℝ → ℝ) : Prop :=
  Differentiable ℝ f

#check (differentiable)



/- If we have a statement `A : Prop`, we can prove `A` using *tactics*. -/

/- `rfl` proves equalities that are equal by definition. -/
example : 2 + 2 = 4 := by rfl
example (n m : ℕ) : n + m = n + m := by rfl

/- `ring` proves equalities that follow from the axioms of a ring. -/
example (a b c : ℝ) : (a * b) * c = b * (a * c) := by {
  ring
  }

example (a b : ℚ) :
  (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  ring

/- `rw` replaces the left-hand side of `h` with its right-hand side in the goal. -/
example (a b c d : ℝ) (h : a + b = c - d) : 2 * (a + b) = 2 * c - 2 * d := by {
  rw [h, mul_sub]
  }
