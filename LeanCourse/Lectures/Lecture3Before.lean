import LeanCourse.Common
open Real Function
noncomputable section





/-
# Practical remarks
* Assignment 3 due on 29.10.2023. Upload it to eCampus.
-/

/- # Last Week -/

/-
Tactics we saw last time:
* to search for a lemma, use `exact?`, `apply?`, `rw?`,
  `#loogle`, `#leansearch` or autocomplete
* `linarith`, `gcongr` and `calc` for reasoning with inequalities
* How to work with `→` and `∀`.
  - `intro` for introducing a hypothesis
  - `have` or `specialize` for forwards reasoning
  - `apply` for backwards reasoning
* How to work with `∧` and `↔`
  - `constructor` to prove them
  - `obtain` to split them
  - use the projections `.1` and `.2` to take the components
  - `rw [h]` works with `↔`
-/



/- # Today: Logic (continued) and Sets -/

/- ## Extential quantifiers -/



/-
In order to prove `∃ x, P x`, we give some `x₀` using tactic `use x₀` and
then prove `P x₀`. This `x₀` can be any expression.

In order to use `h : ∃ x, P x`, we use can use
`obtain ⟨x₀, hx₀⟩ := h`
to fix one `x₀` that works.
-/

example {α : Type*} [PartialOrder α]
    (isDense : ∀ x y : α, x < y → ∃ z : α, x < z ∧ z < y)
    (x y : α) (hxy : x < y) :
    ∃ z₁ z₂ : α, x < z₁ ∧ z₁ < z₂ ∧ z₂ < y := by {
  sorry
  }



/- Lean supports shorthands for quantifiers
followed by an infix predicate (`<`, `≥`, `∈`, ...) -/
example (P : ℕ → Prop) : (∃ n > 3, P n) ↔ (∃ n, n > 3 ∧ P n) := by
  rfl

example (P : ℕ → Prop) : (∀ n ≤ 10, P n) ↔ (∀ n, n ≤ 10 → P n) := by
  rfl



/- ## Disjunctions -/

/-
Lean denotes by `∨` the logical OR operator.

In order to directly prove a goal `P ∨ Q`,
we use either the `left` tactic and prove `P` or the `right`
tactic and prove `Q`.

In order to make use of an assumption
  `h : P ∨ Q`
we use the obtain tactic:
  `obtain hP|hQ := h`
which creates two proof branches: one branch assuming `hP : P`,
and one branch assuming `hQ : Q`.
-/

variable (a b : ℝ)
#check (mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0)

example : a = a * b → a = 0 ∨ b = 1 := by {
  sorry
  }


example (f : ℝ → ℝ) (hf : StrictMono f) : Injective f := by {
  sorry
  }




/- ## Negation

The negation `¬ A` just means `A → False`,
where `False` is a statement without a proof.
We can use the same tactics as for implication:
`intro` to prove a negation, and `apply` to use one. -/

example {p : Prop} (h : p) : ¬ ¬ p := by
  intro h2
  exact h2 h


example {α : Type*} {p : α → Prop} : ¬ (∃ x, p x) ↔ ∀ x, ¬ p x := by {
  sorry
  }



/- We can use `exfalso` to use the fact that
everything follows from `False`: ex falso quod libet -/
example {p : Prop} (h : ¬ p) : p → 0 = 1 := by {
  sorry
  }




/- `contradiction` proves any goal
when two hypotheses are contradictory. -/
example {p : Prop} (h : ¬ p) : p → 0 = 1 := by
  intro hp
  contradiction







/-
We can use classical reasoning (with the law of the excluded middle)
using the following tactics.

* `by_contra h` start a proof by contradiction.
* `by_cases h : p` to start a proof by cases on statement `p`.
* `push_neg` to push negations inside quantifiers and connectives.
-/
example (p q : Prop) (h : ¬q → ¬p) : p → q := by
  intro hp
  by_contra hq
  exact h hq hp

example (p q r : Prop) (h1 : p → r) (h2 : ¬ p → r) : r := by
  by_cases hp : p
  · exact h1 hp
  · exact h2 hp

example {α : Type*} {p : α → α → Prop} :
    ¬ (∃ x y, p x y) ↔ ∀ x y, ¬ p x y := by
  push_neg
  rfl



/-- The sequence `u` of real numbers converges to `l`.
`∀ ε > 0, ...` means `∀ ε, ε > 0 → ...` -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (u : ℕ → ℝ) (l : ℝ) : ¬ SequentialLimit u l ↔
    ∃ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| ≥ ε := by {
  sorry
  }

lemma sequentialLimit_unique (u : ℕ → ℝ) (l l' : ℝ) :
    SequentialLimit u l → SequentialLimit u l' → l = l' := by {
  sorry
  }





/- # Sets

In set theory you can make sets with arbitrary elements.
In Lean, all sets have to be sets of elements from a specific type.

If `s : Set α` then `s` is a set with elements from `α`.
-/

#check Set ℕ
#check Set ℝ

variable {α β ι : Type*} (x : α) (s t u : Set α)

#check x ∈ s       -- \in or \mem
#check x ∉ s       -- \notin
#check s ⊆ t       -- \sub
#check s ⊂ t       -- \ssub


#check s ∩ t       -- \inter or \cap
#check s ∪ t       -- \union or \cup
#check s \ t       -- it is the normal symbol `\` on your keyboard,
                   -- but you have to write `\\` or `\ ` to enter it
#check sᶜ          -- \compl or \^c
#check (∅ : Set α) -- \empty
#check (Set.univ : Set α)

open Set

#check (univ : Set α)






/- Showing that `x` is an elements of `s ∩ t`, `s ∪ t` or `sᶜ`
corresponds by definition to conjunction, disjunction or negation. -/

#check mem_inter_iff x s t
#check mem_union x s t
#check mem_compl_iff s x

#check mem_univ x
#check not_mem_empty x



/- There are various ways to prove this:
* use lemma `mem_inter_iff`
* use `simp`
* directly apply `constructor`
* give a direct proof: `⟨xs, xt⟩`
-/
example (hxs : x ∈ s) (hxt : x ∈ t) : x ∈ s ∩ t := by
  constructor
  · assumption
  · assumption

example (hxs : x ∈ s) : x ∈ s ∪ t := by
  left
  assumption









/- `s ⊆ t` means that for every element `x` in `s`,
  `x` is also an element in `t`. -/

#check subset_def

example : s ∩ t ⊆ s ∩ (t ∪ u) := by {
  sorry
  }

/- you can also prove it at thge level of sets, without talking about elements. -/
example : s ∩ t ⊆ s ∩ (t ∪ u) := by {
  sorry
  }





/- ## Proving two Sets are equal

You can prove that two sets are equal by applying `subset_antisymm`
or using the `ext` tactic.

`ext x` can prove that `s = t` if `x ∈ s ↔ x ∈ t` for a new variable `x`.
-/
#check (subset_antisymm : s ⊆ t → t ⊆ s → s = t)

example : s ∩ t = t ∩ s := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2, hx.1⟩
  · intro hx
    exact ⟨hx.2, hx.1⟩

/- We can also use existing lemmas and `calc`. -/
example : (s ∪ tᶜ) ∩ t = s ∩ t := by
  calc (s ∪ tᶜ) ∩ t
      = (s ∩ t) ∪ (tᶜ ∩ t)  := by rw?
    _ = s ∩ t ∪ ∅           := by rw?
    _ = s ∩ t               := by rw?





/-
# Set-builder notation
-/

def Evens : Set ℕ := {n : ℕ | Even n}
def Odds : Set ℕ := {n | Odd n}

example : Evensᶜ = Odds := by {
  sorry
  }


example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := by rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := by rfl
example : s \ t = {x | x ∈ s ∧ x ∉ t} := by rfl
example : sᶜ = {x | x ∉ s} := by rfl
example : (∅ : Set α) = {x | False} := by rfl
example : (univ : Set α) = {x | True} := by rfl


/-
# Other operations on sets
-/

/- We can take power sets. -/
example (s : Set α) : powerset s = {t | t ⊆ s} := by rfl -- \powerset

-- What is the type of `powerset s`?
-- #check powerset s


/- We can take unions and intersections of families of sets in three different ways:
* Given a family of sets `C : ι → Set α`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements of `ι`.
-/
example (C : ι → Set α) :
    ⋃ i : ι, C i = {x : α | ∃ i : ι, x ∈ C i} := by ext; simp

example (C : ι → Set α) :
    ⋂ i : ι, C i = {x : α | ∀ i : ι, x ∈ C i} := by ext; simp

/-
* Given a family of sets `C : ι → Set α` and `s : Set ι`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements in `s`.
-/
example (s : Set ι) (C : ι → Set α) :
    ⋃ i ∈ s, C i = {x : α | ∃ i ∈ s, x ∈ C i} := by ext; simp

example (s : Set ι) (C : ι → Set α) :
    ⋂ i ∈ s, C i = {x : α | ∀ i ∈ s, x ∈ C i} := by ext; simp

/-
* Given a collection of sets `C : Set (Set α)`
  we can take the union and intersection of `c`
  for all `c ∈ C`
-/

example (𝓒 : Set (Set α)) :
    ⋃₀ 𝓒 = {x : α | ∃ s ∈ 𝓒, x ∈ s} := by ext; simp

example (𝓒 : Set (Set α)) :
    ⋂₀ 𝓒 = {x : α | ∀ s ∈ 𝓒, x ∈ s} := by ext; simp


example (C : ι → Set α) (s : Set α) :
    s ∩ (⋃ i, C i) = ⋃ i, (C i ∩ s) := by {
  sorry
  }

/- We can take images and preimages of sets.

`f ⁻¹' s` is the preimage of `s` under `f`.
`f '' s` is the image of `s` under `f`.

On paper, you would write `f(A)` or `f[A]` for the image
and `f⁻¹(B)` or `f⁻¹[B]` for the preimage.
This notation is somewhat ambiguous, so we use different notation in Lean.

-/

example (f : α → β) (s : Set β) : f ⁻¹' s = { x : α | f x ∈ s } := by rfl

example (f : α → β) (s : Set α) : f '' s = { y : β | ∃ x ∈ s, f x = y } := by rfl


example {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by {
  sorry
  }


/- We can do pointwise operations on sets (i.e. the Minkowski sum). -/

open Pointwise

example (s t : Set ℝ) :
    s + t = {x : ℝ | ∃ a ∈ s, ∃ b ∈ t, a + b = x } := by rfl
example (s t : Set ℝ) : -s = {x : ℝ | -x ∈ s } := by rfl

example : ({1, 3, 5} : Set ℝ) + {0, 10} = {1, 3, 5, 11, 13, 15} := by {
  sorry
  }
