import LeanCourse.Common
open Real Function Set
noncomputable section





/-
# Practical remarks
* Assignment 4 due on 5.11. Upload it to eCampus.
-/

/- # Last Week -/

/-
How to work with `∃, ∨, ¬`:
* Prove `∃ x, P x` using `use` and use a hypothesis using `obtain ⟨x₀, hx₀⟩ := h`
* Prove `P ∨ Q` using `left`/`right` and use a hypothesis using `obtain hP|hQ := h`
* Negation works like implication
* Tactics to reason with negations and `False`:
  `contradiction` / `exfalso`
* Tactics for classical reasoning:
  `by_contra h` / `by_cases h : p` / `push_neg`

* I added a *tactic cheat sheet* to this repository.

* `Set α` is the type of sets with elements from `α`
* Prove two sets equal by using the `ext` tactic.
* We can use the notation `{x : α | P x}` for the set of elements satisfying `P`.
-/

variable {ι α β : Type*} {s t : Set α}

example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := by rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := by rfl
example : s \ t = {x | x ∈ s ∧ x ∉ t} := by rfl
example : sᶜ = {x : α | x ∉ s} := by rfl
example : (∅ : Set α) = {x | False} := by rfl
example : (univ : Set α) = {x | True} := by rfl

example (P : α → Prop) (x : α) :
    x ∈ {y | P y} ↔ P x := by
  simp

example (x : ℝ) (hx : x ≠ 0) : x * 1 / x = 1 := by
  apply?

/-
# Today: Sets (continued) and Functions
-/

/-
## Other operations on sets
-/

/- We can take power sets. -/
example (s : Set α) : powerset s = {t | t ⊆ s} := by rfl -- \powerset

-- What is the type of `powerset s`?
#check powerset s


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
  ext x
  simp
  rw [and_comm]
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
  constructor
  · intro h x hx
    simp
    apply h
    -- simp
    exact?
  · intro h y hy
    obtain ⟨x, x_in_s, fx_eq_y⟩ := hy
    subst y
    specialize h x_in_s
    exact h
  }


/- We can do pointwise operations on sets (e.g. the Minkowski sum). -/

open Pointwise

example (s t : Set ℝ) :
    s + t = {x : ℝ | ∃ a ∈ s, ∃ b ∈ t, a + b = x } := by rfl
example (s t : Set ℝ) : -s = {x : ℝ | -x ∈ s } := by rfl

example : ({1, 3, 5} : Set ℝ) + {0, 10} = {1, 3, 5, 11, 13, 15} := by {
  ext x
  simp [@mem_add]
  norm_num -- normalizes numeric expressions
  tauto
  }


/-
## Inverse of a function.

Suppose we have a function `f : α → β`.
Can we find a inverse `g : β → α` of `f`?
We have to assume that `f` is bijective...

But suppose we try, suppose that `∃ x, f x = y`, and we want to define `g y`.
It must be one of the `x` such that `f x = y`.
We can choose one such `x` using *the axiom of choice*.
-/

section Inverse

variable (f : α → β)

#check Classical.choose
#check Classical.choose_spec


/- This doesn't look like the axiom of choice,
since we're only choosing 1 element.
However, this is a *function* that takes a proof
of an existential and produces an element in `α` from it.
This is called *global choice* and it is a bit stronger
than the usual axiom of choice.
As an exercise you will prove the usual axiom of choice from it.
-/

/- When working with choice,
opening the namespace `Classical` is useful.
If Lean complains that is cannot synthesize `Decidable` or `DecidableEq`
then you should `open Classical`. -/
open Classical

def conditionalInverse (y : β)
  (h : ∃ x : α, f x = y) : α :=
  Classical.choose h

lemma invFun_spec (y : β) (h : ∃ x, f x = y) :
    f (conditionalInverse f y h) = y :=
  Classical.choose_spec h

/- We can now define the function by cases
on whether it lies in the range of `f` or not. -/

variable [Inhabited α]
def inverse (f : α → β) (y : β) : α :=
  if h : ∃ x : α, f x = y then
    conditionalInverse f y h else default

/- We can now prove that `inverse f` is a right-inverse if `f` is surjective
and a left-inverse if `f` is injective.
We use the `ext` tactic to show that two functions are equal. -/
lemma rightInv_of_surjective (hf : Surjective f) :
    f ∘ inverse f = id := by {
  ext y
  simp
  unfold Surjective at hf
  obtain ⟨x, hx⟩ := hf y
  subst y
  simp [inverse]
  rw [invFun_spec f]
  }

lemma leftInv_of_injective (hf : Injective f) :
    inverse f ∘ f = id := by {
  ext x
  simp
  apply hf
  simp [inverse, invFun_spec]
  }

/- We can package this together in one statement. -/
lemma inv_of_bijective (hf : Bijective f) :
    ∃ g : β → α, f ∘ g = id ∧ g ∘ f = id := by {
  let g : β → α := inverse f
  use g
  constructor
  · apply rightInv_of_surjective
    exact Bijective.surjective hf
  · apply leftInv_of_injective
    exact Bijective.injective hf
  }

end Inverse
