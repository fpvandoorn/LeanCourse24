import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8.1.
  Chapter 7 explains some of the design decisions for classes in Mathlib.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 19.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


/- Prove the following exercises about functions where the domain/codomain are
subtypes. -/

abbrev PosReal : Type := {x : ℝ // x > 0}

/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by {
  intro x y hxy
  dsimp
  apply log_le_log
  · apply Subtype.prop
  · show f x ≤ f y
    apply hf
    exact hxy
  }

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : range f ⊆ {x | x > 0}) (h2f : Monotone f) :
  Monotone (log ∘ f) := by {
  intro x y hxy
  apply log_le_log
  · apply hf
    exact mem_range_self x -- `exact?`
  · exact h2f hxy
  }

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by {
  intro x y hxy
  dsimp
  apply hf
  simp_rw [Subtype.mk_le_mk, exp_le_exp, hxy]
  }

/- Only specify that a function is well-behaved on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by {
  intro x y hxy
  apply hf
  · apply exp_pos
  · apply exp_pos
  · rw [exp_le_exp]
    exact hxy
  }



variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup


/- State and prove that the preimage of `U` under the composition of `φ` and `ψ` is a preimage
of a preimage of `U`. This should be an equality of subgroups! -/
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : Subgroup.comap (ψ.comp φ) U = Subgroup.comap φ (Subgroup.comap ψ U):=
  rfl


/- State and prove that the image of `S` under the composition of `φ` and `ψ`
is a image of an image of `S`. -/
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : Subgroup.map (ψ.comp φ) S = Subgroup.map ψ (Subgroup.map φ S) := by
  ext
  simp at *


/- Define the conjugate of a subgroup, as the elements of the form `xhx⁻¹` for `h ∈ H`. -/
def conjugate (x : G) (H : Subgroup G) : Subgroup G where
  carrier := (x * · * x⁻¹) '' H
  one_mem' := by
    dsimp
    use 1, H.one_mem
    simp
  inv_mem' := by
    dsimp
    rintro _ ⟨y, hy, rfl⟩
    use y⁻¹, H.inv_mem hy
    group
  mul_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    use y * z, H.mul_mem hy hz
    group

/- Now let's prove that a group acts on its own subgroups by conjugation. -/

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by {
  ext x
  simp [conjugate]
  }

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by {
  ext x
  constructor
  · rintro ⟨h, h_in, rfl⟩
    use y*h*y⁻¹
    constructor
    · use h
    · group
  · rintro ⟨-, ⟨h, h_in, rfl⟩, rfl⟩
    use h, h_in
    group
  }


/- Saying that a group `G` acts on a set `X` can be done with `MulAction`.
The two examples below show the two properties in the definition of a group action. -/
#print MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
example (g g' : G) (x : X) :
    (g * g') • x = g • (g' • x) := by exact mul_smul g g' x -- `exact?`

example (x : X) :
    (1 : G) • x = x := by exact MulAction.one_smul x -- `exact?`

/- Now define `conjugation` -/
instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := conjugate_one
  mul_smul := conjugate_mul




/-! # Exercises to hand-in. -/


/- A `Setoid` is the name for an equivalence relation in Lean.
Let's define the smallest equivalence relation on a type `X`. -/
def myEquivalenceRelation (X : Type*) : Setoid X where
  r x y := x = y
  iseqv := {
    refl := fun x ↦ rfl
    symm := fun h ↦ h.symm
    trans := fun h1 h2 ↦ h1.trans h2
  }

/- This simp-lemma will simplify `x ≈ y` to `x = y` in the lemma below. -/
@[simp] lemma equiv_iff_eq (X : Type*) (x y : X) :
  letI := myEquivalenceRelation X; x ≈ y ↔ x = y := by rfl

/-
Now let's prove that taking the quotient w.r.t. this equivalence relation is
equivalent to the original type.

Use `Quotient.mk` to define a map into a quotient (or its notation `⟦_⟧`)
Use `Quotient.lift` to define a map out of a quotient.
Use `Quotient.sound` to prove that two elements of the quotient are equal.
Use `Quotient.ind` to prove something for all elements of a quotient.
You can use this using the induction tactic: `induction x using Quotient.ind; rename_i x`.
-/
def quotient_equiv_subtype (X : Type*) :
    Quotient (myEquivalenceRelation X) ≃ X where
      toFun := Quotient.lift id (by
        intro x y h
        simp at h
        rw [h]
        )
      invFun := Quotient.mk _
      left_inv x := by
        induction x using Quotient.ind
        simp
      right_inv x := by
        simp



section GroupActions

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/- Below is the orbit of an element `x ∈ X` w.r.t. a group action by `G`.
Prove that the orbits of two elements are equal
precisely when one element is in the orbit of the other. -/
def orbitOf (x : X) : Set X := range (fun g : G ↦ g • x)

lemma orbitOf_eq_iff (x y : X) : orbitOf G x = orbitOf G y ↔ y ∈ orbitOf G x := by {
  constructor
  · intro h
    rw [h]
    use 1
    simp
  · intro ⟨g, hg⟩
    simp only at hg
    subst hg
    ext y
    constructor
    · intro ⟨g', hg'⟩
      simp only at hg'
      subst hg'
      use g' * g⁻¹
      simp only
      rw [← mul_smul]
      group
    · intro ⟨g', hg'⟩
      simp only at hg'
      subst hg'
      use g' * g
      simp [mul_smul]
  }

/- Define the stabilizer of an element `x` as the subgroup of elements
`g ∈ G` that satisfy `g • x = x`. -/
def stabilizerOf (x : X) : Subgroup G where
  carrier := { g | g • x = x }
  mul_mem' := by {
    intro g g' hg hg'
    simp at *
    rw [mul_smul, hg', hg]
  }
  one_mem' := by simp
  inv_mem' := by {
    intro g hg
    simp at *
    nth_rw 1 [← hg]
    simp -- or: `rw [← mul_smul, inv_mul_cancel, one_smul]`
  }

/-
Let's prove the orbit-stabilizer theorem.

Hint: Only define the forward map (as a separate definition),
and use `Equiv.ofBijective` to get an equivalence -/

-- This is a lemma that allows `simp` to simplify `x ≈ y` in the declaration below.
@[simp] theorem leftRel_iff {x y : G} {s : Subgroup G} :
    letI := QuotientGroup.leftRel s; x ≈ y ↔ x⁻¹ * y ∈ s :=
  QuotientGroup.leftRel_apply

def orbit_stabilizer_theorem (x : X) : G ⧸ stabilizerOf G x ≃ orbitOf G x := by {
  let f : G ⧸ stabilizerOf G x → orbitOf G x := by {
    refine Quotient.lift (fun g ↦ ⟨g • x, ?welldefOrbit⟩) ?welldefQuot
    --
    -- `welldefOrbit`: `f` actually maps to an element of the Orbit
    · simp [orbitOf]
    --
    -- `?welldefQuot`: `f` respects the equivalence relation of the quotient
    · intro g g' hgg'
      simp [stabilizerOf, mul_smul] at *
      nth_rw 1 [← hgg']
      rw [← mul_smul, mul_inv_cancel, one_smul] -- or `simp`
  }
  apply Equiv.ofBijective f
  constructor
  · intro g g' hgg'
    induction g using Quotient.ind; rename_i g
    induction g' using Quotient.ind; rename_i g'
    simp [f] at hgg'
    apply Quotient.sound
    simp [stabilizerOf, mul_smul, ← hgg']
  · rintro ⟨x, g, rfl⟩ -- matching against `∀ (b : ↑(orbitOf G x)), ...`
    use ⟦g⟧
    simp [f]
  }


end GroupActions
