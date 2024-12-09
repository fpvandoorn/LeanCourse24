import LeanCourse.Common
import LeanCourse.DiffGeom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Set ENat Manifold Metric Module Bundle Function
noncomputable section





/-
# Practical remarks
* Assignment 10 does not require you to hand-in anything.
Work on your project instead.
-/

/- ## Last Week -/

/-
Last time we discussed differential and integral calculus:
* `DifferentiableAt`, `HasDerivAt` and `deriv` are used
  to talk about derivatives of "single-variable" functions.
* `HasFDerivAt` and `fderiv` are used to talk about the
  Fréchet derivative (total derivative) of a function
  whose domain is a normed space.
* We use `∫ x in a..b, f x`, `∫ x in A, f x` or `∫ x, f x`
  for integration. You can add `∂μ` at the end to specify that
  it is integration w.r.t. the measure `μ`.
* `MeasurableSpace` associates a standard σ-algebra to a type.
* Mathlib has standard theorems:
  - intermediate value theorem
  - mean value theorem
  - dominated converge theorem
  - fundamental theorem of calculus
  - change of variable theorem
  - etc.
-/



/- # Today: Differential Geometry -/


/- Ingredient needed for smooth manifolds (glatte Mannigfaltigkeit):
A *partial homeomorphism* from `X → Y` is a homeomorphism
from an open subset `s ⊆ X` to an open subset `t ⊆ Y`. -/

-- An equivalence between a subset of the domain and a subset of the codomain
#check PartialEquiv
-- A homeomorphism between open subsets of the domain and codomain
#check PartialHomeomorph


/- A topological space is locally euclidean if you have a
partial homeomorphism to `ℝⁿ` around each point in `X`. -/
#check ChartedSpace


/- A smooth manifold is `X` an charted space structure
such that for any two charts the coordinate change function
between the charts is smooth on their common domain. -/
variable {n : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  {e e' : PartialHomeomorph M (Fin n → ℝ)}

/- We want to require the following condition for smooth manifolds. -/
#check ContDiffOn ℝ ⊤ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source

/- This is captured by the predicate `HasGroupoid`. -/
#check HasGroupoid

/- We can also equip a manifold with another groupoid structure,
to define the class of `C^k` manifolds or analytic manifolds,
or other classes of manifolds. -/
#check StructureGroupoid



/- Here `contDiffGroupoid` specifies the groupoid structure
on partial homeomorphisms stating that coordinate change functions
must be smooth -/
#check contDiffGroupoid



/- `e.symm ≫ₕ e' : ℝⁿ → ℝⁿ` is the coordinate change function from `e` to `e'`. -/
example [SmoothManifoldWithCorners 𝓘(ℝ, Fin n → ℝ) M]
    {e e' : PartialHomeomorph M (Fin n → ℝ)}
    (he : e ∈ atlas (Fin n → ℝ) M) (he' : e' ∈ atlas (Fin n → ℝ) M) :
    ContDiffOn ℝ ⊤ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
  have := (contDiffGroupoid ⊤ 𝓘(ℝ, Fin n → ℝ)).compatible he he'
  simpa [contDiffPregroupoid] using this.1



/- ## General manifolds -/

/- The general definition of manifolds in mathlib is
more general than this example:
* It can be over any normed field, such as `ℝ`, `ℂ` or the p-adic numbers;
* It can have infinite dimension;
* It can have boundaries or corners. -/



/- To cover manifolds with boundaries and corners,
every manifold `M` is modelled by a *model space* `H`.
There is a map `I : H → E` where `E` is a normed space over a field `𝕜`.

Example: `E = ℝⁿ`, `H` is a half-space, and `I : H → E` is the inclusion.
This map `I` is called a *model with corners*.
`𝓡 n` is notation for the identity map `ℝⁿ → ℝⁿ`.
`𝓡∂ n` is the inclusion from the half-space into `ℝⁿ` -/
#check ModelWithCorners
#check 𝓡 n
#check 𝓡∂ 3

#check SmoothManifoldWithCorners

section examples

section unitInterval
open unitInterval

#check I -- I is notation for the interval [0, 1]

/- The interval [0, 1] is modelled by two charts with model space [0, ∞),
so it is a topological manifold -/
#synth ChartedSpace (EuclideanHalfSpace 1) I

/- To state that it is a smooth manifold, we have to say
that all coordinate changes live in the groupoid of smooth maps -/
#synth HasGroupoid I (contDiffGroupoid ∞ (𝓡∂ 1))

/- This is the same as saying that `I` forms a smooth manifold. -/
#synth SmoothManifoldWithCorners (𝓡∂ 1) I

/- Atlases are not maximal in general, but we can use `maximalAtlas`
to consider a maximal atlas. -/
#check (contDiffGroupoid ∞ (𝓡∂ 1)).maximalAtlas I

end unitInterval



/- The sphere in a finite-dimensional inner product space is a smooth manifold -/

variable (n : ℕ) (E : Type*) [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)]

#synth SmoothManifoldWithCorners (𝓡 n) (sphere (0 : E) 1)

/- The map 𝕊ⁿ ↪ ℝⁿ⁺¹ is smooth -/
example : Smooth (𝓡 n) 𝓘(ℝ, E) ((·) : sphere (0 : E) 1 → E) := by
  exact?

/- The circle is a Lie group -/
example : LieGroup (𝓡 1) Circle := by
  infer_instance



/- Declaring a general smooth manifold is a little verbose. -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners 𝕜 F G)
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N]



/- ## Tangent space & tangent bundle -/

/- A differentiable map between manifolds induces a map on tangent spaces. -/

example (f : M → N) (hf : MDifferentiable I J f) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace J (f x) :=
  mfderiv I J f x

example {f g : M → M} (x : M)
    (hg : MDifferentiableAt I I g (f x)) (hf : MDifferentiableAt I I f x) :
    mfderiv I I (g ∘ f) x = (mfderiv I I g (f x)).comp (mfderiv I I f x) :=
  mfderiv_comp x hg hf



/- It also induces a map on the tangent bundle. -/

example (f : M → N) (hf : MDifferentiable I J f) :
    TangentBundle I M → TangentBundle J N :=
  tangentMap I J f

example (f : M → N) (hf : ContMDiff I J ⊤ f) :
    ContMDiff I.tangent J.tangent ⊤ (tangentMap I J f) :=
  hf.contMDiff_tangentMap le_rfl


example [AddGroup N] [LieAddGroup J N] {f g : M → N} {n : ℕ∞}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) :
    ContMDiff I J n (f + g) :=
  hf.add hg





/- ## Smooth vector bundles -/

/- Given a continuous surjection `π : Z → M`.
A trivialization of `π` at `x : M` with fiber `F`
is a neighborhood `U` of `x` and a homeomorphism
`ϕ : π ⁻¹' U → U × F` that commutes with projections. -/
#check Trivialization

/- Fiber bundles have trivializations around each point in the base manifold -/
#check FiberBundle

/- In vector bundles the trivializations induce linear maps on the fibers.
Interestingly, for infinite-dimensional manifolds
you need an additional continuity condition. -/
#check VectorBundle

/- In smooth vector bundles the trivializations are smooth. -/
#check SmoothVectorBundle







/- Let `E₁` and `E₂` be smooth vector bundles over `M`. -/

variable
  (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  (E₁ : M → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x : M, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [SmoothVectorBundle F₁ E₁ I]
variable
  (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  (E₂ : M → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x : M, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [SmoothVectorBundle F₂ E₂ I]


/- The product of two bundles is a smooth vector bundle. -/

#synth SmoothVectorBundle (F₁ × F₂) (E₁ ×ᵇ E₂) I

/- We can take construct the bundle of continuous linear maps between bundles. -/

variable [∀ x, TopologicalAddGroup (E₁ x)] [∀ x, TopologicalAddGroup (E₂ x)]
  [∀ x, ContinuousSMul 𝕜 (E₂ x)]

#synth SmoothVectorBundle (F₁ →L[𝕜] F₂)
    (Bundle.ContinuousLinearMap (.id 𝕜) E₁ E₂) I

/- We can pull back vector bundles. -/

variable (f : C^∞⟮J, N; I, M⟯)

#synth SmoothVectorBundle F₁ ((f : N → M) *ᵖ E₁) J






/- Patrick Massot, Oliver Nash and I have formalized
a result in differential geometry called *Gromov's h-principle*.

In particular, this allows you to abstractly define an eversion of a sphere. -/

def Immersion (f : M → N) : Prop := ∀ m, Injective (mfderiv I J f m)

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 3)]

local notation "ℝ³" => E
local notation "𝕊²" => sphere (0 : ℝ³) 1

theorem sphere_eversion : ∃ f : ℝ → 𝕊² → ℝ³,
    (ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ³) ∞ (uncurry f)) ∧
    (f 0 = fun x : 𝕊² ↦ (x : ℝ³)) ∧
    (f 1 = fun x : 𝕊² ↦ -(x : ℝ³)) ∧
    ∀ t, Immersion (𝓡 2) 𝓘(ℝ, ℝ³) (f t) :=
  sorry -- not yet in mathlib

end examples
