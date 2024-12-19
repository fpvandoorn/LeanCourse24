import LeanCourse.Common
import LeanCourse.DiffGeom

open Set ENat Manifold Metric Module Bundle Function
noncomputable section


/-
* There are no exercises in Mathematics in Lean about differential geometry

* You do not need to hand-in any exercises.

* You can solve the exercises below to practice with manifolds in Lean.
  Or work on your project instead.
-/

/-! # Exercises to practice. -/



/-
Partial homeomorphisms are globally defined maps with a globally defined "inverse", but the only
relevant set is the *source*, which should be mapped homeomorphically to the *target*.

Define a partial homeomorphism from `ℝ` to `ℝ` which is just `x ↦ -x`, but on `(-1, 1)`. In
Lean, the interval `(-1, 1)` is denoted by `Ioo (-1 : ℝ) 1` (where `o` stands for _open_). -/

def myFirstLocalHomeo : PartialHomeomorph ℝ ℝ where
  toFun := fun x ↦ -x
  invFun := fun x ↦ -x
  source := Ioo (-1) 1
  target := Ioo (-1) 1
  map_source' := by
    intros x hx
    simp at hx
    simp [hx.1, hx.2, neg_lt (a := x)]
  map_target' := by
    intros x hx
    simp at hx
    simp [hx.1, hx.2, neg_lt (a := x)]
  left_inv' := by simp
  right_inv' := by simp
  open_source := isOpen_Ioo -- `exact?`
  open_target := isOpen_Ioo -- `exact?`
  continuousOn_toFun := continuous_neg.continuousOn -- `exact?`
  continuousOn_invFun := continuous_neg.continuousOn -- `exact?`

/-!
### Smooth functions on `[0, 1]`

We will prove two simple lemmas about smooth maps on `[0, 1]`.
These lemmas are easy, but are still quite some work in Lean,
because Mathlib is missing many lemmas about manifolds.
In particular, don't expect any lemma that is about closed submanifolds.
-/

open unitInterval

def g : I → ℝ := Subtype.val

/- Smoothness results for `EuclideanSpace` are expressed for general `L^p` spaces
(as `EuclideanSpace` has the `L^2` norm), in: -/
#check PiLp.contDiff_coord
#check PiLp.contDiffOn_iff_coord

-- this is the charted space structure on `I`
#check IccManifold

/- You might want to use `contMDiff_iff` and unfold the definition of
`modelWithCornersEuclideanHalfSpace` (and some other functions) in the proof. -/

example : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ g := by {

  rw [contMDiff_iff]
  refine ⟨continuous_subtype_val, fun x y ↦ ?_⟩
  by_cases h : (x : ℝ) < 1
  · simp [g, modelWithCornersEuclideanHalfSpace, h, IccLeftChart, Function.comp_def]
    have : ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin 1) ↦ x 0) := PiLp.contDiff_coord 0
    refine this.contDiffOn.congr (fun z hz ↦ ?_)
    obtain ⟨hz₀, hz₁⟩ : 0 ≤ z 0 ∧ z 0 < 1 := by simpa using hz
    simp [hz₁.le, hz₀]
  · simp [chartAt, h, IccRightChart, Function.comp_def, modelWithCornersEuclideanHalfSpace, g]
    have : ContDiff ℝ ⊤ (fun (x : EuclideanSpace ℝ (Fin 1)) ↦ 1 - x 0) :=
      contDiff_const.sub (PiLp.contDiff_coord 0)
    refine this.contDiffOn.congr (fun z hz ↦ ?_)
    obtain ⟨hz₀, hz₁⟩ : 0 ≤ z 0 ∧ z 0 < 1 := by simpa using hz
    simp [hz₀, hz₁.le]
  }

lemma msmooth_of_smooth {f : ℝ → I} {s : Set ℝ} (h : ContDiffOn ℝ ∞ (fun x ↦ (f x : ℝ)) s) :
  ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞ f s := by {

  rw [contMDiffOn_iff]
  constructor
  · have : Embedding (Subtype.val : I → ℝ) := embedding_subtype_val
    exact (Embedding.continuousOn_iff this).2 h.continuousOn
  simp only [mfld_simps]
  intro y
  by_cases hy : (y : ℝ) < 1
  · simp [chartAt, modelWithCornersEuclideanHalfSpace, Function.comp_def, hy, IccLeftChart,
      PiLp.contDiffOn_iff_coord]
    apply h.mono inter_subset_left
  · simp [chartAt, modelWithCornersEuclideanHalfSpace, Function.comp_def, hy, IccRightChart,
      PiLp.contDiffOn_iff_coord]
    apply (contDiffOn_const.sub h).mono inter_subset_left
  }

/-! # No exercises to hand-in. -/
