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
  target := sorry
  map_source' := by
    sorry
  map_target' := by
    sorry
  left_inv' := by
    sorry
  right_inv' := by
    sorry
  open_source := sorry
  open_target := sorry
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry

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
  sorry
  }

lemma msmooth_of_smooth {f : ℝ → I} {s : Set ℝ} (h : ContDiffOn ℝ ∞ (fun x ↦ (f x : ℝ)) s) :
  ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞ f s := by {
  sorry
  }

/-! # No exercises to hand-in. -/
