import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Function.Jacobian
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal
noncomputable section

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 11 & 12.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 10.12.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example (x : ℝ) :
    deriv (fun x ↦ Real.exp (x ^ 2)) x = 2 * x * Real.exp (x ^ 2) := by {
  apply HasDerivAt.deriv
  convert HasDerivAt.exp (hasDerivAt_pow _ _) using 1
  ring
  }

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ∞} in
/- In this exercise you should combine the right lemmas from the library,
in particular `IsBoundedBilinearMap.contDiff`. -/
example (L : E →L[𝕜] E →L[𝕜] E) (f g : E → E) (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun z : E × E ↦ L (f z.1) (g z.2)) := by {
  have : ContDiff 𝕜 n L := by exact ContinuousLinearMap.contDiff L
  apply L.isBoundedBilinearMap.contDiff.comp₂
  exact ContDiff.fst' hf
  exact ContDiff.snd' hg
  }


section

variable (α : Type*)
 [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-
In the next three exercises we will show that every continuous injective function `ℝ → ℝ` is
either strictly monotone or strictly antitone.

We start by proving a slightly harder version of the exercise in class.
We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
Useful lemmas: `uIcc_of_le` and `mem_uIcc`. -/
lemma mono_exercise_part1 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  by_contra h
  push_neg at h
  have : uIcc (f x) (f b) ⊆ f '' uIcc x b :=
    intermediate_value_uIcc hf.continuousOn
  rw [uIcc_of_le (h.le.trans h2ab.le)] at this
  obtain ⟨y, hy, h2y⟩ := this ⟨h.le, h2ab.le⟩
  rw [h2f.eq_iff] at h2y
  subst h2y
  simp [mem_uIcc, *, LE.le.le_iff_eq] at hy
  obtain rfl|rfl := hy <;> apply lt_irrefl _ (by assumption)
  }

/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma mono_exercise_part2 {f : α → α} (hf : Continuous f) (h2f : Injective f)
    {a b : α} (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by {
  intro x hx y hy hxy
  by_contra h
  push_neg at h
  simp at hx hy
  have := intermediate_value_Icc hx hf.continuousOn ⟨mono_exercise_part1 α hf h2f hab h2ab hy, h⟩
  obtain ⟨z, hz, h2z⟩ := this
  rw [h2f.eq_iff] at h2z
  subst h2z
  exact hxy.not_le hz.2
  }

/-
Now we can finish just by using the previous exercise multiple times.
In this proof we take advantage that we did the previous exercise for an arbitrary order,
because that allows us to apply it to `ℝ` with the reversed order `≥`.
This is called `OrderDual ℝ`. This allows us to get that `f` is also strictly monotone on
`(-∞, b]`.
Now finish the proof yourself.
You do not need to apply the intermediate value theorem in this exercise.
-/
lemma mono_exercise_part3 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) :
    StrictMono f ∨ StrictAnti f := by {
  have : ∀ {a b : ℝ} (hab : a ≤ b) (h2ab : f a < f b), StrictMonoOn f (Iic b)
  · intro a b hab h2ab
    have := mono_exercise_part2 (OrderDual ℝ) hf h2f hab h2ab
    rw [strictMonoOn_dual_iff.symm] at this
    exact this
  by_contra h
  simp [not_or, StrictMono, StrictAnti] at h
  obtain ⟨⟨a, b, hab, h2ab⟩, ⟨c, d, hcd, h2cd⟩⟩ := h
  have h3cd : f c < f d := h2cd.lt_of_ne (h2f.ne hcd.ne)
  have h1 : a < c
  · by_contra h
    simp at h
    exact mono_exercise_part2 ℝ hf h2f hcd.le h3cd h (h.trans hab.le) hab |>.not_le h2ab
  have h2 : f c ≤ f a
  · by_contra h
    simp at h
    exact mono_exercise_part2 ℝ hf h2f h1.le h left_mem_Ici hab.le hab |>.not_le h2ab
  exact this hcd.le h3cd (h1.le.trans hcd.le) hcd.le h1 |>.not_le h2
  }

end

/-
Let's prove that the absolute value function is not differentiable at 0.
You can do this by showing that the left derivative and the right derivative do exist,
but are not equal. We can state this with `HasDerivWithinAt`
To make the proof go through, we need to show that the intervals have unique derivatives.
An example of a set that doesn't have unique derivatives is the set `ℝ × {0}`
as a subset of `ℝ × ℝ`, since that set doesn't contains only points in the `x`-axis,
so within that set there is no way to know what the derivative of a function should be
in the direction of the `y`-axis.

The following lemmas will be useful
* `HasDerivWithinAt.congr`
* `uniqueDiffWithinAt_convex`
* `HasDerivWithinAt.derivWithin`
* `DifferentiableAt.derivWithin`.
-/

example : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := by {
  intro h
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0 := by {
    apply (hasDerivWithinAt_id _ _).congr
    · simp
    · simp
    }
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0 := by {
    apply (hasDerivWithinAt_id _ _).neg.congr
    · simp
    · simp
    }
  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by {
    refine uniqueDiffWithinAt_convex ?_ ?_ ?_
    · exact convex_Ici 0
    · simp
    · simp
    }
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by {
    refine uniqueDiffWithinAt_convex ?_ ?_ ?_
    · exact convex_Iic 0
    · simp
    · simp
    }
  have h5 := h.derivWithin h3
  rw [← h.derivWithin h4, h1.derivWithin h3, h2.derivWithin h4] at h5
  norm_num at h5
  }



/- There are special cases of the change of variables theorems for affine transformations
(but you can also use the change of variable theorem from the lecture) -/
example (a b : ℝ) :
    ∫ x in a..b, sin (x / 2 + 3) =
    2 * cos (a / 2 + 3) - 2 * cos (b / 2  + 3) := by {
  rw [intervalIntegral.integral_comp_div_add _ (by norm_num)]
  rw [integral_sin]
  simp
  ring
  }

/- Use the change of variables theorem for this exercise. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, exp x * f (exp x) = ∫ y in exp '' s, f y := by {
  rw [integral_image_eq_integral_abs_deriv_smul hs]
  swap
  intro x hx
  exact (hasDerivAt_exp x).hasDerivWithinAt
  simp
  exact exp_injective.injOn
  }

example (x : ℝ) : ∫ t in (0)..x, t * exp t = (x - 1) * exp x + 1 := by {
  have h1 : ∀ s ∈ [[0, x]], HasDerivAt
    (fun t ↦ (t - 1) * exp t)
    (s * exp s) s
  · intros s hs
    rw [show s * exp s = 1 * exp s + (s - 1) * exp s by ring]
    apply HasDerivAt.mul
    apply HasDerivAt.sub_const
    exact hasDerivAt_id' s
    exact hasDerivAt_exp s
  have h2 : IntervalIntegrable (fun t ↦ t * exp t) volume 0 x
  · apply Continuous.intervalIntegrable
    continuity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h1 h2]
  simp
  }

example (a b : ℝ) : ∫ x in a..b, 2 * x * exp (x ^ 2) =
    exp (b ^ 2) - exp (a ^ 2) := by {
  have h1 : ∀ x ∈ [[a, b]], HasDerivAt
    (fun x ↦ exp (x ^ 2))
    (2 * x * exp (x ^ 2)) x
  · intro x hx
    rw [show 2 * x * exp (x ^ 2) = exp (x ^ 2) * (2 * x) by ring]
    apply HasDerivAt.exp
    convert hasDerivAt_pow 2 x
    simp
  have h2 : IntervalIntegrable (fun x ↦ 2 * x * exp (x ^ 2)) volume a b
  · apply Continuous.intervalIntegrable
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt h1 h2
  }


/-! # Exercises to hand-in. -/

/- This is a copy of `mono_exercise_part1` above. See the comments there for more info. -/
variable (α : Type*) [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] in
lemma mono_exercise_part1_copy {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  by_contra h
  push_neg at h
  have : uIcc (f x) (f b) ⊆ f '' uIcc x b :=
    intermediate_value_uIcc hf.continuousOn
  rw [uIcc_of_le (h.le.trans h2ab.le)] at this
  obtain ⟨y, hy, h2y⟩ := this ⟨h.le, h2ab.le⟩
  rw [h2f.eq_iff] at h2y
  subst h2y
  simp [mem_uIcc, *, LE.le.le_iff_eq] at hy
  obtain rfl|rfl := hy <;> apply lt_irrefl _ (by assumption)
  }


/- Prove the following using the change of variables theorem. -/
lemma change_of_variables_exercise (f : ℝ → ℝ) :
    ∫ x in (0)..π, sin x * f (cos x) = ∫ y in (-1)..1, f y := by {
  rw [intervalIntegral.integral_of_le (by positivity),
      intervalIntegral.integral_of_le (by norm_num)]
  simp only [← integral_Icc_eq_integral_Ioc]
  have : Icc (-1) 1 = cos '' Icc 0 π
  · have := bijOn_cos
    exact Eq.symm (BijOn.image_eq this) -- `exact?`
  rw [this, integral_image_eq_integral_abs_deriv_smul]
  rotate_left
  · exact measurableSet_Icc -- `exact?`
  · intro x hx
    exact (hasDerivAt_cos x).hasDerivWithinAt
  · exact injOn_cos -- `exact?`
  · simp
    apply setIntegral_congr
    · exact measurableSet_Icc
    · intro x hx
      simp
      left
      symm
      simp
      exact sin_nonneg_of_mem_Icc hx
  }
