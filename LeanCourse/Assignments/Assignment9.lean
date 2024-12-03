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
  sorry
  }

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ∞} in
/- In this exercise you should combine the right lemmas from the library,
in particular `IsBoundedBilinearMap.contDiff`. -/
example (L : E →L[𝕜] E →L[𝕜] E) (f g : E → E) (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun z : E × E ↦ L (f z.1) (g z.2)) := by {
  sorry
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
  sorry
  }

/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma mono_exercise_part2 {f : α → α} (hf : Continuous f) (h2f : Injective f)
    {a b : α} (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by {
  sorry
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
  -- sorry
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
    sorry
    }
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0 := by {
    sorry
    }
  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by {
  sorry
  }
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by {
  sorry
  }
  -- sorry
  have h5 := h.derivWithin h3
  rw [← h.derivWithin h4, h1.derivWithin h3, h2.derivWithin h4] at h5
  norm_num at h5
  }



/- There are special cases of the change of variables theorems for affine transformations
(but you can also use the change of variable theorem from the lecture) -/
example (a b : ℝ) :
    ∫ x in a..b, sin (x / 2 + 3) =
    2 * cos (a / 2 + 3) - 2 * cos (b / 2  + 3) := by {
  sorry
  }

/- Use the change of variables theorem for this exercise. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, exp x * f (exp x) = ∫ y in exp '' s, f y := by {
  sorry
  }

example (x : ℝ) : ∫ t in (0)..x, t * exp t = (x - 1) * exp x + 1 := by {
  sorry
  }

example (a b : ℝ) : ∫ x in a..b, 2 * x * exp (x ^ 2) =
    exp (b ^ 2) - exp (a ^ 2) := by {
  sorry
  }


/-! # Exercises to hand-in. -/

/- This is a copy of `mono_exercise_part1` above. See the comments there for more info. -/
variable (α : Type*) [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] in
lemma mono_exercise_part1_copy {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  sorry
  }


/- Prove the following using the change of variables theorem. -/
lemma change_of_variables_exercise (f : ℝ → ℝ) :
    ∫ x in (0)..π, sin x * f (cos x) = ∫ y in (-1)..1, f y := by {
  sorry
  }
