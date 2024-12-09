import Mathlib.Geometry.Manifold.Instances.Sphere

/-! Missing bits that should be added to mathlib after cleaning them up -/
open Set BigOperators ENNReal unitInterval

section PiLp_smooth


-- these notations are also declared in Mathlib, but not in a way that the pretty-printer uses them.

/-- The model space used to define `n`-dimensional real manifolds without boundary. -/
scoped[Manifold]
  notation3 (priority := high) "𝓡 " n =>
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)) :
      ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))

/-- The model space used to define `n`-dimensional real manifolds with boundary. -/
scoped[Manifold]
  notation3 (priority := high) "𝓡∂ " n =>
    (modelWithCornersEuclideanHalfSpace n :
      ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n))


variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι : Type*} [Fintype ι]
  {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {α : ι → Type*} {n : WithTop ℕ} (i : ι)
  [∀i, NormedAddCommGroup (α i)] [∀ i, NormedSpace 𝕜 (α i)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma PiLp.norm_coord_le_norm (x : PiLp p α) (i : ι) : ‖x i‖ ≤ ‖x‖ := by
  rcases p.trichotomy with (rfl | rfl | h)
  · exact False.elim (lt_irrefl _ (zero_lt_one.trans_le hp.out))
  · rw [PiLp.norm_eq_ciSup]
    exact le_ciSup (f := fun i ↦ ‖x i‖) (finite_range _).bddAbove i
  · calc ‖x i‖
        ≤ (‖x i‖ ^ p.toReal) ^ (1 / p.toReal) := by
          rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel h.ne', Real.rpow_one]
      _ ≤ ‖x‖ := by
          have A : ∀ j, 0 ≤ ‖x j‖ ^ p.toReal :=
            fun j ↦ Real.rpow_nonneg (norm_nonneg _) _
          simp only [PiLp.norm_eq_sum h, one_mul, LinearMap.coe_mk]
          apply Real.rpow_le_rpow (A i)
          · exact Finset.single_le_sum (fun j _ ↦ A j) (Finset.mem_univ _)
          · exact div_nonneg zero_le_one h.le

lemma PiLp.contDiff_coord :
  ContDiff 𝕜 n (fun x : PiLp p α ↦ x i) :=
let F : PiLp p α →ₗ[𝕜] α i :=
  { toFun := fun x ↦ x i
    map_add' := fun x y ↦ rfl
    map_smul' := fun x c ↦ rfl }
(F.mkContinuous 1 (fun x ↦ by simpa using PiLp.norm_coord_le_norm x i)).contDiff

variable {f : E → PiLp p α} {s : Set E} {x : E}
lemma PiLp.contDiffWithinAt_iff_coord :
  ContDiffWithinAt 𝕜 n f s x ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x ↦ f x i) s x := by
  classical
  constructor
  · intro h i
    have : ContDiff 𝕜 n (fun x : PiLp p α ↦ x i) := PiLp.contDiff_coord i
    exact this.comp_contDiffWithinAt h
  · intro h
    let F : ∀ (i : ι), α i →ₗ[𝕜] PiLp p α := fun i ↦
    { toFun := fun y ↦ Function.update 0 i y
      map_add' := by
        intro y y'
        ext j
        by_cases h : j = i
        · rw [h]; simp
        · simp [h]
      map_smul' := by
        intro c x
        ext j
        by_cases h : j = i
        · rw [h]; simp
        · simp [h] }
    let G : ∀ (i : ι), α i →L[𝕜] PiLp p α := fun i ↦ by
      refine (F i).mkContinuous 1 (fun x ↦ ?_)
      rcases p.trichotomy with (rfl | rfl | h)
      · exact False.elim (lt_irrefl _ (zero_lt_one.trans_le hp.out))
      · haveI : Nonempty ι := ⟨i⟩
        simp only [F, PiLp.norm_eq_ciSup, LinearMap.coe_mk, one_mul]
        refine ciSup_le ?_
        simp only [AddHom.coe_mk, ne_eq]
        intro j
        by_cases hji : j = i
        · rw [hji]; simp [Function.update_same]
        · simp [hji]
      · have : (fun j ↦ ‖Function.update (0 : ∀ i, α i) i x j‖ ^ p.toReal) =
          (fun j ↦ if j = i then ‖x‖ ^ p.toReal else 0) := by
          ext j
          by_cases hji : j = i
          · rw [hji]; simp
          · simp [hji, h.ne']
        simp [F, PiLp.norm_eq_sum h, this, ← Real.rpow_mul, h.ne']
    have : ContDiffWithinAt 𝕜 n (fun x ↦ (∑ i : ι, G i ((f x) i))) s x := by
      refine ContDiffWithinAt.sum (fun i _ ↦ ?_)
      exact (G i).contDiff.comp_contDiffWithinAt (h i)
    convert this with x
    ext j
    simp [G]
    change f x j = (∑ i : ι, Function.update (0 : ∀ i, α i) i (f x i)) j
    rw [Finset.sum_apply]
    have : ∀ i, Function.update (0 : ∀ i, α i) i (f x i) j = (if j = i then f x j else 0) := by
      intro i
      by_cases h : j = i
      · rw [h]; simp
      · simp [h]
    simp [this]

lemma PiLp.contDiffAt_iff_coord :
    ContDiffAt 𝕜 n f x ↔ ∀ i, ContDiffAt 𝕜 n (fun x ↦ f x i) x := by
  simp [← contDiffWithinAt_univ, PiLp.contDiffWithinAt_iff_coord]

lemma PiLp.contDiffOn_iff_coord :
    ContDiffOn 𝕜 n f s ↔ ∀ i, ContDiffOn 𝕜 n (fun x ↦ f x i) s := by
  simp_rw [ContDiffOn, PiLp.contDiffWithinAt_iff_coord]
  tauto

lemma PiLp.contDiff_iff_coord :
    ContDiff 𝕜 n f ↔ ∀ i, ContDiff 𝕜 n (fun x ↦ f x i) := by
  simp [← contDiffOn_univ, PiLp.contDiffOn_iff_coord]

end PiLp_smooth

@[simp]
lemma chartAt_unitInterval (x : I) : chartAt (EuclideanHalfSpace 1) x =
    if (x : ℝ) < 1 then IccLeftChart (0 : ℝ) 1 else IccRightChart 0 1 := by
  rfl
