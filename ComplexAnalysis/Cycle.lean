/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CurveIndex.Continuity

/-!
# Cycles in the complex plane

A cycle is a finite family of closed curves with arbitrary base points. Integrals of one-forms
and indices about a point are summed over the family. Formal integer combinations of closed
curves are represented by repeating and reversing curves, so this is the notion of cycle used
in the homology form of Cauchy's theorem (Conway IV.5, Simon 4.1) without a free abelian group.

## Main definitions

* `Complex.Cycle`: a finite family of closed curves.
* `Complex.Cycle.integral`: the integral of a one-form over a cycle.
* `Complex.Cycle.index`: the index of a cycle about a point.
* `Complex.Cycle.IsC1`: every closed curve of the cycle is `C¹`.

## Main results

* `Complex.Cycle.exists_int_index`: the index is an integer off the cycle.
* `Complex.Cycle.index_eq_zero_of_notMem_ball`: the index vanishes far from the cycle.
* `Complex.Cycle.isOpen_setOf_index_eq`: the index is locally constant off the cycle.
* `Complex.Cycle.exists_norm_integral_le`: a length-type bound for integrals over a cycle.
* `Complex.Cycle.append`, `Complex.Cycle.zsmulLoop`: concatenation of cycles and integer
  multiples of a closed curve, with additivity of integrals and indices.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric Filter
open scoped unitInterval Topology

namespace Complex

/-- A closed curve with an arbitrary base point, packaged with its base point. -/
abbrev Loop := Σ a : ℂ, Path a a

namespace Loop

/-- The loop obtained from a closed path. -/
def ofPath {a : ℂ} (γ : Path a a) : Loop := ⟨a, γ⟩

/-- The reversed loop. -/
def symm (γ : Loop) : Loop := ⟨γ.1, γ.2.symm⟩

/-- Reversal preserves the image. -/
theorem range_symm (γ : Loop) : Set.range γ.symm.2 = Set.range γ.2 := γ.2.symm_range

/-- Reversal preserves `C¹` regularity. -/
theorem contDiffOn_symm {γ : Loop} (hγ : ContDiffOn ℝ 1 γ.2.extend I) :
    ContDiffOn ℝ 1 γ.symm.2.extend I := by
  change ContDiffOn ℝ 1 γ.2.symm.extend I
  rw [Path.extend_symm]
  exact hγ.comp (contDiff_const.sub contDiff_id).contDiffOn
    fun t ht ↦ ⟨by linarith [ht.2], by linarith [ht.1]⟩

end Loop

/-- A cycle: a finite family of closed curves with arbitrary base points. -/
structure Cycle where
  /-- The number of closed curves. -/
  n : ℕ
  /-- The closed curves. -/
  loop : Fin n → Loop

namespace Cycle

variable (Γ : Cycle)

/-- The union of the images of the closed curves of a cycle. -/
def range : Set ℂ := ⋃ i, Set.range (Γ.loop i).2

/-- Every closed curve of the cycle is `C¹`. -/
def IsC1 : Prop := ∀ i, ContDiffOn ℝ 1 (Γ.loop i).2.extend I

/-- The one-form is integrable along every closed curve of the cycle. -/
def Integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ω : ℂ → ℂ →L[ℂ] F) : Prop :=
  ∀ i, CurveIntegrable ω (Γ.loop i).2

/-- The integral of a one-form over a cycle: the sum over its closed curves. -/
def integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ω : ℂ → ℂ →L[ℂ] F) : F :=
  ∑ i, curveIntegral ω (Γ.loop i).2

/-- The index of a cycle about a point: the sum of the indices of its closed curves. -/
def index (w : ℂ) : ℂ := ∑ i, curveIndex (Γ.loop i).2 w

/-- Every point on a constituent loop belongs to the range of the cycle. -/
theorem loop_mem_range (i : Fin Γ.n) (t : I) : (Γ.loop i).2 t ∈ Γ.range :=
  mem_iUnion.mpr ⟨i, t, rfl⟩

/-- The real-parameter extension of a constituent loop takes its values in the range of the
cycle. -/
theorem loop_extend_mem_range (i : Fin Γ.n) (t : ℝ) : (Γ.loop i).2.extend t ∈ Γ.range :=
  mem_iUnion.mpr ⟨i, (Γ.loop i).2.extend_range ▸ mem_range_self t⟩

/-- The range of a cycle lies in a set exactly when every constituent loop lies in that set. -/
theorem range_subset_iff {U : Set ℂ} : Γ.range ⊆ U ↔ ∀ i (t : I), (Γ.loop i).2 t ∈ U := by
  simp only [range, iUnion_subset_iff, Set.range_subset_iff]

/-- Each constituent loop avoids every point outside the range of the cycle. -/
theorem loop_ne_of_notMem_range {w : ℂ} (hw : w ∉ Γ.range) (i : Fin Γ.n) (t : I) :
    (Γ.loop i).2 t ≠ w :=
  fun h ↦ hw (h ▸ Γ.loop_mem_range i t)

/-- The range of a finite cycle of continuous loops is compact. -/
theorem isCompact_range : IsCompact Γ.range :=
  isCompact_iUnion fun i ↦ _root_.isCompact_range (Γ.loop i).2.continuous

/-- The range of a finite cycle of continuous loops is closed. -/
theorem isClosed_range : IsClosed Γ.range := Γ.isCompact_range.isClosed

/-- The range of a finite cycle of continuous loops is bounded. -/
theorem isBounded_range : Bornology.IsBounded Γ.range := Γ.isCompact_range.isBounded

/-- The complement of the range of a cycle is open. -/
theorem isOpen_compl_range : IsOpen Γ.rangeᶜ := Γ.isClosed_range.isOpen_compl

/-- The image of each constituent loop is contained in the range of the cycle. -/
theorem range_loop_subset (i : Fin Γ.n) : Set.range (Γ.loop i).2 ⊆ Γ.range :=
  subset_iUnion (fun i ↦ Set.range (Γ.loop i).2) i

section Index

/-- The index of a `C¹` cycle about a point off the cycle is an integer. -/
theorem exists_int_index (hΓ : Γ.IsC1) {w : ℂ} (hw : w ∉ Γ.range) :
    ∃ n : ℤ, Γ.index w = n := by
  have h : ∀ i, ∃ n : ℤ, curveIndex (Γ.loop i).2 w = n := fun i ↦
    exists_int_curveIndex _ (hΓ i) (Γ.loop_ne_of_notMem_range hw i)
  choose n hn using h
  exact ⟨∑ i, n i, by simp [index, hn]⟩

/-- A cycle contained in a ball has index zero about every point outside that ball. -/
theorem index_eq_zero_of_notMem_ball (hΓ : Γ.IsC1) {c w : ℂ} {R : ℝ}
    (hball : Γ.range ⊆ ball c R) (hw : w ∉ ball c R) : Γ.index w = 0 :=
  Finset.sum_eq_zero fun i _ ↦ curveIndex_eq_zero_of_notMem_ball _ (hΓ i)
    (fun t ↦ hball (Γ.loop_mem_range i t)) hw

/-- The index of a `C¹` cycle vanishes outside some ball around any given center. -/
theorem exists_pos_index_eq_zero_outside_ball (hΓ : Γ.IsC1) (c : ℂ) :
    ∃ R > 0, Γ.range ⊆ ball c R ∧ ∀ w, w ∉ ball c R → Γ.index w = 0 := by
  obtain ⟨R, hR, hball⟩ := Γ.isBounded_range.subset_ball_lt 0 c
  exact ⟨R, hR, hball, fun w hw ↦ Γ.index_eq_zero_of_notMem_ball hΓ hball hw⟩

/-- The index of a `C¹` cycle is continuous off the cycle. -/
theorem continuousOn_index (hΓ : Γ.IsC1) : ContinuousOn Γ.index Γ.rangeᶜ :=
  continuousOn_finsetSum _ fun i _ ↦ (continuousOn_curveIndex _ (hΓ i)).mono
    (compl_subset_compl.mpr (Γ.range_loop_subset i))

/-- The index of a `C¹` cycle is constant on preconnected sets off the cycle. -/
theorem index_eq_of_isPreconnected (hΓ : Γ.IsC1) {U : Set ℂ} (hU : IsPreconnected U)
    (hUΓ : U ⊆ Γ.rangeᶜ) {v w : ℂ} (hv : v ∈ U) (hw : w ∈ U) :
    Γ.index v = Γ.index w :=
  Finset.sum_congr rfl fun i _ ↦ curveIndex_eq_of_isPreconnected _ (hΓ i) hU
    (hUΓ.trans (compl_subset_compl.mpr (Γ.range_loop_subset i))) hv hw

/-- The index of a `C¹` cycle is constant on a ball around any point off the cycle. -/
theorem exists_ball_index_eq (hΓ : Γ.IsC1) {w : ℂ} (hw : w ∉ Γ.range) :
    ∃ r > 0, ball w r ⊆ Γ.rangeᶜ ∧ ∀ z ∈ ball w r, Γ.index z = Γ.index w := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Γ.isOpen_compl_range w hw
  exact ⟨r, hr, hball, fun z hz ↦ Γ.index_eq_of_isPreconnected hΓ
    (convex_ball w r).isPreconnected hball hz (mem_ball_self hr)⟩

/-- The level sets of the index of a `C¹` cycle off the cycle are open. -/
theorem isOpen_setOf_index_eq (hΓ : Γ.IsC1) (c : ℂ) :
    IsOpen {w | w ∉ Γ.range ∧ Γ.index w = c} := by
  rw [Metric.isOpen_iff]
  rintro w ⟨hw, hc⟩
  obtain ⟨r, hr, hball, heq⟩ := Γ.exists_ball_index_eq hΓ hw
  exact ⟨r, hr, fun z hz ↦ ⟨hball hz, (heq z hz).trans hc⟩⟩

end Index

section Integral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Cauchy kernel integral over a cycle is `2πi` times the index. -/
theorem integral_sub_inv_eq_two_pi_I_mul_index (w : ℂ) :
    Γ.integral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) =
      (2 * (Real.pi : ℂ) * Complex.I) * Γ.index w := by
  simp only [integral, index, curveIntegral_sub_inv_eq_two_pi_I_mul_curveIndex, Finset.mul_sum]

/-- A one-form continuous on a set containing a `C¹` cycle is integrable over the cycle. -/
theorem integrable_of_continuousOn (hΓ : Γ.IsC1) {U : Set ℂ} {ω : ℂ → ℂ →L[ℂ] F}
    (hω : ContinuousOn ω U) (hΓU : Γ.range ⊆ U) : Γ.Integrable ω :=
  fun i ↦ hω.curveIntegrable_of_contDiffOn (hΓ i) fun t ↦ hΓU (Γ.loop_mem_range i t)

/-- A continuous Banach-valued function gives an integrable one-form over a `C¹` cycle. -/
theorem integrable_toSpanSingleton_of_continuousOn (hΓ : Γ.IsC1) {U : Set ℂ} {f : ℂ → F}
    (hf : ContinuousOn f U) (hΓU : Γ.range ⊆ U) :
    Γ.Integrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) :=
  Γ.integrable_of_continuousOn hΓ
    ((ContinuousLinearMap.toSpanSingletonLIE ℂ F).continuous.comp_continuousOn hf) hΓU

/-- The integral over a cycle is additive for forms integrable along its constituent loops. -/
theorem integral_add {ω₁ ω₂ : ℂ → ℂ →L[ℂ] F} (h₁ : Γ.Integrable ω₁) (h₂ : Γ.Integrable ω₂) :
    Γ.integral (ω₁ + ω₂) = Γ.integral ω₁ + Γ.integral ω₂ := by
  simp only [integral, curveIntegral_add (h₁ _) (h₂ _), Finset.sum_add_distrib]

/-- The integral over a cycle respects subtraction of integrable forms. -/
theorem integral_sub {ω₁ ω₂ : ℂ → ℂ →L[ℂ] F} (h₁ : Γ.Integrable ω₁) (h₂ : Γ.Integrable ω₂) :
    Γ.integral (ω₁ - ω₂) = Γ.integral ω₁ - Γ.integral ω₂ := by
  simp only [integral, curveIntegral_sub (h₁ _) (h₂ _), Finset.sum_sub_distrib]

/-- Multiplication of a form by a complex scalar commutes with integration over a cycle. -/
theorem integral_smul (c : ℂ) (ω : ℂ → ℂ →L[ℂ] F) :
    Γ.integral (c • ω) = c • Γ.integral ω := by
  simp only [integral, curveIntegral_smul, Finset.smul_sum]

/-- Integrals over a cycle only depend on the one-form on the cycle. -/
theorem integral_congr {ω₁ ω₂ : ℂ → ℂ →L[ℂ] F} (h : EqOn ω₁ ω₂ Γ.range) :
    Γ.integral ω₁ = Γ.integral ω₂ := by
  unfold integral
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [curveIntegral_def]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [curveIntegralFun_def, h (Γ.loop_extend_mem_range i t)]

/-- A constant Banach-valued factor can be taken outside a scalar integral over a cycle. -/
theorem integral_smul_const [CompleteSpace F] {g : ℂ → ℂ} (v : F)
    (hint : Γ.Integrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (g z))) :
    Γ.integral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (g z • v)) =
      Γ.integral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (g z)) • v := by
  simp only [integral, curveIntegral_smul_const v (hint _), Finset.sum_smul]

/-- A length-type constant for a `C¹` cycle: integrals of functions bounded on the cycle are
bounded by the constant times the bound. -/
theorem exists_norm_integral_le (hΓ : Γ.IsC1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (f : ℂ → F) (M : ℝ), (∀ z ∈ Γ.range, ‖f z‖ ≤ M) →
      ‖Γ.integral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z))‖ ≤ L * M := by
  have hloop : ∀ i, ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ I, ‖derivWithin (Γ.loop i).2.extend I t‖ ≤ L := by
    intro i
    obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hΓ i).continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl)
    exact ⟨max L 0, le_max_right _ _, fun t ht ↦ (hL t ht).trans (le_max_left _ _)⟩
  choose L hL0 hL using hloop
  refine ⟨∑ i, L i, Finset.sum_nonneg fun i _ ↦ hL0 i, fun f M hM ↦ ?_⟩
  calc ‖Γ.integral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z))‖
      ≤ ∑ i, ‖curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (Γ.loop i).2‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, L i * M := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [curveIntegral_def]
        have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
            ‖curveIntegralFun (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z))
              (Γ.loop i).2 t‖ ≤ L i * M := by
          intro t ht
          rw [uIoc_of_le zero_le_one] at ht
          rw [curveIntegralFun_def, ContinuousLinearMap.toSpanSingleton_apply, norm_smul]
          exact mul_le_mul (hL i t (Ioc_subset_Icc_self ht))
            (hM _ (Γ.loop_extend_mem_range i t)) (norm_nonneg _) (hL0 i)
        simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ = (∑ i, L i) * M := by rw [Finset.sum_mul]

end Integral

section Algebra

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The cycle consisting of a single closed curve. -/
def single (γ : Loop) : Cycle := ⟨1, fun _ ↦ γ⟩

/-- The cycle consisting of `k` copies of a closed curve. -/
def replicate (k : ℕ) (γ : Loop) : Cycle := ⟨k, fun _ ↦ γ⟩

/-- The concatenation of two cycles as families of closed curves. -/
def append (Γ₁ Γ₂ : Cycle) : Cycle := ⟨Γ₁.n + Γ₂.n, Fin.append Γ₁.loop Γ₂.loop⟩

/-- A closed curve or its reverse, according to the sign of an integer. -/
def _root_.Complex.Loop.zsign (m : ℤ) (γ : Loop) : Loop := if 0 ≤ m then γ else γ.symm

/-- A nonnegative signed multiplicity preserves the orientation of the loop. -/
theorem _root_.Complex.Loop.zsign_of_nonneg {m : ℤ} (hm : 0 ≤ m) (γ : Loop) :
    Loop.zsign m γ = γ := by
  simp [Loop.zsign, hm]

/-- A negative signed multiplicity reverses the orientation of the loop. -/
theorem _root_.Complex.Loop.zsign_of_neg {m : ℤ} (hm : m < 0) (γ : Loop) :
    Loop.zsign m γ = γ.symm := by
  simp [Loop.zsign, not_le.mpr hm]

/-- The cycle consisting of `m` copies of a closed curve, reversed when `m` is negative. -/
def zsmulLoop (m : ℤ) (γ : Loop) : Cycle := replicate m.natAbs (Loop.zsign m γ)

/-- Replicating a loop does not enlarge its image. -/
theorem replicate_range_subset (k : ℕ) (γ : Loop) :
    (replicate k γ).range ⊆ Set.range γ.2 :=
  iUnion_subset fun _ ↦ subset_rfl

/-- Replicating a `C¹` loop gives a `C¹` cycle. -/
theorem replicate_isC1 (k : ℕ) {γ : Loop} (hγ : ContDiffOn ℝ 1 γ.2.extend I) :
    (replicate k γ).IsC1 :=
  fun _ ↦ hγ

/-- The integral over a cycle of `k` copies of a loop is `k` times the loop integral. -/
theorem replicate_integral (k : ℕ) (γ : Loop) (ω : ℂ → ℂ →L[ℂ] F) :
    (replicate k γ).integral ω = k • curveIntegral ω γ.2 := by
  change ∑ _i : Fin k, curveIntegral ω γ.2 = k • curveIntegral ω γ.2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- The index of a cycle of `k` copies of a loop is `k` times the loop index. -/
theorem replicate_index (k : ℕ) (γ : Loop) (w : ℂ) :
    (replicate k γ).index w = k * curveIndex γ.2 w := by
  change ∑ _i : Fin k, curveIndex γ.2 w = k * curveIndex γ.2 w
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The first block of loops in an appended cycle is the first constituent cycle. -/
theorem append_loop_castAdd (Γ₁ Γ₂ : Cycle) (i : Fin Γ₁.n) :
    (Γ₁.append Γ₂).loop (Fin.castAdd Γ₂.n i) = Γ₁.loop i :=
  Fin.append_left _ _ _

/-- The second block of loops in an appended cycle is the second constituent cycle. -/
theorem append_loop_natAdd (Γ₁ Γ₂ : Cycle) (i : Fin Γ₂.n) :
    (Γ₁.append Γ₂).loop (Fin.natAdd Γ₁.n i) = Γ₂.loop i :=
  Fin.append_right _ _ _

/-- The range of an appended cycle is the union of the two constituent ranges. -/
theorem append_range (Γ₁ Γ₂ : Cycle) : (Γ₁.append Γ₂).range = Γ₁.range ∪ Γ₂.range := by
  ext z
  simp only [range, mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, t, ht⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, t, Γ₁.append_loop_castAdd Γ₂ i ▸ ht⟩
    | right i => exact Or.inr ⟨i, t, Γ₁.append_loop_natAdd Γ₂ i ▸ ht⟩
  · rintro (⟨i, t, ht⟩ | ⟨i, t, ht⟩)
    · exact ⟨Fin.castAdd _ i, t, (Γ₁.append_loop_castAdd Γ₂ i).symm ▸ ht⟩
    · exact ⟨Fin.natAdd _ i, t, (Γ₁.append_loop_natAdd Γ₂ i).symm ▸ ht⟩

/-- Appending two `C¹` cycles gives a `C¹` cycle. -/
theorem append_isC1 {Γ₁ Γ₂ : Cycle} (h₁ : Γ₁.IsC1) (h₂ : Γ₂.IsC1) : (Γ₁.append Γ₂).IsC1 := by
  intro i
  induction i using Fin.addCases with
  | left i => exact (Γ₁.append_loop_castAdd Γ₂ i).symm ▸ h₁ i
  | right i => exact (Γ₁.append_loop_natAdd Γ₂ i).symm ▸ h₂ i

/-- The integral over an appended cycle is the sum of the two cycle integrals. -/
theorem append_integral (Γ₁ Γ₂ : Cycle) (ω : ℂ → ℂ →L[ℂ] F) :
    (Γ₁.append Γ₂).integral ω = Γ₁.integral ω + Γ₂.integral ω := by
  change ∑ i : Fin (Γ₁.n + Γ₂.n), curveIntegral ω ((Γ₁.append Γ₂).loop i).2 = _
  rw [Fin.sum_univ_add]
  unfold integral
  congr 1
  · exact Finset.sum_congr rfl fun i _ ↦ by rw [append_loop_castAdd]
  · exact Finset.sum_congr rfl fun i _ ↦ by rw [append_loop_natAdd]

/-- The index of an appended cycle is the sum of the two cycle indices. -/
theorem append_index (Γ₁ Γ₂ : Cycle) (w : ℂ) :
    (Γ₁.append Γ₂).index w = Γ₁.index w + Γ₂.index w := by
  change ∑ i : Fin (Γ₁.n + Γ₂.n), curveIndex ((Γ₁.append Γ₂).loop i).2 w = _
  rw [Fin.sum_univ_add]
  unfold index
  congr 1
  · exact Finset.sum_congr rfl fun i _ ↦ by rw [append_loop_castAdd]
  · exact Finset.sum_congr rfl fun i _ ↦ by rw [append_loop_natAdd]

/-- Replication with an integer multiplicity, including orientation reversal, does not enlarge the
loop image. -/
theorem zsmulLoop_range_subset (m : ℤ) (γ : Loop) :
    (zsmulLoop m γ).range ⊆ Set.range γ.2 := by
  refine (replicate_range_subset _ _).trans ?_
  rcases le_or_gt 0 m with hm | hm
  · rw [Loop.zsign_of_nonneg hm]
  · rw [Loop.zsign_of_neg hm, Loop.range_symm]

/-- Replication with an integer multiplicity preserves `C¹` regularity. -/
theorem zsmulLoop_isC1 (m : ℤ) {γ : Loop} (hγ : ContDiffOn ℝ 1 γ.2.extend I) :
    (zsmulLoop m γ).IsC1 := by
  unfold zsmulLoop
  rcases le_or_gt 0 m with hm | hm
  · rw [Loop.zsign_of_nonneg hm]
    exact replicate_isC1 _ hγ
  · rw [Loop.zsign_of_neg hm]
    exact replicate_isC1 _ (Loop.contDiffOn_symm hγ)

/-- The integral over a loop with integer multiplicity is that integer times the loop integral. -/
theorem zsmulLoop_integral (m : ℤ) (γ : Loop) (ω : ℂ → ℂ →L[ℂ] F) :
    (zsmulLoop m γ).integral ω = m • curveIntegral ω γ.2 := by
  unfold zsmulLoop
  rw [replicate_integral]
  rcases le_or_gt 0 m with hm | hm
  · rw [Loop.zsign_of_nonneg hm, ← natCast_zsmul, Int.natAbs_of_nonneg hm]
  · rw [Loop.zsign_of_neg hm]
    change m.natAbs • curveIntegral ω γ.2.symm = _
    rw [curveIntegral_symm, ← natCast_zsmul, Int.ofNat_natAbs_of_nonpos hm.le, neg_zsmul,
      smul_neg, neg_neg]

/-- The index of a loop with integer multiplicity is that integer times the loop index. -/
theorem zsmulLoop_index (m : ℤ) (γ : Loop) (w : ℂ) :
    (zsmulLoop m γ).index w = m * curveIndex γ.2 w := by
  unfold zsmulLoop
  rw [replicate_index]
  rcases le_or_gt 0 m with hm | hm
  · rw [Loop.zsign_of_nonneg hm, ← Int.cast_natCast, Int.natAbs_of_nonneg hm]
  · rw [Loop.zsign_of_neg hm]
    change (m.natAbs : ℂ) * curveIndex γ.2.symm w = _
    rw [curveIndex_symm, ← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hm.le, Int.cast_neg,
      neg_mul, mul_neg, neg_neg]

end Algebra

end Cycle

end Complex

end
