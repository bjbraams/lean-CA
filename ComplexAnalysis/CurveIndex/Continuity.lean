/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CurveIndex
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Dependence of the curve index on the pole

The analytic index of a closed `C¹` curve is continuous, and hence locally constant,
on the complement of its image. In particular, moving the pole within a connected
region avoiding the curve does not change the index.
The index also vanishes outside a sufficiently large ball, and consequently on every
unbounded connected component of the complement. These facts do not require simplicity
of the curve or any Jordan separation theorem.

## Main results

* `Complex.continuousOn_curveIndex`: The index of a closed `C¹` curve depends continuously on
  the pole away from its image.
* `Complex.curveIndex_eq_zero_of_notMem_ball`: A closed `C¹` curve contained in a ball has index
  zero about every point outside that ball.
* `Complex.exists_pos_curveIndex_eq_zero_outside_ball`: The index of a closed `C¹` curve
  vanishes outside some ball about any prescribed center.
* `Complex.curveIndex_eq_zero_of_isPreconnected_of_not_isBounded`: The index vanishes on every
  unbounded preconnected set disjoint from the curve.
* `Complex.curveIndex_eq_zero_of_not_isBounded_connectedComponentIn`: The index is zero on any
  unbounded connected component of the complement of the curve.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology unitInterval

namespace Complex

/-- The index of a closed `C¹` curve depends continuously on the pole away from its image. -/
theorem continuousOn_curveIndex {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend I) :
    ContinuousOn (curveIndex γ) (range γ)ᶜ := by
  let U := (range γ)ᶜ
  have hU : IsOpen U := (isCompact_range γ.continuous).isClosed.isOpen_compl
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let D : ℝ → ℂ := fun t => derivWithin γ.extend I (projIcc 0 1 zero_le_one t)
  have hD : Continuous D :=
    (continuousOn_iff_continuous_domRestrict.mp
      (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl)).comp continuous_projIcc
  let K : U → ℝ → ℂ := fun w t => (γ.extend t - w)⁻¹ * D t
  have hK : Continuous K.uncurry := by
    apply Continuous.mul
    · apply Continuous.inv₀
      · exact (γ.continuous_extend.comp continuous_snd).sub
          (continuous_subtype_val.comp continuous_fst)
      · intro p
        apply sub_ne_zero.mpr
        intro he
        exact p.1.property ⟨projIcc 0 1 zero_le_one p.2, he⟩
    · exact hD.comp continuous_snd
  have hc := continuous_parametric_integral_of_continuous hK isCompact_Icc
    (μ := volume) (s := I)
  have he (w : U) : curveIndex γ w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in I, K w t := by
    rw [curveIndex, curveIntegral_def, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    simp only [curveIntegralFun_def, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, K, D, projIcc_of_mem zero_le_one ht, mul_comm]
  exact continuousOn_iff_continuous_domRestrict.mpr
    ((continuous_const.mul hc).congr (fun w => (he w).symm))

/-- The index is locally constant on the complement of a closed `C¹` curve. -/
theorem isLocallyConstant_curveIndex {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend I) :
    IsLocallyConstant (fun w : ((range γ)ᶜ : Set ℂ) => curveIndex γ w) := by
  let T := range ((↑) : ℤ → ℂ)
  let : DiscreteTopology T :=
    isDiscrete_iff_discreteTopology.mp isClosedEmbedding_intCast.isEmbedding.isDiscrete_range
  let f : ((range γ)ᶜ : Set ℂ) → T := fun w => ⟨curveIndex γ w, by
    obtain ⟨n, hn⟩ := exists_int_curveIndex γ hγ (fun t ht => w.property ⟨t, ht⟩)
    exact ⟨n, hn.symm⟩⟩
  have hf : Continuous f :=
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_curveIndex γ hγ)).subtype_mk _
  exact ((IsLocallyConstant.iff_continuous f).mpr hf).comp Subtype.val

/-- Moving the pole in a preconnected set disjoint from the curve preserves the index.
The set need not be open or path connected. -/
theorem curveIndex_eq_of_isPreconnected {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend I) {U : Set ℂ} (hU : IsPreconnected U)
    (hUγ : U ⊆ (range γ)ᶜ) {v w : ℂ} (hv : v ∈ U) (hw : w ∈ U) :
    curveIndex γ v = curveIndex γ w := by
  apply hU.constant_of_mapsTo isClosedEmbedding_intCast.isEmbedding.isDiscrete_range
    ((continuousOn_curveIndex γ hγ).mono hUγ) _ hv hw
  intro z hz
  obtain ⟨n, hn⟩ := exists_int_curveIndex γ hγ (fun t ht => hUγ hz ⟨t, ht⟩)
  exact ⟨n, hn.symm⟩

/-- Every pole off a closed `C¹` curve has a disk avoiding the curve on which the index
is constant. This gives an ambient-plane version of local constancy. -/
theorem exists_ball_curveIndex_eq {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend I) {w : ℂ} (hw : w ∉ range γ) :
    ∃ r > 0, ball w r ⊆ (range γ)ᶜ ∧
      ∀ z ∈ ball w r, curveIndex γ z = curveIndex γ w := by
  have hU := (isCompact_range γ.continuous).isClosed.isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU w hw
  exact ⟨r, hr, hball, fun z hz => curveIndex_eq_of_isPreconnected γ hγ
    (convex_ball w r).isPreconnected hball hz (mem_ball_self hr)⟩

/-- The index is constant on each connected component of the complement of the curve. -/
theorem curveIndex_eq_of_mem_connectedComponentIn {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend I) {v w : ℂ} (hv : v ∉ range γ)
    (hw : w ∈ connectedComponentIn (range γ)ᶜ v) :
    curveIndex γ w = curveIndex γ v :=
  curveIndex_eq_of_isPreconnected γ hγ isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _) hw (mem_connectedComponentIn hv)

/-- A closed `C¹` curve contained in a ball has index zero about every point outside that ball. -/
theorem curveIndex_eq_zero_of_notMem_ball {a c w : ℂ} {R : ℝ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hball : ∀ t, γ t ∈ ball c R)
    (hw : w ∉ ball c R) : curveIndex γ w = 0 := by
  have hf : DifferentiableOn ℂ (fun z => (z - w)⁻¹) (ball c R) :=
    (differentiableOn_id.sub_const w).inv
      (fun z hz => sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw))
  rw [curveIndex, curveIntegral_eq_zero_of_differentiableOn_convex
    isOpen_ball (convex_ball c R) hf hγ hball, mul_zero]

/-- The index of a closed `C¹` curve vanishes outside some ball about any prescribed center. -/
theorem exists_pos_curveIndex_eq_zero_outside_ball {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (c : ℂ) :
    ∃ R > 0, ∀ w, w ∉ ball c R → curveIndex γ w = 0 := by
  obtain ⟨R, hR, hball⟩ := (isCompact_range γ.continuous).isBounded.subset_ball_lt 0 c
  exact ⟨R, hR, fun w hw => curveIndex_eq_zero_of_notMem_ball γ hγ
    (fun t => hball ⟨t, rfl⟩) hw⟩

/-- The index vanishes on every unbounded preconnected set disjoint from the curve. -/
theorem curveIndex_eq_zero_of_isPreconnected_of_not_isBounded {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend I) {U : Set ℂ} (hU : IsPreconnected U)
    (hUγ : U ⊆ (range γ)ᶜ) (hUb : ¬ Bornology.IsBounded U) {w : ℂ} (hw : w ∈ U) :
    curveIndex γ w = 0 := by
  obtain ⟨R, _, hR⟩ := exists_pos_curveIndex_eq_zero_outside_ball γ hγ 0
  obtain ⟨z, hz, hzR⟩ : ∃ z ∈ U, z ∉ ball (0 : ℂ) R := by
    by_contra! h
    exact hUb (isBounded_ball.subset h)
  rw [curveIndex_eq_of_isPreconnected γ hγ hU hUγ hw hz]
  exact hR z hzR

/-- The index is zero on any unbounded connected component of the complement of the curve. -/
theorem curveIndex_eq_zero_of_not_isBounded_connectedComponentIn {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend I) {w : ℂ} (hw : w ∉ range γ)
    (hUb : ¬ Bornology.IsBounded (connectedComponentIn (range γ)ᶜ w)) :
    curveIndex γ w = 0 :=
  curveIndex_eq_zero_of_isPreconnected_of_not_isBounded γ hγ
    isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) hUb
    (mem_connectedComponentIn hw)

end Complex
