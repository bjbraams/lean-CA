/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CauchyFormula
public import ComplexAnalysis.LogDerivIntegral
public import ComplexAnalysis.Integral.CirclePath

/-!
# The analytic index of a closed complex curve

The index is the Cauchy-kernel integral divided by `2πi`. It is complex-valued by
definition, and integer-valued for closed `C¹` curves avoiding the pole. This analytic
definition uses Mathlib's totalized curve integral; no properties are asserted here for
arbitrary continuous curves without the stated regularity and integrability hypotheses.

We prove reversal and concatenation laws, vanishing on simply connected domains avoiding
the pole, normalization for circles, and the index form of the Banach-valued Cauchy formula.
This does not identify an interior or an orientation for an arbitrary Jordan curve.

## Main results

* `Complex.exists_int_curveIndex`: The index of a closed `C¹` curve avoiding its pole is an
  integer.
* `Complex.curveIndex_eq_zero_of_isSimplyConnected`: A closed `C¹` curve has index zero about
  any point excluded from a simply connected open domain containing the curve.
* `Complex.curveIndex_circle_of_mem_ball`: A counterclockwise circle has index one about each
  point in its open disk.
* `Complex.curveIndex_circle_of_notMem_closedBall`: A circle of nonnegative radius has index
  zero about every point outside its closed disk. The statement includes the degenerate circle
  of radius zero.
* `Complex.two_pi_I_inv_smul_curveIntegral_sub_inv_smul_eq_curveIndex_smul`: The Banach-valued
  Cauchy formula on a simply connected open domain, weighted by the index of the curve about the
  evaluation point.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set MeasureTheory Metric
open scoped unitInterval

namespace Complex

/-- The analytic index of a closed curve about a point, defined by the normalized
Cauchy-kernel integral. Integer-valuedness requires regularity and avoidance hypotheses. -/
@[expose] def curveIndex {a : ℂ} (γ : Path a a) (w : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ

/-- Recover the Cauchy-kernel integral from the curve index. -/
theorem curveIntegral_sub_inv_eq_two_pi_I_mul_curveIndex {a : ℂ} (γ : Path a a) (w : ℂ) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ =
      (2 * (Real.pi : ℂ) * Complex.I) * curveIndex γ w := by
  rw [curveIndex, ← mul_assoc, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]

/-- The index of a closed `C¹` curve avoiding its pole is an integer. -/
theorem exists_int_curveIndex {a w : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hw : ∀ t, γ t ≠ w) :
    ∃ n : ℤ, curveIndex γ w = (n : ℂ) := by
  obtain ⟨n, hn⟩ := exists_int_curveIntegral_sub_inv γ hγ hw
  refine ⟨n, ?_⟩
  rw [curveIndex, hn, mul_comm (n : ℂ), ← mul_assoc,
    inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

/-- A constant loop has index zero. -/
@[simp] theorem curveIndex_refl (a w : ℂ) : curveIndex (Path.refl a) w = 0 := by
  simp [curveIndex, curveIntegral_refl]

/-- Reversing a loop negates its index. -/
@[simp] theorem curveIndex_symm {a : ℂ} (γ : Path a a) (w : ℂ) :
    curveIndex γ.symm w = -curveIndex γ w := by
  simp [curveIndex, curveIntegral_symm]

/-- Concatenating loops adds their indices, provided both kernel integrals exist.
This form also applies when the concatenation is not `C¹` at its join. -/
theorem curveIndex_trans {a w : ℂ} {γ δ : Path a a}
    (hγ : CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ)
    (hδ : CurveIntegrable (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) δ) :
    curveIndex (γ.trans δ) w = curveIndex γ w + curveIndex δ w := by
  simp only [curveIndex, curveIntegral_trans hγ hδ, mul_add]

/-- A closed `C¹` curve has index zero about any point excluded from a simply connected
open domain containing the curve. -/
theorem curveIndex_eq_zero_of_isSimplyConnected {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) {a w : ℂ} {γ : Path a a}
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U) (hw : w ∉ U) :
    curveIndex γ w = 0 := by
  have hf : DifferentiableOn ℂ (fun z ↦ (z - w)⁻¹) U :=
    (differentiableOn_id.sub_const w).inv (fun z hz ↦ sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw))
  rw [curveIndex, curveIntegral_eq_zero_of_differentiableOn_isSimplyConnected hU hUc hf
    (hγ.differentiableOn one_ne_zero) hγU
    (curveIntegrable_of_continuousOn hf.continuousOn hγ hγU), mul_zero]

/-- A counterclockwise circle has index one about each point in its open disk. -/
theorem curveIndex_circle_of_mem_ball {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    curveIndex (Path.circle c R) w = 1 := by
  rw [curveIndex, curveIntegral_circle, circleIntegral.integral_sub_inv_of_mem_ball hw,
    inv_mul_cancel₀ two_pi_I_ne_zero]

/-- A circle of nonnegative radius has index zero about every point outside its closed disk.
The statement includes the degenerate circle of radius zero. -/
theorem curveIndex_circle_of_notMem_closedBall {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : w ∉ closedBall c R) : curveIndex (Path.circle c R) w = 0 := by
  have hf : DifferentiableOn ℂ (fun z ↦ (z - w)⁻¹) (closedBall c R) :=
    (differentiableOn_id.sub_const w).inv
      (fun z hz ↦ sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw))
  have hz := circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
    hf.continuousOn (fun z hz ↦
      (hf z (ball_subset_closedBall hz.1)).differentiableAt
        (mem_nhds_iff.mpr ⟨ball c R, ball_subset_closedBall, isOpen_ball, hz.1⟩))
  rw [curveIndex, curveIntegral_circle, hz, mul_zero]

/-- The Banach-valued Cauchy formula on a simply connected open domain, weighted by
the index of the curve about the evaluation point. -/
theorem two_pi_I_inv_smul_curveIntegral_sub_inv_smul_eq_curveIndex_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsSimplyConnected U)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) {w : ℂ} (hw : w ∈ U)
    {a : ℂ} {γ : Path a a} (hγ : ContDiffOn ℝ 1 γ.extend I)
    (hγU : ∀ t, γ t ∈ U) (hγw : ∀ t, γ t ≠ w) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹ • f z)) γ =
        curveIndex γ w • f w := by
  rw [curveIntegral_sub_inv_smul_of_isSimplyConnected hU hUc hf hw hγ hγU hγw,
    smul_smul, curveIndex]

end Complex
