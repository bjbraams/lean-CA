/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.UnivalentDisk.Geometry
public import ComplexAnalysis.Integral.Map
public import ComplexAnalysis.CurveIndex

/-!
# Orientation of holomorphic disk contours

An injective holomorphic map sends a counterclockwise circle to a contour of index one
about each point of the image disk. The proof factors `f z - f w` into `z - w` times the
nonvanishing holomorphic divided slope. Its logarithmic derivative contributes zero.
Thus positive orientation is a theorem, rather than part of the contour's input data.

## Main results

* `Complex.dslope_ne_zero_of_injOn_holomorphic`: The divided slope of an injective holomorphic
  map never vanishes on its domain, including at the removable diagonal.
* `Complex.circleIntegral_deriv_div_sub_of_injOn_holomorphic`: The logarithmic derivative of `f
  - f w` has circle integral `2πi` when `f` is injective and holomorphic on a neighborhood of
  the disk and `w` lies inside it.
* `Complex.curveIndex_map'_circle_of_injOn_holomorphic`: An injective holomorphic image of the
  counterclockwise circle has index one about every point of the image disk.
* `Complex.curveIndex_map'_circle_eq_zero_of_notMem_image_closedBall`: The image-circle index
  vanishes outside the image of the closed disk. Injectivity of the holomorphic map is not
  needed for this exterior statement.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section
open Set Metric MeasureTheory
open scoped unitInterval

namespace Complex

/-- The divided slope of an injective holomorphic map never vanishes on its domain,
including at the removable diagonal. -/
theorem dslope_ne_zero_of_injOn_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {w z : ℂ} (hw : w ∈ U) (hz : z ∈ U) : dslope f w z ≠ 0 := by
  by_cases hzw : z = w
  · subst z
    rw [dslope_same]
    exact deriv_ne_zero_of_injOn hU hf hi hw
  · rw [dslope_of_ne _ hzw, slope_def_field]
    exact div_ne_zero (sub_ne_zero.mpr (fun he ↦ hzw (hi hz hw he))) (sub_ne_zero.mpr hzw)

/-- The logarithmic derivative of `f - f w` has circle integral `2πi` when `f` is
injective and holomorphic on a neighborhood of the disk and `w` lies inside it. -/
theorem circleIntegral_deriv_div_sub_of_injOn_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) (hRU : closedBall c R ⊆ U) :
    circleIntegral (fun z ↦ deriv f z / (f z - f w)) c R =
      2 * (Real.pi : ℂ) * Complex.I :=
  have hwU := hRU (ball_subset_closedBall hw)
  circleIntegral_deriv_div_sub_eq_two_pi_I hU hf hw hRU (deriv_ne_zero_of_injOn hU hf hi hwU)
    fun _ hz he ↦ hi hz hwU he

/-- An injective holomorphic image of the counterclockwise circle has index one about
every point of the image disk. -/
theorem curveIndex_map'_circle_of_injOn_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) (hRU : closedBall c R ⊆ U)
    (hc : ContinuousOn f (range (Path.circle c R))) :
    curveIndex ((Path.circle c R).map' hc) (f w) = 1 := by
  have hR : 0 ≤ R := (lt_of_le_of_lt dist_nonneg hw).le
  have hpath : range (Path.circle c R) ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact hRU (circleMap_mem_closedBall c hR _)
  rw [curveIndex, curveIntegral_map' (Path.circle c R) hU hf hpath
    ((Path.contDiffOn_circle c R).differentiableOn one_ne_zero), curveIntegral_circle]
  change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    circleIntegral (fun z ↦ deriv f z / (f z - f w)) c R = 1
  rw [circleIntegral_deriv_div_sub_of_injOn_holomorphic hU hf hi hw hRU,
    inv_mul_cancel₀ two_pi_I_ne_zero]

/-- The image-circle index vanishes outside the image of the closed disk. Injectivity
of the holomorphic map is not needed for this exterior statement. -/
theorem curveIndex_map'_circle_eq_zero_of_notMem_image_closedBall
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {c w : ℂ} {R : ℝ} (hR : 0 ≤ R) (hRU : closedBall c R ⊆ U)
    (hw : w ∉ f '' closedBall c R) (hc : ContinuousOn f (range (Path.circle c R))) :
    curveIndex ((Path.circle c R).map' hc) w = 0 := by
  have hzero := circleIntegral_deriv_div_sub_eq_zero hU hf hR hRU fun z hz he ↦ hw ⟨z, hz, he⟩
  have hpath : range (Path.circle c R) ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact hRU (circleMap_mem_closedBall c hR _)
  rw [curveIndex, curveIntegral_map' (Path.circle c R) hU hf hpath
    ((Path.contDiffOn_circle c R).differentiableOn one_ne_zero), curveIntegral_circle]
  change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    circleIntegral (fun z ↦ deriv f z / (f z - w)) c R = 0
  rw [hzero, mul_zero]

end Complex
