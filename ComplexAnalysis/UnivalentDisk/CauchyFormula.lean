/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.UnivalentDisk.Index

/-!
# Cauchy's formula on holomorphic images of disks

Pulling the contour back to a circle and dividing out the nonvanishing divided slope
gives the Banach-valued Cauchy formula on a univalent disk image. No convexity of the
image domain and no assumed winding-number normalization are required.

## Main results

* `Complex.curveIntegral_sub_inv_smul_map'_circle_of_injOn_holomorphic`: Cauchy's integral
  formula on the image of a circle under an injective holomorphic map, for functions with values
  in a complex Banach space.
* `Complex.two_pi_I_inv_smul_curveIntegral_sub_inv_smul_map'_circle`: The normalized Cauchy
  formula for an injective holomorphic image of a circle.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section
open Set Metric MeasureTheory
open scoped unitInterval

namespace Complex

/-- Cauchy's integral formula on the image of a circle under an injective holomorphic
map, for functions with values in a complex Banach space. -/
theorem curveIntegral_sub_inv_smul_map'_circle_of_injOn_holomorphic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {F : ℂ → E} (hF : DifferentiableOn ℂ F (f '' U))
    {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) (hRU : closedBall c R ⊆ U)
    (hc : ContinuousOn f (range (Path.circle c R))) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - f w)⁻¹ • F z))
        ((Path.circle c R).map' hc) = (2 * (Real.pi : ℂ) * Complex.I) • F (f w) := by
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg hw
  have hwU := hRU (ball_subset_closedBall hw)
  let g := dslope f w
  have hg : DifferentiableOn ℂ g U := (differentiableOn_dslope (hU.mem_nhds hwU)).mpr hf
  have hg0 : ∀ z ∈ U, g z ≠ 0 := fun z hz =>
    dslope_ne_zero_of_injOn_holomorphic hU hf hi hwU hz
  let A : ℂ → E := fun z => (g z)⁻¹ • (deriv f z • F (f z))
  have hA : DifferentiableOn ℂ A U := (hg.inv hg0).smul
    ((hf.analyticOnNhd hU).deriv.differentiableOn.smul (hF.comp hf (mapsTo_image f U)))
  have hpath : range (Path.circle c R) ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact hRU (circleMap_mem_closedBall c hR.le _)
  rw [curveIntegral_map' (Path.circle c R) hU hf hpath
    ((Path.contDiffOn_circle c R).differentiableOn one_ne_zero), curveIntegral_circle]
  calc
    _ = circleIntegral (fun z => (z - w)⁻¹ • A z) c R := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      change deriv f z • ((f z - f w)⁻¹ • F (f z)) =
        (z - w)⁻¹ • ((g z)⁻¹ • (deriv f z • F (f z)))
      have hfact : (z - w) * g z = f z - f w := sub_smul_dslope f w z
      rw [← hfact, mul_inv_rev]
      simp only [smul_smul]
      congr 1
      ring
    _ = (2 * (Real.pi : ℂ) * Complex.I) • A w :=
      (hA.mono hRU).circleIntegral_sub_inv_smul hw
    _ = (2 * (Real.pi : ℂ) * Complex.I) • F (f w) := by
      dsimp [A, g]
      rw [dslope_same, inv_smul_smul₀ (deriv_ne_zero_of_injOn hU hf hi hwU)]

/-- The normalized Cauchy formula for an injective holomorphic image of a circle. -/
theorem two_pi_I_inv_smul_curveIntegral_sub_inv_smul_map'_circle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    {F : ℂ → E} (hF : DifferentiableOn ℂ F (f '' U))
    {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) (hRU : closedBall c R ⊆ U)
    (hc : ContinuousOn f (range (Path.circle c R))) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - f w)⁻¹ • F z))
        ((Path.circle c R).map' hc) = F (f w) := by
  rw [curveIntegral_sub_inv_smul_map'_circle_of_injOn_holomorphic hU hf hi hF hw hRU hc,
    inv_smul_smul₀ two_pi_I_ne_zero]

end Complex
