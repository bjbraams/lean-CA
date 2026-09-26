/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.LaurentSeries.Annulus
public import ComplexAnalysis.CauchyTransform
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The Cauchy transform of a disc

The Cauchy transform of the indicator function of the disc `‖w‖ < ρ` is
`∫_{‖w‖ < ρ} (z - w)⁻¹ dA(w) = π conj z` for `‖z‖ < ρ`. The proof passes to polar coordinates:
the angular integral `∫₀^{2π} (z - s e^{iθ})⁻¹ dθ` is `2π / z` for `s < ‖z‖` and `0` for
`s > ‖z‖` by Cauchy's formula on the circle, and the radial integral of `s · 2π / z` over
`0 < s < ‖z‖` is `π ‖z‖² / z = π conj z`.

This is the integral form of Green's theorem needed for the area theorem: integrating the
index of a closed curve over the plane gives `(2i)⁻¹ ∮ conj w dw`.

## Main results

* `Complex.integral_inv_sub_circleMap`: the angular integral of the Cauchy kernel.
* `Complex.integral_ball_inv_sub`: the Cauchy transform of the disc indicator.
* `Complex.integrable_indicator_ball_inv_sub`: integrability of the disc-truncated Cauchy
  kernel.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Metric Filter MeasureTheory Real
open scoped Topology

section Polar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrability transfers to polar coordinates. -/
theorem integrableOn_polarCoord_target_smul {f : ℝ × ℝ → E} (hf : Integrable f) :
    IntegrableOn (fun p ↦ p.1 • f (polarCoord.symm p)) polarCoord.target := by
  have h1 : IntegrableOn f (polarCoord.symm '' polarCoord.target) := hf.integrableOn
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt) polarCoord.symm.injOn] at h1
  refine h1.congr_fun (fun p hp ↦ ?_) polarCoord.open_target.measurableSet
  rw [polarCoord_target] at hp
  simp only [det_fderivPolarCoordSymm]
  rw [abs_of_pos hp.1]

/-- Integrability transfers to polar coordinates on `ℂ`. -/
theorem Complex.integrableOn_polarCoord_target_smul {f : ℂ → E} (hf : Integrable f) :
    IntegrableOn (fun p ↦ p.1 • f (Complex.polarCoord.symm p)) polarCoord.target := by
  have h : Integrable (f ∘ Complex.measurableEquivRealProd.symm) :=
    (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hf
  exact _root_.integrableOn_polarCoord_target_smul h

end Polar

namespace Complex

/-- The disc-truncated Cauchy kernel `w ↦ 1_{‖w‖ < ρ} (z - w)⁻¹` is integrable. -/
theorem integrable_indicator_ball_inv_sub (z : ℂ) (ρ : ℝ) :
    Integrable ((ball (0 : ℂ) ρ).indicator fun w ↦ (z - w)⁻¹) := by
  have hg := (integrable_indicator_closedBall_mul_inv_norm 1 (ρ + ‖z‖)).comp_sub_right z
  refine hg.mono' ?_ (ae_of_all _ fun w ↦ ?_)
  · exact ((measurable_const.sub measurable_id).inv.indicator
      measurableSet_ball).aestronglyMeasurable
  · by_cases hw : w ∈ ball (0 : ℂ) ρ
    · rw [indicator_of_mem hw, indicator_of_mem, one_mul, norm_inv, norm_sub_rev]
      rw [mem_closedBall_zero_iff]
      have := mem_ball_zero_iff.mp hw
      calc ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ ρ + ‖z‖ := by linarith
    · rw [indicator_of_notMem hw, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ by positivity) _

/-- The angular integral of the Cauchy kernel over the circle of radius `s` centered at the
origin: `2π / z` for `s < ‖z‖` and `0` for `s > ‖z‖`. -/
theorem integral_inv_sub_circleMap {z : ℂ} {s : ℝ} (hs : 0 < s) (hsz : s ≠ ‖z‖) :
    ∫ θ in (0 : ℝ)..2 * π, (z - circleMap 0 s θ)⁻¹ =
      if s < ‖z‖ then 2 * π / z else 0 := by
  have hcm : ∀ θ : ℝ, circleMap 0 s θ ≠ 0 := fun θ ↦ circleMap_ne_center hs.ne'
  have hcirc : (∫ θ in (0 : ℝ)..2 * π, (z - circleMap 0 s θ)⁻¹) =
      ∮ u in C(0, s), (u * I)⁻¹ * (z - u)⁻¹ := by
    rw [circleIntegral]
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    rw [deriv_circleMap, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (mul_ne_zero (hcm θ) I_ne_zero), one_mul]
  rw [hcirc]
  by_cases hz0 : z = 0
  · subst hz0
    have hlt : ¬ s < ‖(0 : ℂ)‖ := not_lt.mpr (by simpa using hs.le)
    simp only [hlt, ↓reduceIte]
    have hEq : EqOn (fun u : ℂ ↦ (u * I)⁻¹ * (0 - u)⁻¹)
        (fun u ↦ -I⁻¹ * (u - 0) ^ (-2 : ℤ)) (sphere 0 s) := by
      intro u hu
      have hu0 : u ≠ 0 := ne_of_mem_sphere hu hs.ne'
      change (u * I)⁻¹ * (0 - u)⁻¹ = -I⁻¹ * (u - 0) ^ (-2 : ℤ)
      rw [zero_sub, sub_zero, zpow_neg, zpow_two]
      field_simp
    rw [circleIntegral.integral_congr hs.le hEq, circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_zpow_of_ne (by norm_num) 0 0 s, mul_zero]
  · have hIz : I * z ≠ 0 := mul_ne_zero I_ne_zero hz0
    have hEq : EqOn (fun u : ℂ ↦ (u * I)⁻¹ * (z - u)⁻¹)
        (fun u ↦ (I * z)⁻¹ * ((u - 0)⁻¹ - (u - z)⁻¹)) (sphere 0 s) := by
      intro u hu
      have hu0 : u ≠ 0 := ne_of_mem_sphere hu hs.ne'
      have huz : u ≠ z := fun h ↦ hsz (by rw [← h, ← mem_sphere_zero_iff_norm.mp hu])
      have huz' : z - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huz)
      have huz'' : u - z ≠ 0 := sub_ne_zero.mpr huz
      change (u * I)⁻¹ * (z - u)⁻¹ = (I * z)⁻¹ * ((u - 0)⁻¹ - (u - z)⁻¹)
      rw [sub_zero]
      field_simp
      ring
    have h1 : CircleIntegrable (fun u : ℂ ↦ (u - 0)⁻¹) 0 s := by
      rw [circleIntegrable_sub_inv_iff]
      right
      rw [mem_sphere_zero_iff_norm, norm_zero, abs_of_pos hs]
      exact hs.ne
    have h2 : CircleIntegrable (fun u : ℂ ↦ (u - z)⁻¹) 0 s := by
      rw [circleIntegrable_sub_inv_iff]
      right
      rw [mem_sphere_zero_iff_norm, abs_of_pos hs]
      exact fun h ↦ hsz h.symm
    rw [circleIntegral.integral_congr hs.le hEq, circleIntegral.integral_const_mul,
      circleIntegral.integral_sub h1 h2,
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hs)]
    split_ifs with hlt
    · rw [circleIntegral_sub_inv_eq_zero_of_lt_norm hs.le hlt, sub_zero]
      field_simp
    · have hzs : z ∈ ball (0 : ℂ) s := by
        rw [mem_ball_zero_iff]
        exact lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hsz)
      rw [circleIntegral.integral_sub_inv_of_mem_ball hzs, sub_self, mul_zero]

/-- The Cauchy transform of the indicator function of a disc:
`∫_{‖w‖ < ρ} (z - w)⁻¹ dA(w) = π conj z` for `‖z‖ < ρ`. -/
theorem integral_ball_inv_sub {z : ℂ} {ρ : ℝ} (hz : ‖z‖ < ρ) :
    ∫ w in ball (0 : ℂ) ρ, (z - w)⁻¹ = π * (starRingEnd ℂ) z := by
  have hρ : 0 < ρ := (norm_nonneg z).trans_lt hz
  set F : ℂ → ℂ := (ball (0 : ℂ) ρ).indicator fun w ↦ (z - w)⁻¹ with hF
  have hint : Integrable F := integrable_indicator_ball_inv_sub z ρ
  rw [← integral_indicator measurableSet_ball, ← Complex.integral_comp_polarCoord_symm]
  have hI := Complex.integrableOn_polarCoord_target_smul hint
  -- the polar integrand
  set G : ℝ × ℝ → ℂ := fun p ↦
    (Ioo 0 ρ).indicator (fun s : ℝ ↦ (s : ℂ) * (z - circleMap 0 s p.2)⁻¹) p.1 with hG
  have hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    intro p
    rw [Complex.polarCoord_symm_apply, circleMap, zero_add, exp_mul_I]
    push_cast
    ring
  have hpt : EqOn (fun p : ℝ × ℝ ↦ p.1 • F (Complex.polarCoord.symm p)) G polarCoord.target := by
    intro p hp
    rw [polarCoord_target] at hp
    simp only [hG, hF, hsymm, real_smul]
    by_cases h : p.1 < ρ
    · rw [indicator_of_mem (show p.1 ∈ Ioo 0 ρ from ⟨hp.1, h⟩), indicator_of_mem]
      rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hp.1]
      exact h
    · rw [indicator_of_notMem (show p.1 ∉ Ioo 0 ρ from fun h' ↦ h h'.2), indicator_of_notMem,
        mul_zero]
      rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hp.1]
      exact h
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hpt]
  have hI' : Integrable G
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
    have := hI.congr_fun hpt polarCoord.open_target.measurableSet
    rwa [IntegrableOn, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict] at this
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hI']
  -- the inner (angular) integral
  have hper : ∀ s : ℝ, Function.Periodic (fun θ : ℝ ↦ (z - circleMap 0 s θ)⁻¹) (2 * π) :=
    fun s θ ↦ by simp only [periodic_circleMap 0 s θ]
  have hinner : ∀ s : ℝ, 0 < s → s ≠ ‖z‖ →
      ∫ θ in Ioo (-π) π, G (s, θ) =
        (Ioo 0 ρ).indicator (fun s : ℝ ↦ (s : ℂ) * (if s < ‖z‖ then 2 * π / z else 0)) s := by
    intro s hs hsz
    simp only [hG]
    by_cases h : s ∈ Ioo 0 ρ
    · simp only [indicator_of_mem h]
      rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
        ← integral_inv_sub_circleMap hs hsz]
      congr 1
      have := (hper s).intervalIntegral_add_eq (-π) 0
      rw [zero_add, show -π + 2 * π = π by ring] at this
      exact this
    · simp only [indicator_of_notMem h, integral_zero]
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioi (0 : ℝ) → ∫ θ in Ioo (-π) π, G (s, θ) =
      (Ioo 0 ρ).indicator (fun s : ℝ ↦ (s : ℂ) * (if s < ‖z‖ then 2 * π / z else 0)) s := by
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ ‖z‖ := by
      rw [ae_iff]
      simp only [not_not]
      exact measure_singleton _
    filter_upwards [hne] with s hs hs0
    exact hinner s hs0 hs
  rw [setIntegral_congr_ae measurableSet_Ioi hae]
  -- the outer (radial) integral
  have hind : ∀ s : ℝ, (Ioo 0 ρ).indicator
      (fun s : ℝ ↦ (s : ℂ) * (if s < ‖z‖ then 2 * π / z else 0)) s =
      (Ioo 0 ‖z‖).indicator (fun s : ℝ ↦ (2 * π / z) * (s : ℂ)) s := by
    intro s
    by_cases h : s ∈ Ioo 0 ‖z‖
    · have h2 := h.2
      rw [indicator_of_mem h, indicator_of_mem (show s ∈ Ioo 0 ρ from ⟨h.1, h.2.trans hz⟩)]
      simp only [h2, ↓reduceIte, mul_comm]
    · rw [indicator_of_notMem h]
      by_cases h' : s ∈ Ioo 0 ρ
      · have hlt : ¬ s < ‖z‖ := fun hlt ↦ h ⟨h'.1, hlt⟩
        rw [indicator_of_mem h']
        simp only [hlt, ↓reduceIte, mul_zero]
      · rw [indicator_of_notMem h']
  simp_rw [hind]
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    show Ioo 0 ‖z‖ ∩ Ioi 0 = Ioo 0 ‖z‖ from inter_eq_left.mpr fun s hs ↦ hs.1,
    integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (norm_nonneg z), intervalIntegral.integral_ofReal,
    integral_id]
  by_cases hz0 : z = 0
  · subst hz0
    simp
  · push_cast
    rw [← mul_conj' z]
    field_simp
    ring

end Complex

end
