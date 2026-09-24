/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Parseval
public import ComplexAnalysis.DiscCauchyTransform
public import ComplexAnalysis.Injective
public import ComplexAnalysis.HolomorphicInverse
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The area theorem

Let `g z = z⁻¹ + h z` with `h` holomorphic on the unit disc, and suppose `g` is injective on the
punctured disc `0 < ‖z‖ < 1` (the class `Σ`). Writing `h z = ∑ b n z ^ n`, the **area theorem**
of Gronwall states `∑ n ‖b n‖² ≤ 1`.

The proof computes the area of the complement `E r` of the image of the punctured disc of
radius `r < 1` in two ways. The index of the image curve `θ ↦ g (r e^{iθ})` about a point `w`
is `(2πi)⁻¹ ∮ g' / (g - w)`; it is `-1` on `E r` (off the null set `g (‖z‖ = r)`) and `0` on
the image, by the argument principle for `z (g z - w)`. Integrating the index over a large disc
and using the Cauchy transform of the disc (`∫_{‖w‖<ρ} (z - w)⁻¹ dA = π conj z`) gives
`-area (E r) = (2i)⁻¹ ∮ conj (g z) g' z dz`, and Parseval's identity on the circle evaluates
the right side as `-π (r⁻² - ∑ n ‖b n‖² r ^ (2n))`. Since the area is nonnegative,
`∑ n ‖b n‖² r ^ (2n) ≤ r⁻²`, and `r → 1` gives the theorem.

## Main results

* `Complex.integral_ball_circleIntegral_deriv_div_sub`: the integral of the index of the image
  of a circle over a large disc, as a contour integral.
* `Complex.circleIntegral_deriv_div_sub_sigma`: the index of the image curve for a map of
  class `Σ`.
* `Complex.tsum_mul_norm_taylorCoeff_sq_mul_pow_le`: `∑ n ‖b n‖² r ^ (2n) ≤ r⁻²`.
* `Complex.tsum_mul_norm_taylorCoeff_sq_le`: **the area theorem** `∑ n ‖b n‖² ≤ 1`.

## References

* J. B. Conway, *Functions of One Complex Variable II*, Chapter 14, §7.
* P. L. Duren, *Univalent Functions*, Chapter 2, §2.
-/

public noncomputable section

open Set Metric Filter MeasureTheory Real
open scoped Topology

namespace Complex

section LogDeriv

variable {U : Set ℂ} {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}

/-- If `f` omits `w` on a closed disc, the logarithmic derivative of `f - w` has vanishing circle
integral. -/
theorem circleIntegral_deriv_div_sub_eq_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hR : 0 ≤ R) (hRU : closedBall c R ⊆ U) (hne : ∀ z ∈ closedBall c R, f z ≠ w) :
    ∮ z in C(c, R), deriv f z / (f z - w) = 0 := by
  have hd := (hf.analyticOnNhd hU).deriv
  have h0 : ∀ z ∈ closedBall c R, f z - w ≠ 0 := fun z hz => sub_ne_zero.mpr (hne z hz)
  have hcont : ContinuousOn (fun z => deriv f z / (f z - w)) (closedBall c R) :=
    (hd.continuousOn.mono hRU).div ((hf.continuousOn.mono hRU).sub continuousOn_const) h0
  refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty hcont
    fun z hz => ?_
  have hzU : z ∈ U := hRU (ball_subset_closedBall hz.1)
  exact (hd z hzU).differentiableAt.div
    (((hf z hzU).differentiableAt (hU.mem_nhds hzU)).sub_const w)
    (h0 z (ball_subset_closedBall hz.1))

/-- If `f w` is attained only at `w`, with nonzero derivative there, the logarithmic derivative
of `f - f w` has circle integral `2πi` around any disc containing `w`. -/
theorem circleIntegral_deriv_div_sub_eq_two_pi_I (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hw : w ∈ ball c R) (hRU : closedBall c R ⊆ U) (hw' : deriv f w ≠ 0)
    (huniq : ∀ z ∈ U, f z = f w → z = w) :
    ∮ z in C(c, R), deriv f z / (f z - f w) = 2 * π * I := by
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg hw
  have hwU := hRU (ball_subset_closedBall hw)
  let g := dslope f w
  have hg : DifferentiableOn ℂ g U := (differentiableOn_dslope (hU.mem_nhds hwU)).mpr hf
  have hg0 : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz
    by_cases hzw : z = w
    · subst hzw
      change dslope f z z ≠ 0
      rw [dslope_same]
      exact hw'
    · change dslope f w z ≠ 0
      rw [dslope_of_ne _ hzw, slope_def_field]
      exact div_ne_zero (sub_ne_zero.mpr fun he => hzw (huniq z hz he)) (sub_ne_zero.mpr hzw)
  have hlog : DifferentiableOn ℂ (fun z => deriv g z / g z) U :=
    (hg.analyticOnNhd hU).deriv.differentiableOn.div hg hg0
  have hzero := circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le countable_empty
    (hlog.continuousOn.mono hRU) (fun z hz =>
      (hlog z (hRU (ball_subset_closedBall hz.1))).differentiableAt
        (hU.mem_nhds (hRU (ball_subset_closedBall hz.1))))
  have he : EqOn (fun z => deriv f z / (f z - f w))
      (fun z => (z - w)⁻¹ + deriv g z / g z) (sphere c R) := by
    intro z hz
    change deriv f z / (f z - f w) = (z - w)⁻¹ + deriv g z / g z
    have hzU := hRU (sphere_subset_closedBall hz)
    have hzw : z ≠ w := sphere_disjoint_ball.ne_of_mem hz hw
    have hfact : ∀ t, (t - w) * g t = f t - f w := fun t => sub_smul_dslope f w t
    have hd := (((hasDerivAt_id z).sub_const w).mul
      ((hg z hzU).differentiableAt (hU.mem_nhds hzU)).hasDerivAt).deriv
    change deriv (fun t => (t - w) * g t) z = 1 * g z + (z - w) * deriv g z at hd
    have hefun : (fun t => (t - w) * g t) = (fun t => f t - f w) := funext hfact
    rw [hefun, deriv_sub_const] at hd
    rw [hd, ← hfact z]
    field_simp [sub_ne_zero.mpr hzw, hg0 z hzU]
  rw [circleIntegral.integral_congr hR.le he, circleIntegral.integral_add, hzero, add_zero,
    circleIntegral.integral_sub_inv_of_mem_ball hw]
  · exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz => sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hw))).circleIntegrable hR.le
  · exact (hlog.continuousOn.mono (sphere_subset_closedBall.trans hRU)).circleIntegrable hR.le

end LogDeriv

section IndexArea

variable {U : Set ℂ} {f : ℂ → ℂ} {r ρ : ℝ}

/-- **The index-area identity.** For `f` holomorphic near the circle `‖z‖ = r` with image in the
disc `‖w‖ < ρ`, the integral over that disc of the contour integral `∮ f' / (f - w)` equals
`π ∮ conj (f z) f' z dz`. Dividing by `2πi`, the integral of the index of the image curve is
`(2i)⁻¹ ∮ conj w dw`. -/
theorem integral_ball_circleIntegral_deriv_div_sub (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hr : 0 < r) (hsub : sphere (0 : ℂ) r ⊆ U)
    (hρ : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ < ρ) :
    ∫ w in ball (0 : ℂ) ρ, ∮ z in C(0, r), deriv f z / (f z - w) =
      π * ∮ z in C(0, r), (starRingEnd ℂ) (f z) * deriv f z := by
  have hsph : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ =>
    circleMap_mem_sphere 0 hr.le θ
  have hderiv : ContinuousOn (deriv f) U := (hf.analyticOnNhd hU).deriv.continuousOn
  -- the curve and its velocity times `f'`
  set a : ℝ → ℂ := fun θ => f (circleMap 0 r θ) with ha_def
  set K : ℝ → ℂ := fun θ => deriv (circleMap 0 r) θ * deriv f (circleMap 0 r θ) with hK_def
  have ha : Continuous a :=
    hf.continuousOn.comp_continuous (continuous_circleMap 0 r) fun θ => hsub (hsph θ)
  have hK : Continuous K := by
    simp only [hK_def, deriv_circleMap]
    exact ((continuous_circleMap 0 r).mul continuous_const).mul
      (hderiv.comp_continuous (continuous_circleMap 0 r) fun θ => hsub (hsph θ))
  have haρ : ∀ θ, ‖a θ‖ < ρ := fun θ => hρ _ (hsph θ)
  have hρ0 : 0 < ρ := (norm_nonneg _).trans_lt (haρ 0)
  obtain ⟨M, hM⟩ :=
    isCompact_uIcc.exists_bound_of_continuousOn (hK.continuousOn (s := uIcc 0 (2 * π)))
  -- the integrand on the product
  set Φ : ℝ × ℂ → ℂ := fun p => K p.1 * (ball (0 : ℂ) ρ).indicator (fun w => (a p.1 - w)⁻¹) p.2
    with hΦ_def
  have hΦmeas : Measurable Φ := by
    refine (hK.comp continuous_fst).measurable.mul ?_
    have : Measurable fun p : ℝ × ℂ => (a p.1 - p.2)⁻¹ :=
      ((ha.comp continuous_fst).sub continuous_snd).measurable.inv
    have h2 : (fun p : ℝ × ℂ => (ball (0 : ℂ) ρ).indicator (fun w => (a p.1 - w)⁻¹) p.2) =
        (univ ×ˢ ball (0 : ℂ) ρ).indicator fun p : ℝ × ℂ => (a p.1 - p.2)⁻¹ := by
      funext p
      by_cases hp : p.2 ∈ ball (0 : ℂ) ρ
      · rw [indicator_of_mem hp, indicator_of_mem (mk_mem_prod (mem_univ _) hp)]
      · rw [indicator_of_notMem hp, indicator_of_notMem fun h => hp h.2]
    rw [h2]
    exact this.indicator (MeasurableSet.univ.prod measurableSet_ball)
  set μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hμ_def
  -- the kernel bound
  set C₀ : ℝ := ∫ u : ℂ, (closedBall (0 : ℂ) (2 * ρ)).indicator (fun u => 1 * ‖u‖⁻¹) u with hC₀
  have hC₀int := integrable_indicator_closedBall_mul_inv_norm 1 (2 * ρ)
  have hker : ∀ θ, ∫ w : ℂ, ‖(ball (0 : ℂ) ρ).indicator (fun w => (a θ - w)⁻¹) w‖ ≤ C₀ := by
    intro θ
    have hle : ∀ w : ℂ, ‖(ball (0 : ℂ) ρ).indicator (fun w => (a θ - w)⁻¹) w‖ ≤
        (closedBall (0 : ℂ) (2 * ρ)).indicator (fun u => 1 * ‖u‖⁻¹) (w - a θ) := by
      intro w
      by_cases hw : w ∈ ball (0 : ℂ) ρ
      · rw [indicator_of_mem hw, indicator_of_mem, one_mul, norm_inv, norm_sub_rev]
        rw [mem_closedBall_zero_iff]
        have := mem_ball_zero_iff.mp hw
        have := haρ θ
        calc ‖w - a θ‖ ≤ ‖w‖ + ‖a θ‖ := norm_sub_le _ _
          _ ≤ 2 * ρ := by linarith
      · rw [indicator_of_notMem hw, norm_zero]
        exact indicator_nonneg (fun _ _ => by positivity) _
    calc ∫ w : ℂ, ‖(ball (0 : ℂ) ρ).indicator (fun w => (a θ - w)⁻¹) w‖
        ≤ ∫ w : ℂ, (closedBall (0 : ℂ) (2 * ρ)).indicator (fun u => 1 * ‖u‖⁻¹) (w - a θ) :=
          integral_mono (integrable_indicator_ball_inv_sub (a θ) ρ).norm
            (hC₀int.comp_sub_right (a θ)) hle
      _ = C₀ := integral_sub_right_eq_self _ (a θ)
  -- integrability on the product
  have hΦint : Integrable Φ (μ.prod volume) := by
    refine (integrable_prod_iff hΦmeas.aestronglyMeasurable).mpr ⟨ae_of_all _ fun θ => ?_, ?_⟩
    · exact (integrable_indicator_ball_inv_sub (a θ) ρ).const_mul (K θ)
    · refine Integrable.mono' (integrable_const (M * C₀))
        (hΦmeas.aestronglyMeasurable.norm.integral_prod_right')
        (ae_restrict_of_ae_restrict_of_subset (subset_refl _) ?_)
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine ae_of_all _ fun θ hθ => ?_
      simp only [hΦ_def, norm_mul, integral_const_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (integral_nonneg fun w => norm_nonneg _)]
      have hC₀0 : 0 ≤ C₀ := integral_nonneg fun u => indicator_nonneg (fun _ _ => by positivity) _
      have hMθ : ‖K θ‖ ≤ M := hM θ (uIoc_subset_uIcc (by rwa [uIoc_of_le (by positivity)]))
      exact mul_le_mul hMθ (hker θ) (integral_nonneg fun w => norm_nonneg _)
        ((norm_nonneg _).trans hMθ)
  -- the left side as a product integral
  have hL : ∫ w in ball (0 : ℂ) ρ, ∮ z in C(0, r), deriv f z / (f z - w) =
      ∫ w : ℂ, ∫ θ, Φ (θ, w) ∂μ := by
    rw [← integral_indicator measurableSet_ball]
    congr 1
    funext w
    by_cases hw : w ∈ ball (0 : ℂ) ρ
    · rw [indicator_of_mem hw, circleIntegral, intervalIntegral.integral_of_le (by positivity)]
      refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
      simp only [hΦ_def, ha_def, hK_def, indicator_of_mem hw, smul_eq_mul, div_eq_mul_inv]
      ring
    · rw [indicator_of_notMem hw]
      symm
      refine integral_eq_zero_of_ae (ae_of_all _ fun θ => ?_)
      simp [hΦ_def, indicator_of_notMem hw]
  -- the right side as a product integral
  have hR : π * ∮ z in C(0, r), (starRingEnd ℂ) (f z) * deriv f z =
      ∫ θ, (∫ w : ℂ, Φ (θ, w)) ∂μ := by
    rw [circleIntegral, intervalIntegral.integral_of_le (by positivity), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    simp only [hΦ_def, ha_def, hK_def]
    rw [integral_const_mul, integral_indicator measurableSet_ball, integral_ball_inv_sub (haρ θ),
      smul_eq_mul]
    ring
  rw [hL, hR, ← integral_prod_symm _ hΦint, ← integral_prod _ hΦint]

end IndexArea

section Sigma

variable {h : ℂ → ℂ} {r : ℝ}

/-- The maps of class `Σ` are holomorphic on the punctured disc. -/
theorem differentiableOn_inv_add (hh : DifferentiableOn ℂ h (ball 0 1)) :
    DifferentiableOn ℂ (fun z => z⁻¹ + h z) (ball 0 1 \ {0}) := fun z hz =>
  ((hasDerivAt_inv hz.2).add
    ((hh z hz.1).differentiableAt
      (isOpen_ball.mem_nhds hz.1)).hasDerivAt).differentiableAt.differentiableWithinAt

/-- The derivative of a map of class `Σ`. -/
theorem deriv_inv_add (hh : DifferentiableOn ℂ h (ball 0 1)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    (hz0 : z ≠ 0) : deriv (fun z => z⁻¹ + h z) z = -(z ^ 2)⁻¹ + deriv h z :=
  ((hasDerivAt_inv hz0).add ((hh z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt).deriv

open Classical in
/-- **The index of the image circle** for a map `g` of class `Σ`: for `w` off the image of the
circle `‖z‖ = r`, the contour integral `∮ g' / (g - w)` is `0` if `w` lies in the image of the
punctured disc of radius `r` and `-2πi` otherwise. -/
theorem circleIntegral_deriv_div_sub_sigma (hh : DifferentiableOn ℂ h (ball 0 1))
    (hinj : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0})) (hr : 0 < r) (hr1 : r < 1) {w : ℂ}
    (hw : ∀ z ∈ sphere (0 : ℂ) r, z⁻¹ + h z ≠ w) :
    ∮ z in C(0, r), deriv (fun z => z⁻¹ + h z) z / (z⁻¹ + h z - w) =
      if w ∈ (fun z => z⁻¹ + h z) '' (ball 0 r \ {0}) then 0 else -(2 * π * I) := by
  have hU : IsOpen (ball (0 : ℂ) 1 \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hgd := differentiableOn_inv_add hh
  set ψ : ℂ → ℂ := fun z => 1 + z * (h z - w) with hψ_def
  have hψd : DifferentiableOn ℂ ψ (ball 0 1) :=
    (differentiableOn_const _).add (differentiableOn_id.mul (hh.sub (differentiableOn_const _)))
  have hψ : ∀ z : ℂ, z ≠ 0 → ψ z = z * (z⁻¹ + h z - w) := fun z hz => by
    simp only [hψ_def]
    field_simp
    ring
  have hψ0 : ψ 0 = 1 := by simp [hψ_def]
  have hderiv : ∀ z ∈ ball (0 : ℂ) 1, deriv ψ z = 1 * (h z - w) + z * deriv h z := fun z hz =>
    (((hasDerivAt_id z).mul
      (((hh z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const w)).const_add
      1).deriv
  have hEq : EqOn (fun z => deriv (fun z => z⁻¹ + h z) z / (z⁻¹ + h z - w))
      (fun z => deriv ψ z / ψ z - (z - 0)⁻¹) (sphere 0 r) := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_mem_sphere hz hr.ne'
    have hz1 : z ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hz]
      exact hr1
    have hgz : z⁻¹ + h z - w ≠ 0 := sub_ne_zero.mpr (hw z hz)
    have hψz : ψ z ≠ 0 := by
      rw [hψ z hz0]
      exact mul_ne_zero hz0 hgz
    have hne' : 1 + z * h z - z * w ≠ 0 := by
      intro h0
      apply hgz
      field_simp
      linear_combination h0
    change deriv (fun z => z⁻¹ + h z) z / (z⁻¹ + h z - w) = deriv ψ z / ψ z - (z - 0)⁻¹
    rw [deriv_inv_add hh hz1 hz0, hderiv z hz1, sub_zero, hψ z hz0]
    field_simp
    ring
  have h1 : CircleIntegrable (fun z => deriv ψ z / ψ z) 0 r := by
    refine ContinuousOn.circleIntegrable hr.le ?_
    have hc : ContinuousOn ψ (sphere 0 r) := hψd.continuousOn.mono (sphere_subset_closedBall.trans
      (closedBall_subset_ball hr1))
    refine ((hψd.analyticOnNhd isOpen_ball).deriv.continuousOn.mono
      (sphere_subset_closedBall.trans (closedBall_subset_ball hr1))).div hc fun z hz => ?_
    have hz0 : z ≠ 0 := ne_of_mem_sphere hz hr.ne'
    rw [hψ z hz0]
    exact mul_ne_zero hz0 (sub_ne_zero.mpr (hw z hz))
  have h2 : CircleIntegrable (fun z : ℂ => (z - 0)⁻¹) 0 r := by
    rw [circleIntegrable_sub_inv_iff]
    right
    rw [mem_sphere_zero_iff_norm, norm_zero, abs_of_pos hr]
    exact hr.ne
  rw [circleIntegral.integral_congr hr.le hEq, circleIntegral.integral_sub h1 h2,
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr)]
  split_ifs with hmem
  · obtain ⟨z₀, hz₀, hz₀w⟩ := hmem
    have hz₀0 : z₀ ≠ 0 := hz₀.2
    have hz₀w' : z₀⁻¹ + h z₀ = w := hz₀w
    have hz₀1 : z₀ ∈ ball (0 : ℂ) 1 := ball_subset_ball hr1.le hz₀.1
    have hψz₀ : ψ z₀ = 0 := by
      rw [hψ z₀ hz₀0, hz₀w']
      simp
    have hd' : deriv ψ z₀ ≠ 0 := by
      rw [hderiv z₀ hz₀1, one_mul]
      have hg' : deriv (fun z => z⁻¹ + h z) z₀ ≠ 0 :=
        deriv_ne_zero_of_injOn hU hgd hinj ⟨hz₀1, hz₀0⟩
      rw [deriv_inv_add hh hz₀1 hz₀0] at hg'
      intro hzero
      apply hg'
      have hw' : w = z₀⁻¹ + h z₀ := hz₀w'.symm
      have : h z₀ - w + z₀ * deriv h z₀ = z₀ * (-(z₀ ^ 2)⁻¹ + deriv h z₀) := by
        rw [hw']
        field_simp
        ring
      rw [this] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left hz₀0
    have huniq : ∀ z ∈ ball (0 : ℂ) 1, ψ z = ψ z₀ → z = z₀ := by
      intro z hz hzz
      rw [hψz₀] at hzz
      have hz0 : z ≠ 0 := fun h0 => by
        rw [h0, hψ0] at hzz
        exact one_ne_zero hzz
      rw [hψ z hz0, mul_eq_zero] at hzz
      rcases hzz with h0 | h0
      · exact absurd h0 hz0
      · exact hinj ⟨hz, hz0⟩ ⟨hz₀1, hz₀0⟩ (by rw [sub_eq_zero] at h0; exact h0.trans hz₀w'.symm)
    have := circleIntegral_deriv_div_sub_eq_two_pi_I isOpen_ball hψd hz₀.1
      (closedBall_subset_ball hr1) hd' huniq
    rw [hψz₀] at this
    simp only [sub_zero] at this
    rw [this, sub_self]
  · have hne : ∀ z ∈ closedBall (0 : ℂ) r, ψ z ≠ 0 := by
      intro z hz
      by_cases hz0 : z = 0
      · rw [hz0, hψ0]
        exact one_ne_zero
      · rw [hψ z hz0]
        refine mul_ne_zero hz0 (sub_ne_zero.mpr fun hgz => ?_)
        rcases (mem_closedBall_zero_iff.mp hz).lt_or_eq with hlt | heq
        · exact hmem ⟨z, ⟨mem_ball_zero_iff.mpr hlt, hz0⟩, hgz⟩
        · exact hw z (mem_sphere_zero_iff_norm.mpr heq) hgz
    have := circleIntegral_deriv_div_sub_eq_zero isOpen_ball hψd hr.le (closedBall_subset_ball hr1)
      (w := 0) hne
    simp only [sub_zero] at this
    rw [this, zero_sub]

/-- The contour integral `∮ conj (g z) g' z dz` for a map `g` of class `Σ`, evaluated by
Parseval's identity. -/
theorem circleIntegral_conj_mul_deriv_sigma (hh : DifferentiableOn ℂ h (ball 0 1)) (hr : 0 < r)
    (hr1 : r < 1) :
    ∮ z in C(0, r), (starRingEnd ℂ) (z⁻¹ + h z) * deriv (fun z => z⁻¹ + h z) z =
      I * ((-(2 * π) / r ^ 2 + 2 * π * ∑' n : ℕ, n * (‖taylorCoeff h n‖ ^ 2 * r ^ (2 * n)) : ℝ) :
        ℂ) := by
  have hmem := circleMap_zero_mem_ball hr.le hr1
  have hcm : ∀ θ : ℝ, circleMap 0 r θ ≠ 0 := fun θ => circleMap_ne_center hr.ne'
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hderiv : DifferentiableOn ℂ (deriv h) (ball 0 1) :=
    (hh.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hcl : DifferentiableOn ℂ h (closedBall 0 r) := hh.mono (closedBall_subset_ball hr1)
  -- the conjugate of `z⁻¹` on the circle
  have hconj : ∀ θ : ℝ, (starRingEnd ℂ) (circleMap 0 r θ)⁻¹ = circleMap 0 r θ / r ^ 2 := by
    intro θ
    have h1 : circleMap 0 r θ * (starRingEnd ℂ) (circleMap 0 r θ) = (r : ℂ) ^ 2 := by
      rw [mul_conj', norm_circleMap_zero, abs_of_pos hr]
    rw [map_inv₀, ← h1]
    have : (starRingEnd ℂ) (circleMap 0 r θ) ≠ 0 := (map_ne_zero _).mpr (hcm θ)
    have hc := hcm θ
    field_simp
  -- the three pieces of the integrand
  set A : ℝ → ℂ := fun θ => (r : ℂ)⁻¹ ^ 2 *
    (-1 + circleMap 0 r θ ^ 2 * deriv h (circleMap 0 r θ)) with hA_def
  set B : ℝ → ℂ := fun θ => (starRingEnd ℂ) (h (circleMap 0 r θ)) * (-(circleMap 0 r θ)⁻¹)
    with hB_def
  set C : ℝ → ℂ := fun θ => (starRingEnd ℂ) (h (circleMap 0 r θ)) *
    (circleMap 0 r θ * deriv h (circleMap 0 r θ)) with hC_def
  have hpt : ∀ θ : ℝ, deriv (circleMap 0 r) θ •
      ((starRingEnd ℂ) ((circleMap 0 r θ)⁻¹ + h (circleMap 0 r θ)) *
        deriv (fun z => z⁻¹ + h z) (circleMap 0 r θ)) = I * (A θ + B θ + C θ) := by
    intro θ
    have hc := hcm θ
    rw [deriv_circleMap, smul_eq_mul, deriv_inv_add hh (hmem θ) (hcm θ), map_add, hconj]
    simp only [hA_def, hB_def, hC_def]
    field_simp
    ring
  have hcont_h : Continuous fun θ : ℝ => h (circleMap 0 r θ) :=
    hh.continuousOn.comp_continuous (continuous_circleMap 0 r) hmem
  have hcont_dh : Continuous fun θ : ℝ => deriv h (circleMap 0 r θ) :=
    hderiv.continuousOn.comp_continuous (continuous_circleMap 0 r) hmem
  have hAc : Continuous A := by
    simp only [hA_def]
    fun_prop
  have hBc : Continuous B := by
    simp only [hB_def]
    exact (continuous_conj.comp hcont_h).mul ((continuous_circleMap 0 r).inv₀ hcm).neg
  have hCc : Continuous C := by
    simp only [hC_def]
    exact (continuous_conj.comp hcont_h).mul ((continuous_circleMap 0 r).mul hcont_dh)
  -- `∫ A`
  have hA : ∫ θ in (0 : ℝ)..2 * π, A θ = (r : ℂ)⁻¹ ^ 2 * (2 * π * (-1)) := by
    simp only [hA_def]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hF : DifferentiableOn ℂ (fun z => -1 + z ^ 2 * deriv h z) (closedBall 0 r) :=
      (differentiableOn_const _).add ((differentiableOn_pow 2).mul
        (hderiv.mono (closedBall_subset_ball hr1)))
    have := integral_circleMap_eq_two_pi_mul hF hr
    simpa using this
  -- `∫ B`
  have hB : ∫ θ in (0 : ℝ)..2 * π, B θ = 0 := by
    have hG : Continuous fun θ : ℝ => -(circleMap 0 r θ)⁻¹ :=
      ((continuous_circleMap 0 r).inv₀ hcm).neg
    have hsum := hasSum_conj_taylorCoeff_mul_integral hh hr.le hr1 hG
    have hzero : ∀ n : ℕ,
        ∫ θ in (0 : ℝ)..2 * π, exp (-(n * (θ * I))) * (-(circleMap 0 r θ)⁻¹) = 0 := by
      intro n
      have hc : (-((n : ℂ) + 1) * I) ≠ 0 := by
        refine mul_ne_zero (neg_ne_zero.mpr ?_) I_ne_zero
        exact_mod_cast Nat.succ_ne_zero n
      have hpt' : ∀ θ : ℝ, exp (-(n * (θ * I))) * (-(circleMap 0 r θ)⁻¹) =
          -(r : ℂ)⁻¹ * exp ((-((n : ℂ) + 1) * I) * θ) := by
        intro θ
        rw [circleMap_zero_eq, mul_inv, ← exp_neg,
          show (-((n : ℂ) + 1) * I) * θ = -(n * (θ * I)) + -(θ * I) by ring, exp_add]
        ring
      simp_rw [hpt']
      rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
      have : exp (-((n : ℂ) + 1) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
        rw [show -((n : ℂ) + 1) * I * ((2 * π : ℝ) : ℂ) = -(((n + 1 : ℕ) : ℂ) * (2 * π * I)) by
          push_cast; ring, exp_neg, exp_nat_mul_two_pi_mul_I, inv_one]
      rw [this]
      simp
    simp_rw [hzero, mul_zero] at hsum
    exact (hsum.unique hasSum_zero).symm ▸ rfl
  -- `∫ C`
  have hC : ∫ θ in (0 : ℝ)..2 * π, C θ =
      ((2 * π * ∑' n : ℕ, n * (‖taylorCoeff h n‖ ^ 2 * r ^ (2 * n)) : ℝ) : ℂ) := by
    have hsum := hasSum_mul_norm_taylorCoeff_sq hh hr hr1
    rw [hsum.tsum_eq.symm, ← ofReal_tsum, tsum_mul_left]
  rw [circleIntegral]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    ((by fun_prop : Continuous fun θ : ℝ => A θ + B θ).intervalIntegrable _ _)
    (hCc.intervalIntegrable _ _),
    intervalIntegral.integral_add (hAc.intervalIntegrable _ _) (hBc.intervalIntegrable _ _),
    hA, hB, hC]
  push_cast
  congr 1
  field_simp
  ring

/-- The complement of the image of the punctured disc of radius `r` under a map of class `Σ`
lies in the disc of radius `M + r⁻¹`, where `M` bounds the map on the circle `‖z‖ = r`. -/
theorem compl_image_subset_closedBall (hh : DifferentiableOn ℂ h (ball 0 1)) (hr : 0 < r)
    (hr1 : r < 1) {M : ℝ} (hM : ∀ z ∈ sphere (0 : ℂ) r, ‖z⁻¹ + h z‖ ≤ M) :
    ((fun z => z⁻¹ + h z) '' (ball 0 r \ {0}))ᶜ ⊆ closedBall 0 (M + r⁻¹) := by
  intro w hw
  rw [mem_compl_iff] at hw
  by_contra hout
  rw [mem_closedBall_zero_iff, not_le] at hout
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (circleMap_mem_sphere 0 hr.le 0))
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  set ψ : ℂ → ℂ := fun z => 1 + z * (h z - w) with hψ_def
  have hψ : ∀ z : ℂ, z ≠ 0 → ψ z = z * (z⁻¹ + h z - w) := fun z hz => by
    simp only [hψ_def]
    field_simp
    ring
  have hψd : DifferentiableOn ℂ ψ (ball 0 1) :=
    (differentiableOn_const _).add (differentiableOn_id.mul (hh.sub (differentiableOn_const _)))
  have hne : ∀ z ∈ closedBall (0 : ℂ) r, ψ z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · rw [hz0]
      simp [hψ_def]
    · rw [hψ z hz0]
      refine mul_ne_zero hz0 (sub_ne_zero.mpr fun hgz => ?_)
      rcases (mem_closedBall_zero_iff.mp hz).lt_or_eq with hlt | heq
      · exact hw ⟨z, ⟨mem_ball_zero_iff.mpr hlt, hz0⟩, hgz⟩
      · have := hM z (mem_sphere_zero_iff_norm.mpr heq)
        rw [hgz] at this
        linarith
  have hφ : DiffContOnCl ℂ (fun z => (ψ z)⁻¹) (ball 0 r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball 0 hr.ne']
    exact ((hψd.mono (closedBall_subset_ball hr1)).inv hne)
  have hbound : ∀ z ∈ frontier (ball (0 : ℂ) r), ‖(ψ z)⁻¹‖ ≤ (r * (‖w‖ - M))⁻¹ := by
    intro z hz
    rw [frontier_ball 0 hr.ne'] at hz
    have hz0 : z ≠ 0 := ne_of_mem_sphere hz hr.ne'
    have hzr : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
    have hM' := hM z hz
    have h1 : ‖w‖ - M ≤ ‖z⁻¹ + h z - w‖ := by
      rw [norm_sub_rev]
      linarith [norm_sub_norm_le w (z⁻¹ + h z)]
    have hpos : 0 < r * (‖w‖ - M) := mul_pos hr (by linarith)
    rw [norm_inv, hψ z hz0, norm_mul, hzr]
    exact inv_anti₀ hpos (by gcongr)
  have hmax := norm_le_of_forall_mem_frontier_norm_le isBounded_ball hφ hbound
    (subset_closure (mem_ball_self hr) : (0 : ℂ) ∈ closure (ball 0 r))
  simp only [hψ_def, zero_mul, add_zero, inv_one, norm_one] at hmax
  have hpos : 0 < r * (‖w‖ - M) := mul_pos hr (by linarith)
  have := (one_le_inv₀ hpos).mp hmax
  have h2 : ‖w‖ - M ≤ r⁻¹ := by
    rw [← one_div, le_div_iff₀ hr]
    linarith
  linarith

/-- **The area theorem on the circle of radius `r`**: for a map `z⁻¹ + h z` of class `Σ` with
Taylor coefficients `b n` of `h`, `∑ n ‖b n‖² r ^ (2n) ≤ r⁻²` for `0 < r < 1`. -/
theorem tsum_mul_norm_taylorCoeff_sq_mul_pow_le (hh : DifferentiableOn ℂ h (ball 0 1))
    (hinj : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0})) (hr : 0 < r) (hr1 : r < 1) :
    ∑' n : ℕ, n * (‖taylorCoeff h n‖ ^ 2 * r ^ (2 * n)) ≤ (r ^ 2)⁻¹ := by
  classical
  have hU : IsOpen (ball (0 : ℂ) 1 \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hgd := differentiableOn_inv_add hh
  have hsub : sphere (0 : ℂ) r ⊆ ball 0 1 \ {0} := fun z hz =>
    mem_sdiff_of_mem (by rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hz]; exact hr1)
      (ne_of_mem_sphere hz hr.ne')
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn
    (hgd.continuousOn.mono hsub)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (circleMap_mem_sphere 0 hr.le 0))
  set ρ : ℝ := M + r⁻¹ + 1 with hρ_def
  have hρ : ∀ z ∈ sphere (0 : ℂ) r, ‖z⁻¹ + h z‖ < ρ := fun z hz => by
    have := hM z hz
    have : 0 < r⁻¹ := inv_pos.mpr hr
    linarith
  -- the image set and its complement
  set S := (fun z => z⁻¹ + h z) '' (ball 0 r \ {0}) with hS_def
  have hSo : IsOpen S := isOpen_image_of_injOn (isOpen_ball.sdiff isClosed_singleton)
    (hgd.mono fun z hz => mem_sdiff_of_mem (ball_subset_ball hr1.le hz.1) hz.2)
    (hinj.mono fun z hz => mem_sdiff_of_mem (ball_subset_ball hr1.le hz.1) hz.2)
  have hEB : Sᶜ ⊆ ball (0 : ℂ) ρ :=
    (compl_image_subset_closedBall hh hr hr1 hM).trans (closedBall_subset_ball (by linarith))
  -- the image of the circle is a null set
  have hnull : volume ((fun z => z⁻¹ + h z) '' sphere (0 : ℂ) r) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume)
      ((hgd.mono hsub).restrictScalars ℝ) (Measure.addHaar_sphere volume 0 r)
  -- the index-area identity
  have hidx := integral_ball_circleIntegral_deriv_div_sub hU hgd hr hsub hρ
  beta_reduce at hidx
  have hae : ∀ᵐ w ∂(volume : Measure ℂ), w ∈ ball (0 : ℂ) ρ →
      (∮ z in C(0, r), deriv (fun z => z⁻¹ + h z) z / (z⁻¹ + h z - w)) =
        (Sᶜ).indicator (fun _ => -(2 * π * I)) w := by
    have h1 : ∀ᵐ w ∂(volume : Measure ℂ), w ∉ (fun z => z⁻¹ + h z) '' sphere (0 : ℂ) r := by
      rw [ae_iff]
      simp only [not_not, ofPred_mem_eq]
      exact hnull
    filter_upwards [h1] with w hw _
    have hw' : ∀ z ∈ sphere (0 : ℂ) r, z⁻¹ + h z ≠ w := fun z hz he => hw ⟨z, hz, he⟩
    rw [circleIntegral_deriv_div_sub_sigma hh hinj hr hr1 hw', ← hS_def]
    by_cases hS : w ∈ S
    · simp [hS]
    · simp [hS]
  rw [setIntegral_congr_ae measurableSet_ball hae,
    integral_indicator hSo.isClosed_compl.measurableSet,
    Measure.restrict_restrict hSo.isClosed_compl.measurableSet, inter_eq_left.mpr hEB,
    setIntegral_const, circleIntegral_conj_mul_deriv_sigma hh hr hr1] at hidx
  -- compare imaginary parts
  have him := congrArg Complex.im hidx
  have h2re : (2 : ℂ).re = 2 := by norm_num
  have h2im : (2 : ℂ).im = 0 := by norm_num
  simp only [real_smul, mul_im, ofReal_re, ofReal_im, neg_re, neg_im, mul_re, I_re, I_im,
    h2re, h2im] at him
  have hvol : 0 ≤ (volume.real Sᶜ) := measureReal_nonneg
  have hpi : 0 < π := pi_pos
  have hr2 : 0 < r ^ 2 := by positivity
  have him' : π * (-(2 * π) / r ^ 2 + 2 * π * ∑' n : ℕ, n * (‖taylorCoeff h n‖ ^ 2 * r ^ (2 * n))) =
      -(2 * π * volume.real Sᶜ) := by
    linear_combination -him
  have key :
      -(2 * π) / r ^ 2 + 2 * π * ∑' n : ℕ, n * (‖taylorCoeff h n‖ ^ 2 * r ^ (2 * n)) ≤ 0 := by
    by_contra hX
    push Not at hX
    have h1 := mul_pos hpi hX
    have h2 := mul_nonneg hpi.le hvol
    linarith
  rw [← sub_nonpos]
  have : 2 * π * (∑' n : ℕ, n * (‖taylorCoeff h n‖ ^ 2 * r ^ (2 * n)) - (r ^ 2)⁻¹) =
      -(2 * π) / r ^ 2 + 2 * π * ∑' n : ℕ, n * (‖taylorCoeff h n‖ ^ 2 * r ^ (2 * n)) := by
    field_simp
    ring
  nlinarith

/-- The partial sums of `n ‖b n‖²` are bounded by one. -/
theorem sum_range_mul_norm_taylorCoeff_sq_le (hh : DifferentiableOn ℂ h (ball 0 1))
    (hinj : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0})) (N : ℕ) :
    ∑ n ∈ Finset.range N, (n : ℝ) * ‖taylorCoeff h n‖ ^ 2 ≤ 1 := by
  set S := ∑ n ∈ Finset.range N, (n : ℝ) * ‖taylorCoeff h n‖ ^ 2 with hS
  have hbound : ∀ r : ℝ, r ∈ Ioo (0 : ℝ) 1 → S ≤ (r ^ 2)⁻¹ / r ^ (2 * N) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hsum := summable_mul_norm_taylorCoeff_sq_mul_pow hh hr.1 hr.2
    have h1 : S * r ^ (2 * N) ≤
        ∑ n ∈ Finset.range N, (n : ℝ) * (‖taylorCoeff h n‖ ^ 2 * r ^ (2 * n)) := by
      rw [hS, Finset.sum_mul]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' : 2 * n ≤ 2 * N := by
        have := Finset.mem_range.mp hn
        omega
      have hpow := pow_le_pow_of_le_one hr.1.le hr.2.le hn'
      have h0 : 0 ≤ (n : ℝ) * ‖taylorCoeff h n‖ ^ 2 := by positivity
      calc (n : ℝ) * ‖taylorCoeff h n‖ ^ 2 * r ^ (2 * N)
          ≤ (n : ℝ) * ‖taylorCoeff h n‖ ^ 2 * r ^ (2 * n) :=
            mul_le_mul_of_nonneg_left hpow h0
        _ = (n : ℝ) * (‖taylorCoeff h n‖ ^ 2 * r ^ (2 * n)) := by ring
    have h2 := sum_le_hasSum (Finset.range N) (fun n _ => by positivity) hsum.hasSum
    have h3 := tsum_mul_norm_taylorCoeff_sq_mul_pow_le hh hinj hr.1 hr.2
    rw [le_div_iff₀ (pow_pos hr.1 _)]
    linarith
  have hlim : Tendsto (fun r : ℝ => (r ^ 2)⁻¹ / r ^ (2 * N)) (𝓝[<] 1) (𝓝 1) := by
    have : Tendsto (fun r : ℝ => (r ^ 2)⁻¹ / r ^ (2 * N)) (𝓝 1)
        (𝓝 (((1 : ℝ) ^ 2)⁻¹ / 1 ^ (2 * N))) :=
      (((continuous_pow 2).tendsto 1).inv₀ (by norm_num)).div
        ((continuous_pow (2 * N)).tendsto 1) (by norm_num)
    simp only [one_pow, inv_one, div_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.eventually_of_mem (Ioo_mem_nhdsLT zero_lt_one) hbound)

/-- **The area theorem** (Gronwall). If `z⁻¹ + h z` with `h` holomorphic on the unit disc is
injective on the punctured unit disc, then the Taylor coefficients `b n` of `h` satisfy
`∑ n ‖b n‖² ≤ 1`. -/
theorem tsum_mul_norm_taylorCoeff_sq_le (hh : DifferentiableOn ℂ h (ball 0 1))
    (hinj : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0})) :
    ∑' n : ℕ, (n : ℝ) * ‖taylorCoeff h n‖ ^ 2 ≤ 1 :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity)
    (sum_range_mul_norm_taylorCoeff_sq_le hh hinj)

/-- The weighted squares `n ‖b n‖²` of the Taylor coefficients of a map of class `Σ` are
summable. -/
theorem summable_mul_norm_taylorCoeff_sq (hh : DifferentiableOn ℂ h (ball 0 1))
    (hinj : InjOn (fun z => z⁻¹ + h z) (ball 0 1 \ {0})) :
    Summable fun n : ℕ => (n : ℝ) * ‖taylorCoeff h n‖ ^ 2 :=
  summable_of_sum_range_le (fun n => by positivity)
    (sum_range_mul_norm_taylorCoeff_sq_le hh hinj)

end Sigma

end Complex

end
