/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.KoebeDistortion
public import ComplexAnalysis.BranchLog

/-!
# The Koebe distortion theorem and the growth theorem (upper bound)

For `f` holomorphic and injective on the unit disc with `f 0 = 0` and `f' 0 = 1` (the class
`S`), the **Koebe distortion theorem** bounds the derivative along a ray:
`(1 - r) / (1 + r) ^ 3 ≤ ‖f' z‖ ≤ (1 + r) / (1 - r) ^ 3` for `‖z‖ = r < 1`, and the **growth
theorem** (upper bound) gives `‖f z‖ ≤ r / (1 - r) ^ 2`.

The proof integrates the pre-Schwarzian bound (`KoebeDistortion`) along the ray from `0` to
`z`. Since `f'` is nonvanishing (`f` injective) and the disc is simply connected, `f'` has a
holomorphic logarithm `L` with `L 0 = 0` (`BranchLog`); `Re (L z) = log ‖f' z‖`, and along the
ray `t ↦ t • u` (`u` the unit vector `z / ‖z‖`), the pre-Schwarzian bound gives
`(2 t - 4) / (1 - t ^ 2) ≤ Re (deriv L (t • u) * u) ≤ (2 t + 4) / (1 - t ^ 2)`. Integrating
(the fundamental theorem of calculus for the real part of a path) and evaluating the explicit
antiderivatives `log (1 + t) - 3 log (1 - t)` and `log (1 - t) - 3 log (1 + t)` gives the
distortion bounds. The growth upper bound follows from `‖f z‖ ≤ ∫₀^r ‖f' (t u)‖ dt` and the
distortion upper bound, using the antiderivative `t / (1 - t) ^ 2` of `(1 + t) / (1 - t) ^ 3`.

## Main results

* `Complex.distortion_le_of_class_S`: **the Koebe distortion theorem**, both bounds together.
* `Complex.norm_le_div_one_sub_sq_of_class_S`: **the growth theorem**, upper bound.

## References

* P. L. Duren, *Univalent Functions*, Chapter 2, Theorem 2.6.
* J. B. Conway, *Functions of One Complex Variable II*, Chapter 14, §7.
-/

public noncomputable section

open Set Metric Filter Real MeasureTheory intervalIntegral
open scoped ComplexConjugate

namespace Complex

variable {f : ℂ → ℂ}

/-! ### Antiderivatives -/

/-- The antiderivative for the upper distortion bound. -/
def distortionUpperAnti (t : ℝ) : ℝ := Real.log (1 + t) - 3 * Real.log (1 - t)

/-- The antiderivative for the lower distortion bound. -/
def distortionLowerAnti (t : ℝ) : ℝ := Real.log (1 - t) - 3 * Real.log (1 + t)

/-- The antiderivative for the growth upper bound. -/
def growthAnti (t : ℝ) : ℝ := t / (1 - t) ^ 2

/-- On `(-1, 1)`, the upper distortion antiderivative has derivative `(2 * t + 4) / (1 - t ^ 2)`. -/
theorem hasDerivAt_distortionUpperAnti {t : ℝ} (ht1 : -1 < t) (ht2 : t < 1) :
    HasDerivAt distortionUpperAnti ((2 * t + 4) / (1 - t ^ 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := (hasDerivAt_id t).const_add 1
  have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := (hasDerivAt_id t).const_sub 1
  have hp1 : (1 : ℝ) + t ≠ 0 := by linarith
  have hp2 : (1 : ℝ) - t ≠ 0 := by linarith
  have hp3 : (1 : ℝ) - t ^ 2 ≠ 0 := by
    intro h; apply hp1; nlinarith
  have hl1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 + t)⁻¹ t := by
    have h := (Real.hasDerivAt_log hp1).comp t h1
    simp only [mul_one] at h
    exact h
  have hl2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 - t)⁻¹) t := by
    have h := (Real.hasDerivAt_log hp2).comp t h2
    simp only [mul_neg, mul_one] at h
    exact h
  have h := hl1.sub (hl2.const_mul 3)
  have heq : distortionUpperAnti = fun t => Real.log (1 + t) - 3 * Real.log (1 - t) := rfl
  rw [heq]
  convert h using 1
  field_simp
  ring

/-- On `(-1, 1)`, the lower distortion antiderivative has derivative `(2 * t - 4) / (1 - t ^ 2)`. -/
theorem hasDerivAt_distortionLowerAnti {t : ℝ} (ht1 : -1 < t) (ht2 : t < 1) :
    HasDerivAt distortionLowerAnti ((2 * t - 4) / (1 - t ^ 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := (hasDerivAt_id t).const_add 1
  have h2 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := (hasDerivAt_id t).const_sub 1
  have hp1 : (1 : ℝ) + t ≠ 0 := by linarith
  have hp2 : (1 : ℝ) - t ≠ 0 := by linarith
  have hp3 : (1 : ℝ) - t ^ 2 ≠ 0 := by
    intro h; apply hp1; nlinarith
  have hl1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 + t)⁻¹ t := by
    have h := (Real.hasDerivAt_log hp1).comp t h1
    simp only [mul_one] at h
    exact h
  have hl2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 - t)⁻¹) t := by
    have h := (Real.hasDerivAt_log hp2).comp t h2
    simp only [mul_neg, mul_one] at h
    exact h
  have h := hl2.sub (hl1.const_mul 3)
  have heq : distortionLowerAnti = fun t => Real.log (1 - t) - 3 * Real.log (1 + t) := rfl
  rw [heq]
  convert h using 1
  field_simp
  ring

/-- Below one, the growth antiderivative has derivative `(1 + t) / (1 - t) ^ 3`. -/
theorem hasDerivAt_growthAnti {t : ℝ} (ht1 : t < 1) :
    HasDerivAt growthAnti ((1 + t) / (1 - t) ^ 3) t := by
  have hp2 : (1 : ℝ) - t ≠ 0 := by linarith
  have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := (hasDerivAt_id t).const_sub 1
  have h2 : HasDerivAt (fun t : ℝ => (1 - t) * (1 - t)) ((-1) * (1 - t) + (1 - t) * (-1)) t :=
    h1.mul h1
  have h2' : HasDerivAt (fun t : ℝ => (1 - t) ^ 2) ((-1) * (1 - t) + (1 - t) * (-1)) t := by
    have heq : (fun t : ℝ => (1 - t) ^ 2) = fun t : ℝ => (1 - t) * (1 - t) := by
      funext t; ring
    rw [heq]; exact h2
  have h3 : HasDerivAt growthAnti
      ((1 * (1 - t) ^ 2 - t * ((-1) * (1 - t) + (1 - t) * (-1))) / ((1 - t) ^ 2) ^ 2) t :=
    (hasDerivAt_id t).div h2' (pow_ne_zero 2 hp2)
  convert h3 using 1
  field_simp
  ring


/-- Exponentiating the lower distortion antiderivative gives the rational distortion bound. -/
theorem exp_distortionLowerAnti {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.exp (distortionLowerAnti r) = (1 - r) / (1 + r) ^ 3 := by
  have hrp1 : (0 : ℝ) < 1 + r := by linarith
  have hrm1 : (0 : ℝ) < 1 - r := by linarith
  rw [distortionLowerAnti, Real.exp_sub, Real.exp_log hrm1,
    show (3 : ℝ) * Real.log (1 + r) = Real.log ((1 + r) ^ 3) by
      rw [Real.log_pow]; push_cast; ring,
    Real.exp_log (by positivity)]

/-- Exponentiating the upper distortion antiderivative gives the rational distortion bound. -/
theorem exp_distortionUpperAnti {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.exp (distortionUpperAnti r) = (1 + r) / (1 - r) ^ 3 := by
  have hrp1 : (0 : ℝ) < 1 + r := by linarith
  have hrm1 : (0 : ℝ) < 1 - r := by linarith
  rw [distortionUpperAnti, Real.exp_sub, Real.exp_log hrp1,
    show (3 : ℝ) * Real.log (1 - r) = Real.log ((1 - r) ^ 3) by
      rw [Real.log_pow]; push_cast; ring,
    Real.exp_log (by positivity)]

/-- The pre-Schwarzian estimate bounds the real logarithmic derivative in every unit
radial direction inside the disc. -/
private theorem radial_logDeriv_bounds (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) {u : ℂ} (hu : ‖u‖ = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (2 * t - 4) / (1 - t ^ 2) ≤
        ((deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)) * u).re ∧
      ((deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)) * u).re ≤
        (2 * t + 4) / (1 - t ^ 2) := by
  have htu : ‖(t : ℂ) * u‖ < 1 := by
    rw [norm_mul, Complex.norm_real, hu, mul_one, Real.norm_of_nonneg ht0]
    exact ht1
  have hmem : (t : ℂ) * u ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr htu
  have hpre := norm_one_sub_normSq_mul_deriv_deriv_div_deriv_sub_two_conj_le hf hinj hmem
  rw [mul_div_assoc] at hpre
  have hconj : conj ((t : ℂ) * u) * u = (t : ℂ) := by
    rw [map_mul, conj_ofReal, mul_assoc, mul_comm (conj u) u, mul_conj', hu]
    push_cast; ring
  have hnormsq : normSq ((t : ℂ) * u) = t ^ 2 := by
    rw [normSq_mul, normSq_eq_norm_sq, normSq_eq_norm_sq u, hu]
    simp [Complex.norm_real]
  have hrewrite : ((1 - (normSq ((t : ℂ) * u) : ℂ)) * (deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)) -
      2 * conj ((t : ℂ) * u)) * u =
      (1 - ((t : ℝ) ^ 2 : ℂ)) * ((deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)) * u) - 2 * t := by
    rw [hnormsq]
    push_cast
    linear_combination (-2 : ℂ) * hconj
  have hnorm2 : ‖(1 - ((t : ℝ) ^ 2 : ℂ)) * ((deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)) * u) - 2 * t‖ ≤ 4 := by
    rw [← hrewrite, norm_mul, hu, mul_one]
    exact hpre
  have ht2 : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith [ht1, ht0]
  have hRe : ((1 - ((t : ℝ) ^ 2 : ℂ)) * ((deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)) * u) - 2 * t).re =
      (1 - t ^ 2) * ((deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)) * u).re - 2 * t := by
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq]
  have hRebound : |(1 - t ^ 2) * ((deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)) * u).re - 2 * t| ≤ 4 := by
    rw [← hRe]
    exact (abs_re_le_norm _).trans hnorm2
  rw [abs_le] at hRebound
  have hpos : 0 < 1 - t ^ 2 := by nlinarith [ht1, ht0]
  constructor
  · rw [div_le_iff₀ hpos]; nlinarith [hRebound.1]
  · rw [le_div_iff₀ hpos]; nlinarith [hRebound.2]

/-- Integrating the radial differential inequalities gives the two distortion
antiderivative bounds for a real function normalized at zero. -/
private theorem distortion_bounds_of_deriv_bounds {G D : ℝ → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hGderiv : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt G (D t) t)
    (hcont : ContinuousOn D (Icc 0 r))
    (hGbound : ∀ t ∈ Icc (0 : ℝ) r,
      (2 * t - 4) / (1 - t ^ 2) ≤ D t ∧ D t ≤ (2 * t + 4) / (1 - t ^ 2))
    (hG0 : G 0 = 0) : distortionLowerAnti r ≤ G r ∧ G r ≤ distortionUpperAnti r := by
  have hint : IntervalIntegrable D volume 0 r := (uIcc_of_le hr0 ▸ hcont).intervalIntegrable
  have hFTC : (∫ t in (0 : ℝ)..r, D t) = G r := by
    rw [integral_eq_sub_of_hasDerivAt
      (fun t ht => hGderiv t (by rwa [uIcc_of_le hr0] at ht)) hint, hG0, sub_zero]
  -- explicit continuity of the bounding functions on `[0, r]`
  have hcontlow : ContinuousOn (fun t : ℝ => (2 * t - 4) / (1 - t ^ 2)) (Icc 0 r) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
    nlinarith [ht.2.trans_lt hr1, ht.1]
  have hcontup : ContinuousOn (fun t : ℝ => (2 * t + 4) / (1 - t ^ 2)) (Icc 0 r) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
    nlinarith [ht.2.trans_lt hr1, ht.1]
  have hintlow : IntervalIntegrable (fun t : ℝ => (2 * t - 4) / (1 - t ^ 2)) volume 0 r :=
    (uIcc_of_le hr0 ▸ hcontlow).intervalIntegrable
  have hintup : IntervalIntegrable (fun t : ℝ => (2 * t + 4) / (1 - t ^ 2)) volume 0 r :=
    (uIcc_of_le hr0 ▸ hcontup).intervalIntegrable
  -- bound the integral by the explicit antiderivatives
  have hlowerint : (∫ t in (0 : ℝ)..r, (2 * t - 4) / (1 - t ^ 2)) = distortionLowerAnti r := by
    have h := integral_eq_sub_of_hasDerivAt
      (f := distortionLowerAnti) (f' := fun t => (2 * t - 4) / (1 - t ^ 2))
      (fun t ht => by
        rw [uIcc_of_le hr0] at ht
        exact hasDerivAt_distortionLowerAnti (by linarith [ht.1]) (by linarith [ht.2.trans_lt hr1]))
      hintlow
    rw [h]
    simp [distortionLowerAnti]
  have hupperint : (∫ t in (0 : ℝ)..r, (2 * t + 4) / (1 - t ^ 2)) = distortionUpperAnti r := by
    have h := integral_eq_sub_of_hasDerivAt
      (f := distortionUpperAnti) (f' := fun t => (2 * t + 4) / (1 - t ^ 2))
      (fun t ht => by
        rw [uIcc_of_le hr0] at ht
        exact hasDerivAt_distortionUpperAnti (by linarith [ht.1]) (by linarith [ht.2.trans_lt hr1]))
      hintup
    rw [h]
    simp [distortionUpperAnti]
  have hloweri : (∫ t in (0 : ℝ)..r, (2 * t - 4) / (1 - t ^ 2)) ≤
      ∫ t in (0 : ℝ)..r, D t :=
    integral_mono_on hr0 hintlow hint fun t ht => (hGbound t ht).1
  have hupperi : (∫ t in (0 : ℝ)..r, D t) ≤
      ∫ t in (0 : ℝ)..r, (2 * t + 4) / (1 - t ^ 2) :=
    integral_mono_on hr0 hint hintup fun t ht => (hGbound t ht).2
  rw [hlowerint] at hloweri
  rw [hupperint] at hupperi
  rw [hFTC] at hloweri hupperi
  exact ⟨hloweri, hupperi⟩

/-! ### The Koebe distortion theorem -/

/-- **The Koebe distortion theorem.** For `f` holomorphic and injective on the disc with
`f 0 = 0` and `f' 0 = 1`, `‖f' z‖` is bounded between `(1 - ‖z‖) / (1 + ‖z‖) ^ 3` and
`(1 + ‖z‖) / (1 - ‖z‖) ^ 3`. -/
theorem distortion_le_of_class_S (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (hf1 : deriv f 0 = 1) {z₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) :
    (1 - ‖z₀‖) / (1 + ‖z₀‖) ^ 3 ≤ ‖deriv f z₀‖ ∧
      ‖deriv f z₀‖ ≤ (1 + ‖z₀‖) / (1 - ‖z₀‖) ^ 3 := by
  set r : ℝ := ‖z₀‖ with hr_def
  have hr0 : 0 ≤ r := norm_nonneg z₀
  have hr1 : r < 1 := mem_ball_zero_iff.mp hz₀
  rcases eq_or_lt_of_le hr0 with hr0' | hr0'
  · -- the trivial case `z₀ = 0`
    have hz₀0 : z₀ = 0 := by
      have h := hr0'.symm
      rw [hr_def] at h
      exact norm_eq_zero.mp h
    rw [← hr0', hz₀0, hf1]
    norm_num
  -- the general case: set up the ray and the holomorphic logarithm of `f'`
  have hU : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd hU
  have hderivfan : AnalyticOnNhd ℂ (deriv f) (ball 0 1) := hfan.deriv
  have hderivne : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn hU hf hinj hz
  have hw0 : Complex.exp (0 : ℂ) = deriv f 0 := by rw [hf1]; simp
  obtain ⟨L, hLan, hLeq, hL0⟩ := exists_analyticOnNhd_logBranch_eq hU
    isSimplyConnected_ball_zero_one hderivfan.differentiableOn hderivne
    (mem_ball_self one_pos) hw0
  set u : ℂ := z₀ / r with hu_def
  have hu : ‖u‖ = 1 := by
    have hnr : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr0']
    rw [hu_def, norm_div, hnr]
    exact div_self hr0'.ne'
  have hzru : z₀ = (r : ℂ) * u := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0'.ne'
    rw [hu_def, mul_div_cancel₀ z₀ hr']
  -- the real part of the log-derivative along the ray
  set G : ℝ → ℝ := fun t => (L ((t : ℂ) * u)).re with hG_def
  have hGderiv : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt G (deriv L ((t : ℂ) * u) * u).re t := by
    intro t ht
    have htu : ‖(t : ℂ) * u‖ < 1 := by
      rw [norm_mul, Complex.norm_real, hu, mul_one, Real.norm_of_nonneg ht.1]
      exact ht.2.trans_lt hr1
    have hmem : (t : ℂ) * u ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr htu
    have h1 : HasDerivAt (fun s : ℂ => s * u) u ((t : ℂ)) := by
      simpa using (hasDerivAt_id ((t : ℂ))).mul_const u
    have h2 : HasDerivAt L (deriv L ((t : ℂ) * u)) ((t : ℂ) * u) :=
      (hLan ((t : ℂ) * u) hmem).differentiableAt.hasDerivAt
    have h3 : HasDerivAt (fun s : ℂ => L (s * u)) (deriv L ((t : ℂ) * u) * u) ((t : ℂ)) :=
      h2.comp (t : ℂ) h1
    have h4 : HasDerivAt (fun s : ℝ => L ((s : ℂ) * u)) (deriv L ((t : ℂ) * u) * u) t :=
      h3.comp_ofReal
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h4
  have hGbound : ∀ t ∈ Icc (0 : ℝ) r,
      (2 * t - 4) / (1 - t ^ 2) ≤ (deriv L ((t : ℂ) * u) * u).re ∧
        (deriv L ((t : ℂ) * u) * u).re ≤ (2 * t + 4) / (1 - t ^ 2) := by
    intro t ht
    have hmem : (t : ℂ) * u ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, hu, mul_one,
        Real.norm_of_nonneg ht.1]
      exact ht.2.trans_lt hr1
    rw [deriv_logBranch hU hderivfan.differentiableOn hLan.continuousOn hLeq hmem]
    exact radial_logDeriv_bounds hf hinj hu ht.1 (ht.2.trans_lt hr1)
  -- integrate along the ray
  have hcont : ContinuousOn (fun t : ℝ => (deriv L ((t : ℂ) * u) * u).re) (Icc 0 r) := by
    have hmaps : MapsTo (fun t : ℝ => (t : ℂ) * u) (Icc 0 r) (ball 0 1) := by
      intro t ht
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, hu, mul_one, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      exact ht.2.trans_lt hr1
    have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) * u) (Icc 0 r) := by fun_prop
    have h2 : ContinuousOn (deriv L) (ball (0:ℂ) 1) := hLan.deriv.continuousOn
    have h3 : ContinuousOn (fun t : ℝ => deriv L ((t : ℂ) * u)) (Icc 0 r) := h2.comp h1 hmaps
    exact Complex.continuous_re.comp_continuousOn (h3.mul continuousOn_const)
  have hG0 : G 0 = 0 := by simp [hG_def, hL0]
  have hGr : G r = Real.log ‖deriv f z₀‖ := by
    have h1 : Complex.exp (L z₀) = deriv f z₀ := hLeq hz₀
    have h2 : ‖deriv f z₀‖ = Real.exp (L z₀).re := by rw [← h1, Complex.norm_exp]
    have h3 : (L z₀).re = Real.log ‖deriv f z₀‖ := by rw [h2, Real.log_exp]
    change (L ((r:ℂ) * u)).re = Real.log ‖deriv f z₀‖
    rw [← hzru, h3]
  have hbounds := distortion_bounds_of_deriv_bounds hr0 hr1 hGderiv hcont hGbound hG0
  rw [hGr] at hbounds
  have hexp_lower : Real.exp (distortionLowerAnti r) ≤ Real.exp (Real.log ‖deriv f z₀‖) :=
    Real.exp_le_exp.mpr hbounds.1
  have hexp_upper : Real.exp (Real.log ‖deriv f z₀‖) ≤ Real.exp (distortionUpperAnti r) :=
    Real.exp_le_exp.mpr hbounds.2
  have hf'pos : 0 < ‖deriv f z₀‖ := by
    rw [norm_pos_iff]; exact hderivne z₀ hz₀
  rw [Real.exp_log hf'pos] at hexp_lower hexp_upper
  rw [exp_distortionLowerAnti hr0 hr1] at hexp_lower
  rw [exp_distortionUpperAnti hr0 hr1] at hexp_upper
  exact ⟨hr_def ▸ hexp_lower, hr_def ▸ hexp_upper⟩

/-! ### The growth theorem (upper bound) -/

/-- **The growth theorem, upper bound.** For `f` holomorphic and injective on the disc with
`f 0 = 0` and `f' 0 = 1`, `‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2`. -/
theorem norm_le_div_one_sub_sq_of_class_S (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) : ‖f z₀‖ ≤ ‖z₀‖ / (1 - ‖z₀‖) ^ 2 := by
  set r : ℝ := ‖z₀‖ with hr_def
  have hr0 : 0 ≤ r := norm_nonneg z₀
  have hr1 : r < 1 := mem_ball_zero_iff.mp hz₀
  rcases eq_or_lt_of_le hr0 with hr0' | hr0'
  · have hz₀0 : z₀ = 0 := by
      have h := hr0'.symm; rw [hr_def] at h; exact norm_eq_zero.mp h
    rw [← hr0', hz₀0, hf0]; norm_num
  have hU : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
  set u : ℂ := z₀ / r with hu_def
  have hu : ‖u‖ = 1 := by
    have hnr : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr0']
    rw [hu_def, norm_div, hnr]; exact div_self hr0'.ne'
  have hzru : z₀ = (r : ℂ) * u := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0'.ne'
    rw [hu_def, mul_div_cancel₀ z₀ hr']
  -- the fundamental theorem of calculus for `f` along the ray
  have hderiv : ∀ t ∈ Icc (0 : ℝ) r,
      HasDerivAt (fun s : ℝ => f ((s : ℂ) * u)) (deriv f ((t : ℂ) * u) * u) t := by
    intro t ht
    have htu : ‖(t : ℂ) * u‖ < 1 := by
      rw [norm_mul, Complex.norm_real, hu, mul_one, Real.norm_of_nonneg ht.1]
      exact ht.2.trans_lt hr1
    have hmem : (t : ℂ) * u ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr htu
    have h1 : HasDerivAt (fun s : ℂ => s * u) u ((t : ℂ)) := by
      simpa using (hasDerivAt_id ((t : ℂ))).mul_const u
    have h2 : HasDerivAt f (deriv f ((t : ℂ) * u)) ((t : ℂ) * u) :=
      (hf.differentiableAt (hU.mem_nhds hmem)).hasDerivAt
    have h3 : HasDerivAt (fun s : ℂ => f (s * u)) (deriv f ((t : ℂ) * u) * u) ((t : ℂ)) :=
      h2.comp (t : ℂ) h1
    exact h3.comp_ofReal
  have hcont : ContinuousOn (fun t : ℝ => deriv f ((t : ℂ) * u) * u) (Icc 0 r) := by
    have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) * u) (Icc 0 r) := by fun_prop
    have hmaps : MapsTo (fun t : ℝ => (t : ℂ) * u) (Icc 0 r) (ball 0 1) := by
      intro t ht
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, hu, mul_one, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      exact ht.2.trans_lt hr1
    have h2 : ContinuousOn (deriv f) (ball (0 : ℂ) 1) := (hf.analyticOnNhd hU).deriv.continuousOn
    exact (h2.comp h1 hmaps).mul continuousOn_const
  have hint : IntervalIntegrable (fun t : ℝ => deriv f ((t : ℂ) * u) * u) volume 0 r :=
    (uIcc_of_le hr0 ▸ hcont).intervalIntegrable
  have hFTC : f z₀ = ∫ t in (0 : ℝ)..r, deriv f ((t : ℂ) * u) * u := by
    have h := integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t (by rwa [uIcc_of_le hr0] at ht)) hint
    simp only [Complex.ofReal_zero, zero_mul, hf0, sub_zero] at h
    rw [hzru]
    exact h.symm
  -- bound the norm via the triangle inequality and the distortion upper bound
  have hnormineq : ‖f z₀‖ ≤ ∫ t in (0 : ℝ)..r, ‖deriv f ((t : ℂ) * u) * u‖ := by
    rw [hFTC]
    exact norm_integral_le_integral_norm hr0
  have hnormeq : ∀ t ∈ Icc (0 : ℝ) r, ‖deriv f ((t : ℂ) * u) * u‖ = ‖deriv f ((t : ℂ) * u)‖ := by
    intro t _; rw [norm_mul, hu, mul_one]
  have hnormboundpt : ∀ t ∈ Icc (0 : ℝ) r,
      ‖deriv f ((t : ℂ) * u)‖ ≤ (1 + t) / (1 - t) ^ 3 := by
    intro t ht
    have htun : ‖(t : ℂ) * u‖ = t := by
      rw [norm_mul, Complex.norm_real, hu, mul_one, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have htu : (t : ℂ) * u ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, htun]
      exact ht.2.trans_lt hr1
    have := (distortion_le_of_class_S hf hinj hf1 htu).2
    rwa [htun] at this
  have hnormcontnorm : ContinuousOn (fun t : ℝ => ‖deriv f ((t : ℂ) * u) * u‖) (Icc 0 r) :=
    hcont.norm
  have hintnorm : IntervalIntegrable (fun t : ℝ => ‖deriv f ((t : ℂ) * u) * u‖) volume 0 r :=
    (uIcc_of_le hr0 ▸ hnormcontnorm).intervalIntegrable
  have hcontgrow : ContinuousOn (fun t : ℝ => (1 + t) / (1 - t) ^ 3) (Icc 0 r) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
    have : (0:ℝ) < 1 - t := by linarith [ht.2.trans_lt hr1]
    positivity
  have hintgrow : IntervalIntegrable (fun t : ℝ => (1 + t) / (1 - t) ^ 3) volume 0 r :=
    (uIcc_of_le hr0 ▸ hcontgrow).intervalIntegrable
  have hint2 : (∫ t in (0 : ℝ)..r, ‖deriv f ((t : ℂ) * u) * u‖) ≤
      ∫ t in (0 : ℝ)..r, (1 + t) / (1 - t) ^ 3 :=
    integral_mono_on hr0 hintnorm hintgrow fun t ht => by
      rw [hnormeq t ht]; exact hnormboundpt t ht
  have hgrowint : (∫ t in (0 : ℝ)..r, (1 + t) / (1 - t) ^ 3) = growthAnti r := by
    have h := integral_eq_sub_of_hasDerivAt
      (f := growthAnti) (f' := fun t => (1 + t) / (1 - t) ^ 3)
      (fun t ht => by
        rw [uIcc_of_le hr0] at ht
        exact hasDerivAt_growthAnti (by linarith [ht.2.trans_lt hr1]))
      hintgrow
    rw [h]; simp [growthAnti]
  rw [hgrowint] at hint2
  refine hnormineq.trans (hint2.trans_eq ?_)
  rw [growthAnti, hr_def]

end Complex

end
