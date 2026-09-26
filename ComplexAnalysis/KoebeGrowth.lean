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
`(2 t - 4) / (1 - t ^ 2) ≤ Re (deriv L (t • u) * u) ≤ (2 t + 4) / (1 - t ^ 2)`. Comparing
with the explicit antiderivatives `log (1 + t) - 3 log (1 - t)` and `log (1 - t) - 3 log (1 + t)`
(Mathlib's fencing theorem `image_le_of_deriv_right_le_deriv_boundary`) gives the distortion
bounds. The growth upper bound compares `‖f (t u)‖` with `t / (1 - t) ^ 2`, whose derivative
`(1 + t) / (1 - t) ^ 3` bounds `‖f' (t u)‖` by the distortion upper bound
(`image_norm_le_of_norm_deriv_right_le_deriv_boundary'`).

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
  have hp : (1 : ℝ) + t ≠ 0 := by linarith
  have hm : (1 : ℝ) - t ≠ 0 := by linarith
  have hq : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith
  refine ((((hasDerivAt_id' t).const_add 1).log hp).sub
    ((((hasDerivAt_id' t).const_sub 1).log hm).const_mul 3)).congr_deriv ?_
  field_simp
  ring

/-- On `(-1, 1)`, the lower distortion antiderivative has derivative `(2 * t - 4) / (1 - t ^ 2)`. -/
theorem hasDerivAt_distortionLowerAnti {t : ℝ} (ht1 : -1 < t) (ht2 : t < 1) :
    HasDerivAt distortionLowerAnti ((2 * t - 4) / (1 - t ^ 2)) t := by
  have hp : (1 : ℝ) + t ≠ 0 := by linarith
  have hm : (1 : ℝ) - t ≠ 0 := by linarith
  have hq : (1 : ℝ) - t ^ 2 ≠ 0 := by nlinarith
  refine ((((hasDerivAt_id' t).const_sub 1).log hm).sub
    ((((hasDerivAt_id' t).const_add 1).log hp).const_mul 3)).congr_deriv ?_
  field_simp
  ring

/-- Below one, the growth antiderivative has derivative `(1 + t) / (1 - t) ^ 3`. -/
theorem hasDerivAt_growthAnti {t : ℝ} (ht1 : t < 1) :
    HasDerivAt growthAnti ((1 + t) / (1 - t) ^ 3) t := by
  have hm : (1 : ℝ) - t ≠ 0 := by linarith
  refine ((hasDerivAt_id' t).div (((hasDerivAt_id' t).const_sub 1).pow 2)
    (pow_ne_zero 2 hm)).congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- Exponentiating the lower distortion antiderivative gives the rational distortion bound. -/
theorem exp_distortionLowerAnti {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.exp (distortionLowerAnti r) = (1 - r) / (1 + r) ^ 3 := by
  rw [distortionLowerAnti, Real.exp_sub, Real.exp_log (by linarith),
    show (3 : ℝ) * Real.log (1 + r) = Real.log ((1 + r) ^ 3) by simp [Real.log_pow],
    Real.exp_log (by positivity)]

/-- Exponentiating the upper distortion antiderivative gives the rational distortion bound. -/
theorem exp_distortionUpperAnti {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.exp (distortionUpperAnti r) = (1 + r) / (1 - r) ^ 3 := by
  have : 0 < 1 - r := by linarith
  rw [distortionUpperAnti, Real.exp_sub, Real.exp_log (by linarith),
    show (3 : ℝ) * Real.log (1 - r) = Real.log ((1 - r) ^ 3) by simp [Real.log_pow],
    Real.exp_log (by positivity)]

/-! ### Rays in the disc -/

/-- A point `t * u` on the ray through a unit vector `u` has norm `t` for `t ≥ 0`. -/
theorem norm_ofReal_mul_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖(t : ℂ) * u‖ = t := by
  rw [norm_mul, norm_real, hu, mul_one, Real.norm_of_nonneg ht]

/-- A point `t * u` with `0 ≤ t < 1` on the ray through a unit vector `u` lies in the unit
disc. -/
theorem ofReal_mul_mem_ball {u : ℂ} (hu : ‖u‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (t : ℂ) * u ∈ ball (0 : ℂ) 1 := by
  rwa [mem_ball_zero_iff, norm_ofReal_mul_of_norm_eq_one hu ht0]

/-- The chain rule along the ray `t ↦ t * u`. -/
theorem hasDerivAt_comp_ofReal_mul {g : ℂ → ℂ} {u : ℂ} {t : ℝ}
    (hg : DifferentiableAt ℂ g ((t : ℂ) * u)) :
    HasDerivAt (fun s : ℝ ↦ g ((s : ℂ) * u)) (deriv g ((t : ℂ) * u) * u) t := by
  have h1 : HasDerivAt (fun s : ℂ ↦ s * u) u (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).mul_const u
  exact (hg.hasDerivAt.comp (t : ℂ) h1).comp_ofReal

/-- The pre-Schwarzian estimate bounds the real logarithmic derivative in every unit
radial direction inside the disc. -/
private theorem radial_logDeriv_bounds (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) {u : ℂ} (hu : ‖u‖ = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (2 * t - 4) / (1 - t ^ 2) ≤
        ((deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)) * u).re ∧
      ((deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)) * u).re ≤
        (2 * t + 4) / (1 - t ^ 2) := by
  set q := deriv (deriv f) ((t : ℂ) * u) / deriv f ((t : ℂ) * u)
  have hpre := norm_one_sub_normSq_mul_deriv_deriv_div_deriv_sub_two_conj_le hf hinj
    (ofReal_mul_mem_ball hu ht0 ht1)
  rw [mul_div_assoc] at hpre
  have hconj : conj ((t : ℂ) * u) * u = (t : ℂ) := by
    rw [map_mul, conj_ofReal, mul_assoc, mul_comm (conj u) u, mul_conj', hu]
    push_cast; ring
  have hnormsq : normSq ((t : ℂ) * u) = t ^ 2 := by
    rw [normSq_eq_norm_sq, norm_ofReal_mul_of_norm_eq_one hu ht0]
  have hrewrite : ((1 - (normSq ((t : ℂ) * u) : ℂ)) * q - 2 * conj ((t : ℂ) * u)) * u =
      (1 - ((t : ℝ) ^ 2 : ℂ)) * (q * u) - 2 * t := by
    rw [hnormsq]
    push_cast
    linear_combination (-2 : ℂ) * hconj
  have hRe : ((1 - ((t : ℝ) ^ 2 : ℂ)) * (q * u) - 2 * t).re = (1 - t ^ 2) * (q * u).re - 2 * t := by
    simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq]
  have hbound : |(1 - t ^ 2) * (q * u).re - 2 * t| ≤ 4 := by
    rw [← hRe]
    refine (abs_re_le_norm _).trans ?_
    rw [← hrewrite, norm_mul, hu, mul_one]
    exact hpre
  rw [abs_le] at hbound
  have hpos : 0 < 1 - t ^ 2 := by nlinarith
  constructor
  · rw [div_le_iff₀ hpos]; nlinarith [hbound.1]
  · rw [le_div_iff₀ hpos]; nlinarith [hbound.2]

/-! ### The Koebe distortion theorem -/

/-- **The Koebe distortion theorem.** For `f` holomorphic and injective on the disc with
`f 0 = 0` and `f' 0 = 1`, `‖f' z‖` is bounded between `(1 - ‖z‖) / (1 + ‖z‖) ^ 3` and
`(1 + ‖z‖) / (1 - ‖z‖) ^ 3`. -/
theorem distortion_le_of_class_S (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (hf1 : deriv f 0 = 1) {z₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) :
    (1 - ‖z₀‖) / (1 + ‖z₀‖) ^ 3 ≤ ‖deriv f z₀‖ ∧
      ‖deriv f z₀‖ ≤ (1 + ‖z₀‖) / (1 - ‖z₀‖) ^ 3 := by
  set r : ℝ := ‖z₀‖
  have hr0 : 0 ≤ r := norm_nonneg z₀
  have hr1 : r < 1 := mem_ball_zero_iff.mp hz₀
  have hU : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
  have hderivfan : AnalyticOnNhd ℂ (deriv f) (ball 0 1) := (hf.analyticOnNhd hU).deriv
  have hderivne : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0 := fun z hz ↦
    deriv_ne_zero_of_injOn hU hf hinj hz
  -- a holomorphic logarithm `L` of `f'` with `L 0 = 0`
  obtain ⟨L, hLan, hLeq, hL0⟩ := exists_analyticOnNhd_logBranch_eq hU
    ((convex_ball 0 1).isSimplyConnected (nonempty_ball.mpr one_pos)) hderivfan.differentiableOn
    hderivne
    (mem_ball_self one_pos) (by rw [hf1, exp_zero])
  -- the ray through `z₀`
  set u : ℂ := exp (arg z₀ * I)
  have hu : ‖u‖ = 1 := norm_exp_ofReal_mul_I _
  have hzru : (r : ℂ) * u = z₀ := norm_mul_exp_arg_mul_I z₀
  have hmem : ∀ t ∈ Icc (0 : ℝ) r, (t : ℂ) * u ∈ ball (0 : ℂ) 1 := fun t ht ↦
    ofReal_mul_mem_ball hu ht.1 (ht.2.trans_lt hr1)
  -- `G t = Re L (t u)` has the radial logarithmic derivative as derivative
  set G : ℝ → ℝ := fun t ↦ (L ((t : ℂ) * u)).re
  set D : ℝ → ℝ := fun t ↦ (deriv L ((t : ℂ) * u) * u).re
  have hG : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt G (D t) t := fun t ht ↦
    reCLM.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_comp_ofReal_mul (hLan _ (hmem t ht)).differentiableAt)
  have hD : ∀ t ∈ Icc (0 : ℝ) r,
      (2 * t - 4) / (1 - t ^ 2) ≤ D t ∧ D t ≤ (2 * t + 4) / (1 - t ^ 2) := by
    intro t ht
    simp only [D]
    rw [deriv_logBranch hU hderivfan.differentiableOn hLan.continuousOn hLeq (hmem t ht)]
    exact radial_logDeriv_bounds hf hinj hu ht.1 (ht.2.trans_lt hr1)
  have hGc : ContinuousOn G (Icc 0 r) := fun t ht ↦ (hG t ht).continuousAt.continuousWithinAt
  have hanti : ∀ t ∈ Icc (0 : ℝ) r, -1 < t ∧ t < 1 := fun t ht ↦
    ⟨by linarith [ht.1], ht.2.trans_lt hr1⟩
  have hUp : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt distortionUpperAnti ((2 * t + 4) / (1 - t ^ 2)) t :=
    fun t ht ↦ hasDerivAt_distortionUpperAnti (hanti t ht).1 (hanti t ht).2
  have hLo : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt distortionLowerAnti ((2 * t - 4) / (1 - t ^ 2)) t :=
    fun t ht ↦ hasDerivAt_distortionLowerAnti (hanti t ht).1 (hanti t ht).2
  have hrmem : r ∈ Icc (0 : ℝ) r := ⟨hr0, le_rfl⟩
  have hG0 : G 0 = 0 := by simp [G, hL0]
  -- compare with the explicit antiderivatives
  have hupper : G r ≤ distortionUpperAnti r :=
    image_le_of_deriv_right_le_deriv_boundary hGc
      (fun t ht ↦ (hG t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (by simp [hG0, distortionUpperAnti])
      (fun t ht ↦ (hUp t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hUp t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht ↦ (hD t (Ico_subset_Icc_self ht)).2) hrmem
  have hlower : distortionLowerAnti r ≤ G r :=
    image_le_of_deriv_right_le_deriv_boundary
      (fun t ht ↦ (hLo t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hLo t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (by simp [hG0, distortionLowerAnti]) hGc
      (fun t ht ↦ (hG t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht ↦ (hD t (Ico_subset_Icc_self ht)).1) hrmem
  -- `G r = log ‖f' z₀‖`
  have hGr : G r = Real.log ‖deriv f z₀‖ := by
    simp only [G, hzru, ← hLeq hz₀, Function.comp_apply, norm_exp, Real.log_exp]
  rw [hGr] at hupper hlower
  have hf'pos : 0 < ‖deriv f z₀‖ := norm_pos_iff.mpr (hderivne z₀ hz₀)
  rw [← exp_distortionLowerAnti hr0 hr1, ← exp_distortionUpperAnti hr0 hr1,
    ← Real.exp_log hf'pos]
  exact ⟨Real.exp_le_exp.mpr hlower, Real.exp_le_exp.mpr hupper⟩

/-! ### The growth theorem (upper bound) -/

/-- **The growth theorem, upper bound.** For `f` holomorphic and injective on the disc with
`f 0 = 0` and `f' 0 = 1`, `‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2`. -/
theorem norm_le_div_one_sub_sq_of_class_S (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) : ‖f z₀‖ ≤ ‖z₀‖ / (1 - ‖z₀‖) ^ 2 := by
  set r : ℝ := ‖z₀‖
  have hr1 : r < 1 := mem_ball_zero_iff.mp hz₀
  set u : ℂ := exp (arg z₀ * I)
  have hu : ‖u‖ = 1 := norm_exp_ofReal_mul_I _
  have hzru : (r : ℂ) * u = z₀ := norm_mul_exp_arg_mul_I z₀
  have hmem : ∀ t ∈ Icc (0 : ℝ) r, (t : ℂ) * u ∈ ball (0 : ℂ) 1 := fun t ht ↦
    ofReal_mul_mem_ball hu ht.1 (ht.2.trans_lt hr1)
  have hderiv : ∀ t ∈ Icc (0 : ℝ) r,
      HasDerivAt (fun s : ℝ ↦ f ((s : ℂ) * u)) (deriv f ((t : ℂ) * u) * u) t := fun t ht ↦
    hasDerivAt_comp_ofReal_mul (hf.differentiableAt (isOpen_ball.mem_nhds (hmem t ht)))
  have hgrow : ∀ t ∈ Icc (0 : ℝ) r, HasDerivAt growthAnti ((1 + t) / (1 - t) ^ 3) t :=
    fun t ht ↦ hasDerivAt_growthAnti (ht.2.trans_lt hr1)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [hf0, growthAnti])
    (fun t ht ↦ (hgrow t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hgrow t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht ↦ by
      have htu := norm_ofReal_mul_of_norm_eq_one hu ht.1
      have := (distortion_le_of_class_S hf hinj hf1 (hmem t (Ico_subset_Icc_self ht))).2
      rw [htu] at this
      rwa [norm_mul, hu, mul_one])
    (⟨norm_nonneg z₀, le_rfl⟩ : r ∈ Icc (0 : ℝ) r)
  rwa [hzru] at key

end Complex

end
