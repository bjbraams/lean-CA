/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Parseval's identity for Taylor coefficients on circles

For a function `f` holomorphic on the disc `‖z‖ < R` with Taylor coefficients
`c n = f⁽ⁿ⁾(0) / n!`, the restriction of `f` to the circle `‖z‖ = r < R` has the uniformly
convergent Fourier expansion `f (r e^{iθ}) = ∑ c n r ^ n e^{i n θ}`. Integrating term by term
gives Cauchy's coefficient formula `∫₀^{2π} e^{-inθ} f (r e^{iθ}) dθ = 2π r ^ n c n` and, for
a second continuous function `G` on the circle, the pairing formula
`∫₀^{2π} conj (f (r e^{iθ})) G θ dθ = ∑ conj (c n) r ^ n ∫₀^{2π} e^{-inθ} G θ dθ`.
Specializing `G` gives Parseval's identity `∫₀^{2π} ‖f (r e^{iθ})‖² dθ = 2π ∑ ‖c n‖² r ^ (2n)`,
Gutzmer's inequality, and the identity `∫₀^{2π} conj (f) (z f') dθ = 2π ∑ n ‖c n‖² r ^ (2n)`
used in the area theorem.

## Main definitions

* `Complex.taylorCoeff f n`: the Taylor coefficient `f⁽ⁿ⁾(0) / n!`.

## Main results

* `Complex.integral_exp_neg_mul_circleMap`: Cauchy's coefficient formula on a circle.
* `Complex.hasSum_conj_taylorCoeff_mul_integral`: the pairing formula.
* `Complex.hasSum_norm_taylorCoeff_sq`: **Parseval's identity**.
* `Complex.tsum_norm_taylorCoeff_sq_le`: **Gutzmer's inequality**.
* `Complex.hasSum_mul_norm_taylorCoeff_sq`: the pairing of `f` with `z f'`.

## References

* R. Remmert, *Theory of Complex Functions*, Chapter 8, §3 (Gutzmer's formula).
-/

@[expose] public noncomputable section

open Set Metric Filter Real intervalIntegral
open scoped Topology

namespace Complex

/-- The `n`-th Taylor coefficient `f⁽ⁿ⁾(0) / n!` of `f` at the origin. -/
def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ := (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

variable {f : ℂ → ℂ} {r R : ℝ}

/-- The circle map centered at the origin. -/
theorem circleMap_zero_eq (r θ : ℝ) : circleMap 0 r θ = r * exp (θ * I) := by
  simp [circleMap]

/-- Points of the circle of radius `r < R` lie in the ball of radius `R`. -/
theorem circleMap_zero_mem_ball (hr : 0 ≤ r) (hrR : r < R) (θ : ℝ) :
    circleMap 0 r θ ∈ ball (0 : ℂ) R := by
  rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_nonneg hr]
  exact hrR

/-- The Taylor series of `f` at a point of the circle of radius `r`. -/
theorem hasSum_taylorCoeff_circleMap (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : 0 ≤ r)
    (hrR : r < R) (θ : ℝ) :
    HasSum (fun n : ℕ => taylorCoeff f n * r ^ n * exp (n * (θ * I)))
      (f (circleMap 0 r θ)) := by
  have h := hasSum_taylorSeries_on_ball hf (circleMap_zero_mem_ball hr hrR θ)
  convert h using 2 with n
  rw [smul_eq_mul, smul_eq_mul, sub_zero, circleMap_zero_eq, mul_pow, ← exp_nat_mul, taylorCoeff]
  ring

/-- **Cauchy's coefficient formula** on the circle of radius `r`: the `n`-th Fourier
coefficient of `θ ↦ f (r e^{iθ})` is `r ^ n` times the `n`-th Taylor coefficient. -/
theorem integral_exp_neg_mul_circleMap (hf : DifferentiableOn ℂ f (closedBall 0 r)) (hr : 0 < r)
    (n : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (-(n * (θ * I))) * f (circleMap 0 r θ) =
      2 * π * r ^ n * taylorCoeff f n := by
  have h := hf.circleIntegral_one_div_sub_center_pow_smul hr n
  rw [circleIntegral] at h
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hI : ∀ θ : ℝ, exp (-(n * (θ * I))) * f (circleMap 0 r θ) =
      ((r : ℂ) ^ n / I) * (deriv (circleMap 0 r) θ •
        (1 / (circleMap 0 r θ - 0) ^ (n + 1)) • f (circleMap 0 r θ)) := by
    intro θ
    rw [deriv_circleMap, smul_eq_mul, smul_eq_mul, sub_zero, circleMap_zero_eq, exp_neg,
      exp_nat_mul]
    have he : exp (θ * I) ≠ 0 := exp_ne_zero _
    field_simp
    ring
  simp_rw [hI]
  rw [integral_const_mul, h, taylorCoeff, smul_eq_mul]
  field_simp

/-- **The mean value property** on the circle of radius `r`. -/
theorem integral_circleMap_eq_two_pi_mul (hf : DifferentiableOn ℂ f (closedBall 0 r))
    (hr : 0 < r) : ∫ θ in (0 : ℝ)..2 * π, f (circleMap 0 r θ) = 2 * π * f 0 := by
  have h := integral_exp_neg_mul_circleMap hf hr 0
  simp only [Nat.cast_zero, zero_mul, neg_zero, exp_zero, one_mul, pow_zero, mul_one,
    taylorCoeff, Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero] at h
  exact h

/-- The Fourier integral of a nontrivial character over a period vanishes. -/
theorem integral_exp_neg_mul (n : ℕ) (hn : n ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, exp (-(n * (θ * I))) = 0 := by
  have hc : -((n : ℂ) * I) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (Nat.cast_ne_zero.mpr hn) I_ne_zero)
  have hpt : ∀ θ : ℝ, exp (-(n * (θ * I))) = exp (-((n : ℂ) * I) * θ) := fun θ => by
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_exp_mul_complex hc]
  have : exp (-((n : ℂ) * I) * ((2 * π : ℝ) : ℂ)) = 1 := by
    rw [show -((n : ℂ) * I) * ((2 * π : ℝ) : ℂ) = -((n : ℂ) * (2 * π * I)) by push_cast; ring,
      exp_neg, exp_nat_mul_two_pi_mul_I, inv_one]
  rw [this]
  simp

/-- The zeroth Taylor coefficient is the value at the origin. -/
@[simp] theorem taylorCoeff_zero (f : ℂ → ℂ) : taylorCoeff f 0 = f 0 := by
  simp [taylorCoeff]

/-- The first Taylor coefficient is the derivative at the origin. -/
@[simp] theorem taylorCoeff_one (f : ℂ → ℂ) : taylorCoeff f 1 = deriv f 0 := by
  simp [taylorCoeff]

/-- Taylor coefficients are additive. -/
theorem taylorCoeff_add {g : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R))
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hR : 0 < R) (n : ℕ) :
    taylorCoeff (fun z => f z + g z) n = taylorCoeff f n + taylorCoeff g n := by
  have hr : 0 < R / 2 := by positivity
  have hsub : closedBall (0 : ℂ) (R / 2) ⊆ ball 0 R := closedBall_subset_ball (by linarith)
  have h1 := integral_exp_neg_mul_circleMap (hf.mono hsub) hr n
  have h2 := integral_exp_neg_mul_circleMap (hg.mono hsub) hr n
  have h3 := integral_exp_neg_mul_circleMap (f := fun z => f z + g z) ((hf.add hg).mono hsub) hr n
  have hmem := circleMap_zero_mem_ball hr.le (by linarith : R / 2 < R)
  have hfc : Continuous fun θ : ℝ => exp (-(n * (θ * I))) * f (circleMap 0 (R / 2) θ) :=
    (by fun_prop : Continuous fun θ : ℝ => exp (-(n * (θ * I)))).mul
      (hf.continuousOn.comp_continuous (continuous_circleMap _ _) hmem)
  have hgc : Continuous fun θ : ℝ => exp (-(n * (θ * I))) * g (circleMap 0 (R / 2) θ) :=
    (by fun_prop : Continuous fun θ : ℝ => exp (-(n * (θ * I)))).mul
      (hg.continuousOn.comp_continuous (continuous_circleMap _ _) hmem)
  rw [integral_congr (fun θ _ => mul_add _ _ _),
    integral_add (hfc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _), h1, h2] at h3
  have hne : (2 * π * ((R / 2 : ℝ) : ℂ) ^ n) ≠ 0 := by
    have : ((R / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    exact mul_ne_zero h2π (pow_ne_zero _ this)
  have := h3.symm
  rw [← mul_add] at this
  exact mul_left_cancel₀ hne this

/-- The Taylor coefficients of the divided difference `dslope f 0` are those of `f`, shifted by
one. -/
theorem taylorCoeff_dslope_zero (hf : DifferentiableOn ℂ f (ball 0 R)) (hR : 0 < R) (n : ℕ) :
    taylorCoeff (dslope f 0) n = taylorCoeff f (n + 1) := by
  have hr : 0 < R / 2 := by positivity
  have hr' : ((R / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsub : closedBall (0 : ℂ) (R / 2) ⊆ ball 0 R := closedBall_subset_ball (by linarith)
  have hp : DifferentiableOn ℂ (dslope f 0) (ball 0 R) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hR))).mpr hf
  have h1 := integral_exp_neg_mul_circleMap (hp.mono hsub) hr n
  have h2 := integral_exp_neg_mul_circleMap (hf.mono hsub) hr (n + 1)
  have h3 := integral_exp_neg_mul (n + 1) n.succ_ne_zero
  have hmem := circleMap_zero_mem_ball hr.le (by linarith : R / 2 < R)
  have hcm : ∀ θ : ℝ, circleMap 0 (R / 2) θ ≠ 0 := fun θ => circleMap_ne_center hr.ne'
  have hpt : ∀ θ : ℝ, exp (-(n * (θ * I))) * dslope f 0 (circleMap 0 (R / 2) θ) =
      ((R / 2 : ℝ) : ℂ)⁻¹ * (exp (-((n + 1 : ℕ) * (θ * I))) * f (circleMap 0 (R / 2) θ) -
        f 0 * exp (-((n + 1 : ℕ) * (θ * I)))) := by
    intro θ
    rw [dslope_of_ne _ (hcm θ), slope_def_field, sub_zero, circleMap_zero_eq]
    have he : exp (θ * I) ≠ 0 := exp_ne_zero _
    have hexp : exp (-((n + 1 : ℕ) * (θ * I))) = exp (-(n * (θ * I))) * (exp (θ * I))⁻¹ := by
      rw [← exp_neg, ← exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    field_simp
  have hfc : Continuous fun θ : ℝ => exp (-((n + 1 : ℕ) * (θ * I))) * f (circleMap 0 (R / 2) θ) :=
    (by fun_prop : Continuous fun θ : ℝ => exp (-((n + 1 : ℕ) * (θ * I)))).mul
      (hf.continuousOn.comp_continuous (continuous_circleMap _ _) hmem)
  rw [integral_congr (fun θ _ => hpt θ), integral_const_mul,
    integral_sub (hfc.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => f 0 * exp (-((n + 1 : ℕ) * (θ * I)))).intervalIntegrable
      _ _), h2, integral_const_mul, h3, mul_zero, sub_zero] at h1
  have hne : (2 * π * ((R / 2 : ℝ) : ℂ) ^ n) ≠ 0 := by
    have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    exact mul_ne_zero h2π (pow_ne_zero _ hr')
  refine mul_left_cancel₀ hne ?_
  rw [← h1, pow_succ]
  field_simp

/-- Multiplying by `z ^ m` shifts the Taylor coefficients by `m`. -/
theorem taylorCoeff_pow_mul {K : ℂ → ℂ} (hK : DifferentiableOn ℂ K (ball 0 R)) (hR : 0 < R)
    (m n : ℕ) : taylorCoeff (fun z => z ^ m * K z) (n + m) = taylorCoeff K n := by
  have hr : 0 < R / 2 := by positivity
  have hr' : ((R / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsub : closedBall (0 : ℂ) (R / 2) ⊆ ball 0 R := closedBall_subset_ball (by linarith)
  have h1 := integral_exp_neg_mul_circleMap (f := fun z => z ^ m * K z)
    (((differentiableOn_pow m).mul hK).mono hsub) hr (n + m)
  have h2 := integral_exp_neg_mul_circleMap (hK.mono hsub) hr n
  have hpt : ∀ θ : ℝ, exp (-((n + m : ℕ) * (θ * I))) *
      (circleMap 0 (R / 2) θ ^ m * K (circleMap 0 (R / 2) θ)) =
      ((R / 2 : ℝ) : ℂ) ^ m * (exp (-(n * (θ * I))) * K (circleMap 0 (R / 2) θ)) := by
    intro θ
    rw [circleMap_zero_eq, mul_pow, ← exp_nat_mul]
    have hexp : exp (-((n + m : ℕ) * (θ * I))) =
        exp (-(n * (θ * I))) * (exp (m * (θ * I)))⁻¹ := by
      rw [← exp_neg, ← exp_add]
      congr 1
      push_cast
      ring
    have he : exp (m * (θ * I)) ≠ 0 := exp_ne_zero _
    rw [hexp]
    field_simp
  rw [integral_congr (fun θ _ => hpt θ), integral_const_mul, h2] at h1
  have hne : (2 * π * ((R / 2 : ℝ) : ℂ) ^ (n + m)) ≠ 0 := by
    have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    exact mul_ne_zero h2π (pow_ne_zero _ hr')
  refine mul_left_cancel₀ hne ?_
  rw [← h1, pow_add]
  ring

/-- The Taylor coefficients of `f` are summable against `r ^ n` for `r` below the radius. -/
theorem summable_norm_taylorCoeff_mul_pow (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : 0 ≤ r)
    (hrR : r < R) : Summable fun n : ℕ => ‖taylorCoeff f n‖ * r ^ n := by
  obtain ⟨r', hrr', hr'R⟩ := exists_between hrR
  have hr'0 : 0 < r' := hr.trans_lt hrr'
  have hz : (r' : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos hr'0]
    exact hr'R
  have hsum := hasSum_taylorSeries_on_ball hf hz
  have hterm : Tendsto (fun n : ℕ =>
      ‖(n.factorial : ℂ)⁻¹ • ((r' : ℂ) - 0) ^ n • iteratedDeriv n f 0‖) atTop (𝓝 0) := by
    simpa using hsum.summable.tendsto_atTop_zero.norm
  obtain ⟨C, hC⟩ := hterm.bddAbove_range
  have hCn : ∀ n : ℕ, ‖taylorCoeff f n‖ * r' ^ n ≤ C := by
    intro n
    have := hC (mem_range_self n)
    rw [sub_zero, smul_eq_mul, smul_eq_mul, norm_mul, norm_mul, norm_pow, norm_inv,
      norm_natCast, norm_real, Real.norm_eq_abs, abs_of_pos hr'0] at this
    unfold taylorCoeff
    rw [norm_mul, norm_inv, norm_natCast]
    calc (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f 0‖ * r' ^ n
        = (n.factorial : ℝ)⁻¹ * (r' ^ n * ‖iteratedDeriv n f 0‖) := by ring
      _ ≤ C := this
  have hq : 0 ≤ r / r' := div_nonneg hr hr'0.le
  have hq1 : r / r' < 1 := (div_lt_one hr'0).mpr hrr'
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_of_lt_one hq hq1).mul_left C)
  calc ‖taylorCoeff f n‖ * r ^ n = ‖taylorCoeff f n‖ * r' ^ n * (r / r') ^ n := by
        rw [div_pow, mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ hr'0.ne')]
    _ ≤ C * (r / r') ^ n := by gcongr; exact hCn n

/-- **The pairing formula.** The integral of `conj f` against a continuous function `G` on the
circle is the sum of the conjugate Taylor coefficients against the Fourier coefficients of
`G`. -/
theorem hasSum_conj_taylorCoeff_mul_integral {G : ℝ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R))
    (hr : 0 ≤ r) (hrR : r < R) (hG : Continuous G) :
    HasSum (fun n : ℕ => (starRingEnd ℂ) (taylorCoeff f n) * r ^ n *
        ∫ θ in (0 : ℝ)..2 * π, exp (-(n * (θ * I))) * G θ)
      (∫ θ in (0 : ℝ)..2 * π, (starRingEnd ℂ) (f (circleMap 0 r θ)) * G θ) := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ θ ∈ uIcc (0 : ℝ) (2 * π), ‖G θ‖ ≤ M :=
    isCompact_uIcc.exists_bound_of_continuousOn hG.continuousOn
  have hsum := summable_norm_taylorCoeff_mul_pow hf hr hrR
  have hconj : ∀ (n : ℕ) (θ : ℝ), (starRingEnd ℂ) (n * (θ * I) : ℂ) = -(n * (θ * I)) := by
    intro n θ
    rw [map_mul, map_mul, map_natCast, conj_ofReal, conj_I]
    ring
  have hpt : ∀ θ : ℝ, HasSum (fun n : ℕ => (starRingEnd ℂ) (taylorCoeff f n) * r ^ n *
      (exp (-(n * (θ * I))) * G θ)) ((starRingEnd ℂ) (f (circleMap 0 r θ)) * G θ) := by
    intro θ
    have h := (hasSum_conj'.mpr (hasSum_taylorCoeff_circleMap hf hr hrR θ)).mul_right (G θ)
    convert h using 2 with n
    rw [map_mul, map_mul, ← exp_conj, hconj, map_pow, conj_ofReal]
    ring
  have hnorm : ∀ (n : ℕ) (θ : ℝ), ‖exp (-(n * (θ * I)))‖ = 1 := by
    intro n θ
    rw [norm_exp]
    simp
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * π)
    (F := fun (n : ℕ) (θ : ℝ) => (starRingEnd ℂ) (taylorCoeff f n) * r ^ n *
      (exp (-(n * (θ * I))) * G θ))
    (bound := fun n _ => ‖taylorCoeff f n‖ * r ^ n * M)
    (fun n => (by fun_prop : Continuous fun θ : ℝ => (starRingEnd ℂ) (taylorCoeff f n) * r ^ n *
      (exp (-(n * (θ * I))) * G θ)).aestronglyMeasurable)
    (fun n => MeasureTheory.ae_of_all _ fun θ hθ => ?_)
    (MeasureTheory.ae_of_all _ fun θ _ => hsum.mul_right M)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ => hpt θ)
  · simp_rw [integral_const_mul] at hdom
    exact hdom
  · rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, norm_pow, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr, hnorm, one_mul]
    gcongr
    exact hM θ (uIoc_subset_uIcc hθ)

/-- Integration by parts on the circle: the Fourier coefficients of `θ ↦ (z f') (r e^{iθ})`
are `n` times those of `θ ↦ f (r e^{iθ})`. -/
theorem integral_exp_neg_mul_circleMap_mul_deriv (hf : DifferentiableOn ℂ f (ball 0 R))
    (hr : 0 < r) (hrR : r < R) (n : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (-(n * (θ * I))) *
        (circleMap 0 r θ * deriv f (circleMap 0 r θ)) =
      n * ∫ θ in (0 : ℝ)..2 * π, exp (-(n * (θ * I))) * f (circleMap 0 r θ) := by
  have hmem := circleMap_zero_mem_ball hr.le hrR
  have hfd : ∀ θ : ℝ, HasDerivAt f (deriv f (circleMap 0 r θ)) (circleMap 0 r θ) := fun θ =>
    (hf.differentiableAt (isOpen_ball.mem_nhds (hmem θ))).hasDerivAt
  have hderiv : ContinuousOn (deriv f) (ball 0 R) :=
    (hf.analyticOnNhd isOpen_ball).deriv.continuousOn
  have hu : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), HasDerivAt (fun θ : ℝ => exp (-(n * (θ * I))))
      (-(n * I) * exp (-(n * (θ * I)))) θ := by
    intro θ _
    have h := ((hasDerivAt_id θ).ofReal_comp.const_mul (-(n * I))).cexp
    have h1 : (fun y : ℝ => exp (-(n * I) * ((id y : ℝ) : ℂ))) =
        fun θ : ℝ => exp (-(n * (θ * I))) := by
      funext y
      simp only [id]
      congr 1
      ring
    rw [h1] at h
    refine h.congr_deriv ?_
    simp only [id, ofReal_one]
    rw [show -(n * I) * (θ : ℂ) = -(n * (θ * I)) by ring]
    ring
  have hv : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), HasDerivAt (fun θ : ℝ => f (circleMap 0 r θ))
      (deriv f (circleMap 0 r θ) * (circleMap 0 r θ * I)) θ := fun θ _ =>
    (hfd θ).comp θ (hasDerivAt_circleMap 0 r θ)
  have hcont : Continuous fun θ : ℝ => deriv f (circleMap 0 r θ) :=
    hderiv.comp_continuous (continuous_circleMap 0 r) hmem
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv
    ((by fun_prop : Continuous fun θ : ℝ => -(n * I) * exp (-(n * (θ * I)))).intervalIntegrable
      _ _)
    ((by fun_prop : Continuous fun θ : ℝ => deriv f (circleMap 0 r θ) *
      (circleMap 0 r θ * I)).intervalIntegrable _ _)
  have hper : circleMap 0 r (2 * π) = circleMap 0 r 0 := by
    have := periodic_circleMap 0 r 0
    rwa [zero_add] at this
  have hexp : exp (-(n * (((2 * π : ℝ) : ℂ) * I))) = 1 := by
    rw [exp_neg, exp_nat_mul]
    push_cast
    rw [exp_two_pi_mul_I, one_pow, inv_one]
  rw [hper, hexp] at hibp
  simp only [ofReal_zero, zero_mul, mul_zero, neg_zero, exp_zero, one_mul, sub_self, zero_sub]
    at hibp
  have hI : ∀ θ : ℝ, exp (-(n * (θ * I))) * (circleMap 0 r θ * deriv f (circleMap 0 r θ)) =
      -I * (exp (-(n * (θ * I))) * (deriv f (circleMap 0 r θ) * (circleMap 0 r θ * I))) := by
    intro θ
    linear_combination
      (exp (-(n * (θ * I))) * circleMap 0 r θ * deriv f (circleMap 0 r θ)) * I_sq
  simp_rw [hI]
  rw [integral_const_mul, hibp]
  have h2 : ∀ θ : ℝ, -(n * I) * exp (-(n * (θ * I))) * f (circleMap 0 r θ) =
      -(n * I) * (exp (-(n * (θ * I))) * f (circleMap 0 r θ)) := fun θ => mul_assoc _ _ _
  simp_rw [h2]
  rw [integral_const_mul]
  linear_combination
    (-(n * ∫ θ in (0 : ℝ)..2 * π, exp (-(n * (θ * I))) * f (circleMap 0 r θ))) * I_sq

/-- **Parseval's identity** for the Taylor coefficients on the circle of radius `r`. -/
theorem hasSum_norm_taylorCoeff_sq (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : 0 < r)
    (hrR : r < R) :
    HasSum (fun n : ℕ => 2 * π * (‖taylorCoeff f n‖ ^ 2 * r ^ (2 * n)))
      (∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap 0 r θ)‖ ^ 2) := by
  have hmem := circleMap_zero_mem_ball hr.le hrR
  have hG : Continuous fun θ : ℝ => f (circleMap 0 r θ) :=
    hf.continuousOn.comp_continuous (continuous_circleMap 0 r) hmem
  have hcl : DifferentiableOn ℂ f (closedBall 0 r) := hf.mono (closedBall_subset_ball hrR)
  have h := hasSum_conj_taylorCoeff_mul_integral hf hr.le hrR hG
  simp_rw [integral_exp_neg_mul_circleMap hcl hr] at h
  have h2 : (∫ θ in (0 : ℝ)..2 * π, (starRingEnd ℂ) (f (circleMap 0 r θ)) * f (circleMap 0 r θ)) =
      ((∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap 0 r θ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    funext θ
    rw [conj_mul']
    push_cast
    ring
  have h3 : ∀ n : ℕ, (starRingEnd ℂ) (taylorCoeff f n) * r ^ n * (2 * π * r ^ n * taylorCoeff f n) =
      ((2 * π * (‖taylorCoeff f n‖ ^ 2 * r ^ (2 * n)) : ℝ) : ℂ) := by
    intro n
    rw [show (starRingEnd ℂ) (taylorCoeff f n) * r ^ n * (2 * π * r ^ n * taylorCoeff f n) =
      2 * π * (((starRingEnd ℂ) (taylorCoeff f n) * taylorCoeff f n) * ((r : ℂ) ^ n) ^ 2) by ring,
      conj_mul', pow_mul']
    push_cast
    ring
  simp_rw [h3, h2] at h
  exact hasSum_ofReal.mp h

/-- **Gutzmer's inequality**: if `‖f‖ ≤ M` on the circle of radius `r`, then
`∑ ‖c n‖² r ^ (2n) ≤ M²`. -/
theorem tsum_norm_taylorCoeff_sq_le (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : 0 < r)
    (hrR : r < R) {M : ℝ} (hM : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ M) :
    ∑' n : ℕ, ‖taylorCoeff f n‖ ^ 2 * r ^ (2 * n) ≤ M ^ 2 := by
  have hmem := circleMap_zero_mem_ball hr.le hrR
  have hsph : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ =>
    circleMap_mem_sphere 0 hr.le θ
  have hpi : (2 * π)⁻¹ * (2 * π) = 1 := inv_mul_cancel₀ (by positivity)
  have h : HasSum (fun n : ℕ => ‖taylorCoeff f n‖ ^ 2 * r ^ (2 * n))
      ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap 0 r θ)‖ ^ 2) := by
    convert (hasSum_norm_taylorCoeff_sq hf hr hrR).mul_left (2 * π)⁻¹ using 2 with n
    rw [← mul_assoc, hpi, one_mul]
  rw [h.tsum_eq]
  have hG : Continuous fun θ : ℝ => f (circleMap 0 r θ) :=
    hf.continuousOn.comp_continuous (continuous_circleMap 0 r) hmem
  have hint : ∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap 0 r θ)‖ ^ 2 ≤
      ∫ _ in (0 : ℝ)..2 * π, M ^ 2 := by
    refine integral_mono_on (by positivity) ((hG.norm.pow 2).intervalIntegrable _ _)
      intervalIntegrable_const fun θ _ => ?_
    have h1 := hM _ (hsph θ)
    have h0 := norm_nonneg (f (circleMap 0 r θ))
    nlinarith
  rw [integral_const, sub_zero, smul_eq_mul] at hint
  calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖f (circleMap 0 r θ)‖ ^ 2
      ≤ (2 * π)⁻¹ * (2 * π * M ^ 2) := by gcongr
    _ = M ^ 2 := by rw [← mul_assoc, hpi, one_mul]

/-- The pairing of `f` with `z f'` on the circle of radius `r`:
`∫₀^{2π} conj (f) (z f') dθ = 2π ∑ n ‖c n‖² r ^ (2n)`. -/
theorem hasSum_mul_norm_taylorCoeff_sq (hf : DifferentiableOn ℂ f (ball 0 R)) (hr : 0 < r)
    (hrR : r < R) :
    HasSum (fun n : ℕ => ((2 * π * (n * (‖taylorCoeff f n‖ ^ 2 * r ^ (2 * n))) : ℝ) : ℂ))
      (∫ θ in (0 : ℝ)..2 * π, (starRingEnd ℂ) (f (circleMap 0 r θ)) *
        (circleMap 0 r θ * deriv f (circleMap 0 r θ))) := by
  have hmem := circleMap_zero_mem_ball hr.le hrR
  have hderiv : ContinuousOn (deriv f) (ball 0 R) :=
    (hf.analyticOnNhd isOpen_ball).deriv.continuousOn
  have hG : Continuous fun θ : ℝ => circleMap 0 r θ * deriv f (circleMap 0 r θ) :=
    (continuous_circleMap 0 r).mul (hderiv.comp_continuous (continuous_circleMap 0 r) hmem)
  have hcl : DifferentiableOn ℂ f (closedBall 0 r) := hf.mono (closedBall_subset_ball hrR)
  have h := hasSum_conj_taylorCoeff_mul_integral hf hr.le hrR hG
  simp_rw [integral_exp_neg_mul_circleMap_mul_deriv hf hr hrR,
    integral_exp_neg_mul_circleMap hcl hr] at h
  convert h using 2 with n
  rw [show (starRingEnd ℂ) (taylorCoeff f n) * r ^ n * (n * (2 * π * r ^ n * taylorCoeff f n)) =
    2 * π * (n * (((starRingEnd ℂ) (taylorCoeff f n) * taylorCoeff f n) * ((r : ℂ) ^ n) ^ 2))
    by ring, conj_mul', pow_mul']
  push_cast
  ring

/-- The weighted squares `n ‖c n‖² r ^ (2n)` of the Taylor coefficients are summable. -/
theorem summable_mul_norm_taylorCoeff_sq_mul_pow (hf : DifferentiableOn ℂ f (ball 0 R))
    (hr : 0 < r) (hrR : r < R) :
    Summable fun n : ℕ => (n : ℝ) * (‖taylorCoeff f n‖ ^ 2 * r ^ (2 * n)) := by
  have h := (summable_ofReal.mp (hasSum_mul_norm_taylorCoeff_sq hf hr hrR).summable).mul_left
    (2 * π)⁻¹
  refine h.congr fun n => ?_
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end Complex

end
