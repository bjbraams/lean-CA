/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.PathConnected

/-!
# The Gamma integral with a complex Laplace parameter

For `0 < re a` and `0 < re w`, the integral on the positive real axis of
`y ^ (a - 1) * exp (-y * w)` is `w ^ (-a) * Gamma a`, with the principal power.

This module supplies the kernel's norm, continuity and integrability, differentiation
under the integral in the decay rate, and holomorphy on the right half-plane.
The positive-real-rate evaluation is Mathlib's `integral_cpow_mul_exp_neg_mul_Ioi`.
All declarations are independent of simplex measures and special-function applications.

## Main results

* `Complex.norm_cpow_mul_exp_neg_mul`: Pointwise norm of the complex-rate Gamma kernel.
* `Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi`: Integrability of the complex-rate Gamma
  kernel on `(0, ∞)`.
* `Complex.hasDerivAt_integral_cpow_mul_exp_neg_mul_Ioi`: The Laplace kernel is holomorphic in
  the decay rate throughout the right half-plane.
* `Complex.analyticOnNhd_integral_cpow_mul_exp_neg_mul_Ioi`: For an integrable power at zero,
  the Gamma/Laplace integral is holomorphic in the complex decay rate on the open right
  half-plane.
* `Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`: The Gamma/Laplace integral for a decay
  rate with positive real part, evaluated using the principal complex power.

## References

* `Mathlib.Analysis.Calculus.ParametricIntegral`: formal background used by this module.
* `Mathlib.Analysis.Complex.Convex`: formal background used by this module.
* `Mathlib.Analysis.Complex.HalfPlane`: formal background used by this module.
-/

public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Complex

/-- Pointwise norm of the complex-rate Gamma kernel. -/
theorem norm_cpow_mul_exp_neg_mul {a w : ℂ} {y : ℝ} (hy : 0 < y) :
    ‖(y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w)‖ =
      Real.exp (-w.re * y) * y ^ (a.re - 1) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, sub_re, one_re,
    Complex.norm_exp]
  have hre : (-(y : ℂ) * w).re = -w.re * y := by
    simp [mul_re, mul_comm]
  rw [hre]
  ring

/-- The integrand of `integral_cpow_mul_exp_neg_mul_Ioi` is integrable. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi_ofReal {a : ℂ} {r : ℝ}
    (ha : 0 < a.re) (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (a - 1) * exp (-(r * y))) (Set.Ioi 0) := by
  have hval := integral_cpow_mul_exp_neg_mul_Ioi (a := a) (r := r) ha hr
  by_contra h
  have hz : (∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (a - 1) * exp (-(r * y))) = 0 :=
    integral_undef h
  have hne : (1 / r : ℂ) ^ a * Gamma a ≠ 0 := by
    refine mul_ne_zero ?_ (Gamma_ne_zero_of_re_pos ha)
    exact cpow_ne_zero_iff.mpr (Or.inl (one_div_ne_zero (ofReal_ne_zero.mpr hr.ne')))
  exact hne (hval ▸ hz)

/-- Continuity of the complex-rate Gamma kernel on `(0, ∞)`. -/
theorem continuousOn_cpow_mul_exp_neg_mul_Ioi (a w : ℂ) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w))
      (Set.Ioi (0 : ℝ)) := by
  intro y hy
  refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
  · exact (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hy)).comp
      continuous_ofReal.continuousAt
  · exact continuous_exp.continuousAt.comp
      (((continuous_neg.comp continuous_ofReal).mul continuous_const).continuousAt)

/-- Integrability of the complex-rate Gamma kernel on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi {a w : ℂ}
    (ha : 0 < a.re) (hw : 0 < w.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w))
      (Set.Ioi (0 : ℝ)) := by
  have hreal := integrableOn_cpow_mul_exp_neg_mul_Ioi_ofReal (a := a) (r := w.re) ha hw
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (continuousOn_cpow_mul_exp_neg_mul_Ioi a w).aestronglyMeasurable measurableSet_Ioi
  refine Integrable.mono' (μ := volume.restrict (Set.Ioi (0 : ℝ))) hreal.norm hmeas ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
  have hypos : 0 < y := hy
  have hrealnorm :
      ‖(y : ℂ) ^ (a - 1) * exp (-(w.re * y))‖ =
        Real.exp (-w.re * y) * y ^ (a.re - 1) := by
    simpa [mul_comm (y : ℂ)] using
      (norm_cpow_mul_exp_neg_mul (a := a) (w := (w.re : ℂ)) hypos)
  rw [norm_cpow_mul_exp_neg_mul hypos, hrealnorm]

/-- The Laplace kernel is holomorphic in the decay rate throughout the right half-plane. -/
theorem hasDerivAt_integral_cpow_mul_exp_neg_mul_Ioi {a w : ℂ}
    (ha : 0 < a.re) (hw : 0 < w.re) :
    HasDerivAt
      (fun w' => ∫ y : ℝ in Set.Ioi (0 : ℝ),
        (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w'))
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
        -((y : ℂ) * ((y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w)))) w := by
  let r : ℝ := w.re / 2
  let s : Set ℂ := {w' | r < w'.re}
  have hδ : 0 < r := half_pos hw
  have hs : s ∈ 𝓝 w :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (half_lt_self hw)
  let F : ℂ → ℝ → ℂ := fun w' y =>
    (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w')
  let F' : ℂ → ℝ → ℂ := fun w' y =>
    -((y : ℂ) * ((y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w')))
  let bound : ℝ → ℝ := fun y =>
    ‖(y : ℂ) ^ (((a.re : ℂ) + 1) - 1) * exp (-(r * y))‖
  have hF_meas : ∀ᶠ w' in 𝓝 w, AEStronglyMeasurable (F w')
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    filter_upwards [(isOpen_re_gt 0).eventually_mem hw] with w' hw'
    exact (integrableOn_cpow_mul_exp_neg_mul_Ioi ha hw').1
  have hinter := integrableOn_cpow_mul_exp_neg_mul_Ioi_ofReal
      (a := (a.re : ℂ) + 1) (r := r) (add_pos ha zero_lt_one) hδ
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hinter.norm
  have hF'_meas : AEStronglyMeasurable (F' w)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro y hy
    have hypos : 0 < y := hy
    refine ContinuousAt.continuousWithinAt (ContinuousAt.neg (ContinuousAt.mul ?_ ?_))
    · exact continuous_ofReal.continuousAt
    · exact (continuousOn_cpow_mul_exp_neg_mul_Ioi a w y hy).continuousAt
        (isOpen_Ioi.mem_nhds hypos)
  have hbound : ∀ᵐ y : ℝ ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ w' ∈ s,
      ‖F' w' y‖ ≤ bound y := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy w' hw'
    have hypos : 0 < y := hy
    have hle : r ≤ w'.re := le_of_lt hw'
    have hy1 : y * y ^ (a.re - 1) = y ^ a.re := by
      simpa [Real.rpow_one] using (Real.rpow_add hypos 1 (a.re - 1)).symm
    have hre : (((a.re : ℂ) + 1) - 1).re = a.re := by simp
    have hLHS :
        ‖F' w' y‖ = Real.exp (-w'.re * y) * y ^ a.re := by
      unfold F'
      rw [norm_neg, norm_mul, norm_cpow_mul_exp_neg_mul (a := a) (w := w') hypos]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hypos.le]
      calc
        y * (Real.exp (-w'.re * y) * y ^ (a.re - 1)) =
            Real.exp (-w'.re * y) * (y * y ^ (a.re - 1)) := by ring
        _ = Real.exp (-w'.re * y) * y ^ a.re := by rw [hy1]
    have hRHS :
        bound y = Real.exp (-r * y) * y ^ a.re := by
      simp only [bound, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hypos, hre, Complex.norm_exp]
      simp [mul_comm]
    rw [hLHS, hRHS]
    gcongr
  have hdiff : ∀ᵐ y : ℝ ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ w' ∈ s,
      HasDerivAt (F · y) (F' w' y) w' := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy w' hw'
    have harg : HasDerivAt (fun w'' : ℂ => -(y : ℂ) * w'') (-(y : ℂ)) w' :=
      hasDerivAt_const_mul (-(y : ℂ))
    have hexp : HasDerivAt (fun w'' : ℂ => exp (-(y : ℂ) * w''))
        (exp (-(y : ℂ) * w') * (-(y : ℂ))) w' :=
      (Complex.hasDerivAt_exp _).comp w' harg
    refine (hexp.const_mul ((y : ℂ) ^ (a - 1))).congr_deriv ?_
    simp [F', mul_comm, mul_assoc, mul_neg, neg_mul]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (F := F) (F' := F') (bound := bound)
      hs hF_meas (integrableOn_cpow_mul_exp_neg_mul_Ioi ha hw)
      hF'_meas hbound hbound_int hdiff).2

/-- For an integrable power at zero, the Gamma/Laplace integral is holomorphic in the
complex decay rate on the open right half-plane. -/
theorem analyticOnNhd_integral_cpow_mul_exp_neg_mul_Ioi {a : ℂ} (ha : 0 < a.re) :
    AnalyticOnNhd ℂ
      (fun w : ℂ => ∫ y : ℝ in Set.Ioi (0 : ℝ),
        (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w)) {w | 0 < w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_re_gt 0)
  intro w hw
  exact (hasDerivAt_integral_cpow_mul_exp_neg_mul_Ioi ha hw).differentiableAt.differentiableWithinAt

/-- The Gamma/Laplace integral for a decay rate with positive real part, evaluated using
the principal complex power. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos {a w : ℂ}
    (ha : 0 < a.re) (hw : 0 < w.re) :
    ∫ y : ℝ in Set.Ioi (0 : ℝ), (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w) =
      w ^ (-a) * Gamma a := by
  let Ω : Set ℂ := {w | 0 < w.re}
  have hΩpre : IsPreconnected Ω := (convex_halfSpace_re_gt 0).isPreconnected
  let F : ℂ → ℂ := fun w' =>
    ∫ y : ℝ in Set.Ioi (0 : ℝ), (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * w')
  let G : ℂ → ℂ := fun w' => w' ^ (-a) * Gamma a
  have hF : AnalyticOnNhd ℂ F Ω := analyticOnNhd_integral_cpow_mul_exp_neg_mul_Ioi ha
  have hG : AnalyticOnNhd ℂ G Ω := by
    intro w' hw'
    have hwslit : w' ∈ slitPlane :=
      mem_slitPlane_iff.mpr (Or.inl hw')
    exact (AnalyticAt.cpow analyticAt_id analyticAt_const hwslit).mul analyticAt_const
  have hpos : (1 : ℂ) ∈ Ω := by simp [Ω]
  refine hF.eqOn_of_preconnected_of_frequently_eq hG hΩpre hpos ?_ hw
  have hseq : Tendsto (fun n : ℕ => ((1 + (n + 1 : ℝ)⁻¹ : ℝ) : ℂ))
      atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hr : Tendsto (fun n : ℕ => (1 + (n + 1 : ℝ)⁻¹ : ℝ)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    · filter_upwards with n hn
      have : (1 + (n + 1 : ℝ)⁻¹ : ℝ) = 1 := Complex.ofReal_injective hn
      have : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
      linarith
  refine hseq.frequently (Frequently.of_forall fun n => ?_)
  let r : ℝ := 1 + (n + 1 : ℝ)⁻¹
  have hr : 0 < r := by positivity
  have hreal := integral_cpow_mul_exp_neg_mul_Ioi (a := a) (r := r) ha hr
  have hcongr :
      (∫ y : ℝ in Set.Ioi (0 : ℝ),
          (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * (r : ℂ))) =
        ∫ y : ℝ in Set.Ioi (0 : ℝ),
          (y : ℂ) ^ (a - 1) * exp (-(r * y)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have : -(y : ℂ) * (r : ℂ) = -(r * y : ℂ) := by
      simp [mul_comm]
    simp [this]
  have hpow : (1 / r : ℂ) ^ a = (r : ℂ) ^ (-a) := by
    rw [one_div, inv_cpow_ofReal_nonneg hr.le a, ← cpow_neg]
  calc
    F (r : ℂ) = ∫ y : ℝ in Set.Ioi (0 : ℝ),
        (y : ℂ) ^ (a - 1) * exp (-(y : ℂ) * (r : ℂ)) := rfl
    _ = ∫ y : ℝ in Set.Ioi (0 : ℝ),
        (y : ℂ) ^ (a - 1) * exp (-(r * y)) := hcongr
    _ = (1 / r : ℂ) ^ a * Gamma a := hreal
    _ = (r : ℂ) ^ (-a) * Gamma a := by rw [hpow]
    _ = G (r : ℂ) := rfl

end Complex
end
