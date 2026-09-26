/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.HalfPlane
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Principal powers on the right half-plane

Multiplication formulas with explicit branch control, and holomorphy on disks
centered on the positive real axis with radius equal to their center.

## Main results

* `Complex.ofReal_pos_mul_cpow`: Positive-real scaling commutes with the principal complex
  power.
* `Complex.mul_cpow_of_re_pos`: Two factors in the right half-plane have compatible principal
  logarithms.
* `Complex.analyticOnNhd_cpow_ball_ofReal`: The principal power is holomorphic on any disk
  centered at a positive real number with that number as radius.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section
open Set Filter
open scoped Topology
namespace Complex

/-- Positive-real scaling commutes with the principal complex power. -/
theorem ofReal_pos_mul_cpow (t w : ℂ) {a : ℝ} (ha : 0 < a) (hw : w ≠ 0) :
    ((a : ℂ) * w) ^ t = (a : ℂ) ^ t * w ^ t := by
  have hloga : log (a : ℂ) = (Real.log a : ℂ) := by
    simpa using (log_ofReal_mul ha (x := 1) one_ne_zero)
  rw [cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne') hw)]
  rw [mul_comm (a : ℂ) w, log_mul_ofReal a ha w hw, add_mul, exp_add]
  rw [cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne')]
  rw [cpow_def_of_ne_zero hw]
  rw [hloga]

/-- Two factors in the right half-plane have compatible principal logarithms. -/
theorem mul_cpow_of_re_pos {a w : ℂ} (ha : 0 < a.re) (hw : 0 < w.re) (t : ℂ) :
    (a * w) ^ t = a ^ t * w ^ t := by
  have ha0 := ne_zero_of_re_pos ha
  have hw0 := ne_zero_of_re_pos hw
  have haarg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  have hwarg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  have hlog : log (a * w) = log a + log w :=
    Complex.log_mul ha0 hw0 ⟨by linarith [haarg.1, hwarg.1],
      by linarith [haarg.2, hwarg.2]⟩
  rw [cpow_def_of_ne_zero (mul_ne_zero ha0 hw0), cpow_def_of_ne_zero ha0,
    cpow_def_of_ne_zero hw0, hlog, add_mul, exp_add]

/-- The principal power is holomorphic on any disk centered at a positive real
number with that number as radius. -/
theorem analyticOnNhd_cpow_ball_ofReal (t : ℂ) (A : ℝ) :
    AnalyticOnNhd ℂ (fun w : ℂ ↦ w ^ t) (Metric.ball (A : ℂ) A) := by
  intro w hw
  have hnorm : ‖(A : ℂ) - w‖ < A := by simpa [dist_eq_norm, norm_sub_rev] using hw
  have hreal : 0 < w.re := by
    have h := re_le_norm ((A : ℂ) - w)
    simp only [sub_re, ofReal_re] at h
    linarith
  have hslit : w ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hreal)
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_slitPlane.eventually_mem hslit] with v hv
  exact differentiableAt_id.cpow_const hv

end Complex
end
