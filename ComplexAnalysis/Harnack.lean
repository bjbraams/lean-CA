/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# The Poisson kernel and Harnack's inequality

Basic properties of Mathlib's Poisson kernel `poissonKernel c w z` on the circle
`‖z - c‖ = R` for `w` in the open disc: nonnegativity, continuity, total mass one, and the
two-sided bounds `(R - ‖w - c‖) / (R + ‖w - c‖) ≤ poissonKernel c w z ≤ (R + ‖w - c‖) /
(R - ‖w - c‖)`. Combined with Mathlib's Poisson representation of harmonic functions and the
mean value property, they give **Harnack's inequality** for nonnegative harmonic functions.

## Main results

* `Complex.circleAverage_poissonKernel`: the kernel has total mass one.
* `Complex.harnack`: Harnack's inequality on a disc.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem X.2.9 (Harnack's inequality).
* T. W. Gamelin, *Complex Analysis*, Section X.1.
-/

public noncomputable section

open Set Metric Filter Function InnerProductSpace Real
open scoped Topology

namespace Complex

variable {c w z : ℂ} {R : ℝ}

/-- The Poisson kernel is nonnegative on the circle. -/
theorem poissonKernel_nonneg (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    0 ≤ poissonKernel c w z := by
  rw [poissonKernel_def]
  refine div_nonneg ?_ (sq_nonneg _)
  rw [mem_sphere_iff_norm] at hz
  rw [mem_ball_iff_norm] at hw
  rw [hz]
  nlinarith [norm_nonneg (w - c)]

/-- The Poisson kernel is continuous on the circle. -/
theorem continuousOn_poissonKernel_sphere (hw : w ∈ ball c R) :
    ContinuousOn (poissonKernel c w) (sphere c R) := by
  refine ContinuousOn.congr
    (f := fun z => (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2) ?_
    fun z _ => poissonKernel_def c w z
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
  rw [mem_sphere_iff_norm] at hz
  rw [mem_ball_iff_norm] at hw
  have hne : z - c - (w - c) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hz
    linarith
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)

/-- The upper bound for the Poisson kernel on the circle. -/
theorem poissonKernel_le (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    poissonKernel c w z ≤ (R + ‖w - c‖) / (R - ‖w - c‖) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel, comp_apply, herglotzRieszKernel_def]
  exact re_herglotzRieszKernel_le hz hw

/-- The lower bound for the Poisson kernel on the circle. -/
theorem le_poissonKernel (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) ≤ poissonKernel c w z := by
  rw [poissonKernel_eq_re_herglotzRieszKernel, comp_apply, herglotzRieszKernel_def]
  exact le_re_herglotzRieszKernel hz hw

/-- The Poisson kernel has total mass one. -/
theorem circleAverage_poissonKernel (hw : w ∈ ball c R) :
    circleAverage (poissonKernel c w) c R = 1 := by
  have := (harmonicContOnCl_const (c := (1 : ℝ)) (s := ball c R)).circleAverage_poissonKernel_smul
    hw
  convert this using 2
  ext z
  simp

/-- **Harnack's inequality.** A nonnegative harmonic function on a disc, continuous on the
closed disc, satisfies `(R - r) / (R + r) * u c ≤ u w ≤ (R + r) / (R - r) * u c` at distance `r`
from the center. -/
theorem harnack (hR : 0 < R) {u : ℂ → ℝ} (hu : HarmonicContOnCl u (ball c R))
    (hpos : ∀ z ∈ sphere c R, 0 ≤ u z) (hw : w ∈ ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) * u c ≤ u w ∧ u w ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * u c := by
  have hR' : |R| = R := abs_of_pos hR
  have hcont : ContinuousOn u (sphere c R) := hu.continuousOn_ball.mono sphere_subset_closedBall
  have hint : CircleIntegrable u c R := hcont.circleIntegrable hR.le
  have hkint : CircleIntegrable (poissonKernel c w • u) c R :=
    ((continuousOn_poissonKernel_sphere hw).smul hcont).circleIntegrable hR.le
  have hmean : circleAverage u c R = u c := by
    have hu' : HarmonicContOnCl u (ball c |R|) := by rwa [hR']
    exact hu'.circleAverage_eq
  have hpoisson : circleAverage (poissonKernel c w • u) c R = u w :=
    hu.circleAverage_poissonKernel_smul hw
  constructor
  · rw [← hpoisson, ← hmean, ← smul_eq_mul, ← circleAverage_fun_smul]
    refine circleAverage_mono (by fun_prop) hkint fun z hz => ?_
    rw [hR'] at hz
    exact mul_le_mul_of_nonneg_right (le_poissonKernel hz hw) (hpos z hz)
  · rw [← hpoisson, ← hmean, ← smul_eq_mul, ← circleAverage_fun_smul]
    refine circleAverage_mono hkint (by fun_prop) fun z hz => ?_
    rw [hR'] at hz
    exact mul_le_mul_of_nonneg_right (poissonKernel_le hz hw) (hpos z hz)

end Complex

end
