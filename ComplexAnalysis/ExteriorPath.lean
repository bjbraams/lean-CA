/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.BranchLog.Analytic
public import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Compactified paths to infinity

The parametrization `t + (1 - u) / u * q u` runs from infinity to `t` as the real
parameter runs from zero to one, when `q 0 ≠ 0`. Its reversed Jacobian and the
normalized node factors are regular at zero. These elementary identities support
contour integrals with an unbounded exterior path without making a branch choice.

## Main results

* `Complex.compactifiedRay_one`: The finite endpoint of a compactified exterior path.
* `Complex.tendsto_compactifiedRay_cocompact`: The compactified exterior path tends to infinity
  in the topology of the plane.
* `Complex.hasDerivAt_compactifiedRay`: The compactified Jacobian gives the derivative of the
  exterior path away from zero.
* `Complex.analyticOnNhd_compactifiedRayJacobian`: The reversed Jacobian is holomorphic wherever
  the path-direction function is holomorphic.
* `Complex.compactifiedRay_sub_factor`: Factoring a node difference along the compactified path
  isolates its regular endpoint factor.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace Complex

/-- A path to infinity in compactified coordinates; only nonzero parameters describe the path. -/
def compactifiedRay (q : ℂ → ℂ) (t u : ℂ) : ℂ := t + (1 - u) / u * q u

/-- The reversed path derivative after removing its double pole at the compactified endpoint. -/
def compactifiedRayJacobian (q : ℂ → ℂ) (u : ℂ) : ℂ :=
  q u - u * (1 - u) * deriv q u

/-- The finite endpoint of a compactified exterior path. -/
@[simp] theorem compactifiedRay_one (q : ℂ → ℂ) (t : ℂ) : compactifiedRay q t 1 = t := by
  simp [compactifiedRay]

/-- Multiplication by the compactifying coordinate removes the pole of an exterior path. -/
theorem mul_compactifiedRay (q : ℂ → ℂ) (t : ℂ) {u : ℂ} (hu : u ≠ 0) :
    u * compactifiedRay q t u = u * t + (1 - u) * q u := by
  unfold compactifiedRay
  field_simp

/-- The scaled exterior path has a finite limit equal to its initial direction. -/
theorem tendsto_mul_compactifiedRay {q : ℂ → ℂ} (hq : ContinuousAt q 0) (t : ℂ) :
    Tendsto (fun u => u * compactifiedRay q t u) (𝓝[≠] 0) (𝓝 (q 0)) := by
  have h : Tendsto (fun u : ℂ => u * t + (1 - u) * q u) (𝓝 0) (𝓝 (q 0)) := by
    have hc : ContinuousAt (fun u : ℂ => u * t + (1 - u) * q u) 0 := by fun_prop
    simpa using hc.tendsto
  apply (h.mono_left inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (mul_compactifiedRay q t hu).symm

/-- A nonzero initial direction makes the exterior path escape every bounded set. -/
theorem tendsto_norm_compactifiedRay {q : ℂ → ℂ} (hq : ContinuousAt q 0)
    (hq0 : q 0 ≠ 0) (t : ℂ) :
    Tendsto (fun u => ‖compactifiedRay q t u‖) (𝓝[≠] 0) atTop := by
  apply ((tendsto_mul_compactifiedRay hq t).norm.pos_mul_atTop
    (norm_pos_iff.mpr hq0) tendsto_norm_inv_nhdsNE_zero_atTop).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [norm_mul, norm_inv]
  field_simp [norm_ne_zero_iff.mpr (show u ≠ 0 from hu)]

/-- The compactified exterior path tends to infinity in the topology of the plane. -/
theorem tendsto_compactifiedRay_cocompact {q : ℂ → ℂ} (hq : ContinuousAt q 0)
    (hq0 : q 0 ≠ 0) (t : ℂ) :
    Tendsto (compactifiedRay q t) (𝓝[≠] 0) (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact]
  exact tendsto_norm_atTop_iff_cobounded.mp (tendsto_norm_compactifiedRay hq hq0 t)

/-- The compactified Jacobian gives the derivative of the exterior path away from zero. -/
theorem hasDerivAt_compactifiedRay {q : ℂ → ℂ} (t : ℂ) {u : ℂ}
    (hq : DifferentiableAt ℂ q u) (hu : u ≠ 0) :
    HasDerivAt (compactifiedRay q t) (-(compactifiedRayJacobian q u) / u ^ 2) u := by
  unfold compactifiedRay compactifiedRayJacobian
  convert (((hasDerivAt_const u 1).sub (hasDerivAt_id u)).div (hasDerivAt_id u) hu
    |>.mul hq.hasDerivAt).const_add t using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- The reversed Jacobian is holomorphic wherever the path-direction function is holomorphic. -/
theorem analyticOnNhd_compactifiedRayJacobian {V : Set ℂ} {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q V) : AnalyticOnNhd ℂ (compactifiedRayJacobian q) V :=
  hq.sub ((analyticOnNhd_id.mul (analyticOnNhd_const.sub analyticOnNhd_id)).mul hq.deriv)

/-- Factoring a node difference along the compactified path isolates its regular endpoint factor. -/
theorem compactifiedRay_sub_factor (q : ℂ → ℂ) (t z : ℂ) {u : ℂ}
    (hu : u ≠ 0) (hq : q u ≠ 0) :
    (1 - u) + u * (t - z) / q u = u * (compactifiedRay q t u - z) / q u := by
  unfold compactifiedRay
  field_simp
  ring

end Complex
