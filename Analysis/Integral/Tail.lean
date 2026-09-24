/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Uniform control of integral tails

A family dominated on a half-line by one integrable real function has uniformly
vanishing tail integrals. For an integrable family, finite-interval integrals
therefore approximate the full half-line integrals uniformly in the family
parameter. The parameter space is arbitrary and may be empty; the measure need
not be Lebesgue measure. For Lebesgue measure, a power-decay majorant also gives
the explicit tail bound `C * R^(1-p) / (p-1)` when `p > 1`.

## Main results

* `MeasureTheory.tendstoUniformly_integral_Ioi_zero_of_norm_le`: A common integrable majorant
  gives uniformly vanishing half-line tails.
* `MeasureTheory.tendstoUniformly_intervalIntegral_integral_Ioi_of_norm_le`: Finite-interval
  integrals converge uniformly to half-line integrals when the family is integrable and has a
  common integrable majorant.
* `MeasureTheory.norm_integral_Ioi_le_rpow`: A power-decay majorant gives an explicit bound on a
  half-line integral. The exponent must be strictly greater than one.

## References

* `Mathlib.MeasureTheory.Integral.IntegralEqImproper`: formal background used by this module.
* `Mathlib.Topology.MetricSpace.Pseudo.Basic`: formal background used by this module.
* `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`: formal background used by this module.
-/

public section
open Set Filter MeasureTheory
open scoped Topology
namespace MeasureTheory

variable {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure ℝ} {a : ℝ} {f : ι → ℝ → F} {g : ℝ → ℝ}

/-- A common integrable majorant gives uniformly vanishing half-line tails. -/
theorem tendstoUniformly_integral_Ioi_zero_of_norm_le
    (hg : IntegrableOn g (Ioi a) μ)
    (hbound : ∀ i, ∀ t ∈ Ioi a, ‖f i t‖ ≤ g t) :
    TendstoUniformly (fun R i => ∫ t in Ioi R, f i t ∂μ) (fun _ => 0) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have htail : Tendsto (fun R => ∫ t in Ioi R, g t ∂μ) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  filter_upwards [htail.eventually (gt_mem_nhds hε), eventually_ge_atTop a] with R hR haR
  intro i
  rw [dist_zero_left]
  apply lt_of_le_of_lt _ hR
  apply norm_integral_le_of_norm_le (hg.mono_set (Ioi_subset_Ioi haR))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hbound i t (lt_of_le_of_lt haR ht)

/-- Finite-interval integrals converge uniformly to half-line integrals when the family
is integrable and has a common integrable majorant. -/
theorem tendstoUniformly_intervalIntegral_integral_Ioi_of_norm_le
    (hf : ∀ i, IntegrableOn (f i) (Ioi a) μ) (hg : IntegrableOn g (Ioi a) μ)
    (hbound : ∀ i, ∀ t ∈ Ioi a, ‖f i t‖ ≤ g t) :
    TendstoUniformly (fun R i => ∫ t in a..R, f i t ∂μ)
      (fun i => ∫ t in Ioi a, f i t ∂μ) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have htail := Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_integral_Ioi_zero_of_norm_le hg hbound) ε hε
  filter_upwards [htail, eventually_ge_atTop a] with R hR haR
  intro i
  rw [dist_eq_norm, ← intervalIntegral.integral_Ioi_sub_Ioi (hf i) haR,
    sub_sub_cancel]
  simpa only [dist_zero_left] using hR i

/-- A power-decay majorant gives an explicit bound on a half-line integral.
The exponent must be strictly greater than one. -/
theorem norm_integral_Ioi_le_rpow {f : ℝ → F} {R p C : ℝ}
    (hR : 0 < R) (hp : 1 < p)
    (hbound : ∀ t ∈ Ioi R, ‖f t‖ ≤ C * t ^ (-p)) :
    ‖∫ t in Ioi R, f t‖ ≤ C * (R ^ (1 - p) / (p - 1)) := by
  have hg := (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hR).const_mul C
  have h := norm_integral_le_of_norm_le hg
    (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -p < -1) hR] at h
  convert h using 1
  rw [show -p + 1 = -(p - 1) by ring, neg_div_neg_eq, neg_sub]

end MeasureTheory
