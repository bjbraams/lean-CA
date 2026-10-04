/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Rouche
public import ComplexAnalysis.ZeroPersistence
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import TauCeti.Analysis.Complex.Conformal.Hurwitz

/-!
# Hurwitz's theorem

Uniform approximation on a closed disk with a zero-free boundary eventually preserves
the total number of zeros counted with multiplicity. On a connected open set, a locally
uniform limit of zero-free holomorphic functions is zero-free or identically zero.

The zero-free and injective-limit conclusions use the Tau Ceti contributors'
`TauCeti.hurwitz` and `TauCeti.hurwitz_injOn`, imported from
`TauCeti.Analysis.Complex.Conformal.Hurwitz`. The local adapters retain arbitrary nontrivial
filters. The disk zero-persistence and divisor-counting helpers remain local.

## Main results

* `Complex.exists_zero_of_norm_lt_sphere`: The center-versus-boundary zero criterion on a disk
  with arbitrary center.
* `Complex.eventually_sum_divisor_eq_of_tendstoUniformlyOn`: Uniform convergence on a closed
  disk eventually preserves its divisor degree if the holomorphic limit has no boundary zeros.
* `Complex.eventually_exists_zero_of_tendstoUniformlyOn`: A zero of the limit persists under
  uniform holomorphic approximation on a closed disk whose boundary contains no zeros of the
  limit.
* `Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn`: **Hurwitz's theorem.** A
  locally uniform limit of zero-free holomorphic functions on a connected open set is
  identically zero or has no zeros.
* `Complex.eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn`: A locally uniform limit of
  injective holomorphic functions on a connected open set is constant or injective.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Metric MeromorphicOn
open scoped Topology

namespace Complex

/-- The center-versus-boundary zero criterion on a disk with arbitrary center. -/
theorem exists_zero_of_norm_lt_sphere {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hlt : ∀ z ∈ sphere c R, ‖f c‖ < ‖f z‖) :
    ∃ z ∈ ball c R, f z = 0 := by
  obtain ⟨w, hw, he⟩ := exists_zero_of_norm_lt_boundary (f := fun w ↦ f (c + w)) hR
    (fun w hw ↦ ((hf (c + w) (by simpa [dist_eq_norm] using hw)).differentiableAt.comp w
      ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt)
    (fun w hw ↦ by simpa using hlt (c + w) (by simpa [dist_eq_norm] using hw))
  exact ⟨c + w, by simpa [dist_eq_norm] using hw, he⟩

/-- Uniform convergence on a closed disk eventually preserves its divisor degree if the
holomorphic limit has no boundary zeros. -/
theorem eventually_sum_divisor_eq_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hF : ∀ᶠ n in l, AnalyticOnNhd ℂ (F n) (closedBall c R))
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z ∈ sphere c R, f z ≠ 0)
    (hlim : TendstoUniformlyOn F f l (closedBall c R)) :
    ∀ᶠ n in l, (∑ᶠ z, divisor (F n) (closedBall c R) z) =
      ∑ᶠ z, divisor f (closedBall c R) z := by
  obtain ⟨b, hb', hmin⟩ := (isCompact_sphere c R).exists_isMinOn
    ⟨c + R, by simp [abs_of_pos hR]⟩
    (hf.continuousOn.norm.mono sphere_subset_closedBall)
  have hpos := norm_pos_iff.mpr (hb b hb')
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.mp hlim _ hpos] with n hn hclose
  apply (sum_divisor_eq_of_norm_sub_lt hR hf hn _).symm
  intro z hz
  have hh := hclose z (sphere_subset_closedBall hz)
  have hh' : ‖F n z - f z‖ < ‖f b‖ := by
    simpa [dist_eq_norm, norm_sub_rev] using hh
  exact hh'.trans_le (hmin hz)

/-- A zero of the limit persists under uniform holomorphic approximation on a closed disk
whose boundary contains no zeros of the limit. -/
theorem eventually_exists_zero_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hF : ∀ᶠ n in l, AnalyticOnNhd ℂ (F n) (closedBall c R))
    (hf : ContinuousOn f (closedBall c R)) (hz : f c = 0)
    (hb : ∀ z ∈ sphere c R, f z ≠ 0)
    (hlim : TendstoUniformlyOn F f l (closedBall c R)) :
    ∀ᶠ n in l, ∃ z ∈ ball c R, F n z = 0 := by
  obtain ⟨b, hb', hmin⟩ := (isCompact_sphere c R).exists_isMinOn
    ⟨c + R, by simp [abs_of_pos hR]⟩ (hf.norm.mono sphere_subset_closedBall)
  have hpos := norm_pos_iff.mpr (hb b hb')
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.mp hlim _ (by positivity :
    0 < ‖f b‖ / 3)] with n hn hclose
  apply exists_zero_of_norm_lt_sphere hR hn
  intro z hz'
  have hcenter : ‖F n c‖ < ‖f b‖ / 3 := by
    simpa [hz] using hclose c (mem_closedBall_self hR.le)
  have hboundary : ‖f z - F n z‖ < ‖f b‖ / 3 := by
    simpa [dist_eq_norm] using hclose z (sphere_subset_closedBall hz')
  have hnorm := norm_sub_norm_le (f z) (F n z)
  have hmin' : ‖f b‖ ≤ ‖f z‖ := hmin hz'
  linarith

/-- **Hurwitz's theorem.** A locally uniform limit of zero-free holomorphic functions on
a connected open set is identically zero or has no zeros.

This adapts the Tau Ceti contributors' `TauCeti.hurwitz` from
`TauCeti.Analysis.Complex.Conformal.Hurwitz`; the mathematical proof is imported.

Related formalizations: Vincent Beffara's RMT4 and Yury Kudryashov's Mathlib PR #33505. See
`CREDITS.md`. -/
theorem eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (hne : ∀ᶠ n in l, ∀ z ∈ U, F n z ≠ 0)
    (hlim : TendstoLocallyUniformlyOn F f l U) :
    EqOn f 0 U ∨ ∀ z ∈ U, f z ≠ 0 := by
  simpa only [Set.EqOn, Pi.zero_apply] using (TauCeti.hurwitz hU hconn hF hlim hne).symm

/-- A locally uniform limit of injective holomorphic functions on a connected open set
is constant or injective.

This adapts the Tau Ceti contributors' `TauCeti.hurwitz_injOn` from
`TauCeti.Analysis.Complex.Conformal.Hurwitz`; the mathematical proof is imported.

Related formalizations: Vincent Beffara's RMT4 and Yury Kudryashov's Mathlib PR #33505. See
`CREDITS.md`. -/
theorem eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn
    {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (hinj : ∀ᶠ n in l, InjOn (F n) U)
    (hlim : TendstoLocallyUniformlyOn F f l U) :
    (∃ v : ℂ, EqOn f (fun _ ↦ v) U) ∨ InjOn f U := by
  simpa only [Set.EqOn] using (TauCeti.hurwitz_injOn hU hconn hF hlim hinj).symm

end Complex
