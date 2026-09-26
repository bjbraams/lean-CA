/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.LaurentSeries.Basic
public import ComplexAnalysis.CauchyDerivatives

/-!
# Residues at isolated singularities

The residue is the limit of normalized integrals on shrinking circles. For a function
holomorphic on a punctured neighborhood these integrals are eventually constant, so this
definition agrees with the Laurent coefficient of exponent `-1`. No meromorphy assumption
is needed: essential isolated singularities and Banach-valued functions are allowed.

The value at the center has no effect. Without isolated holomorphy or another hypothesis
ensuring convergence, the definition has the usual unspecified `limUnder` value.

## Main results

* `Complex.residue_eq_of_eventually_eq`: Eventually constant normalized circle integrals compute
  the residue.
* `Complex.eventually_circleIntegral_eq_residue`: Near an isolated holomorphic singularity,
  small-circle integrals exist and compute the residue.
* `Complex.residue_add`: Residues add for functions holomorphic on punctured neighborhoods.
* `Complex.residue_const_smul`: Residues commute with multiplication by a constant scalar.
* `Complex.residue_sub`: Residues subtract for functions holomorphic on punctured neighborhoods.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The residue at `c`, defined by normalized circle integrals as the radius tends to zero
through positive values. For an isolated holomorphic singularity the integrals stabilize.

A scalar counterpart appears in Roman Kvasnytskyi's Mathlib PR #29588. See `CREDITS.md`. -/
@[expose] def residue (f : ℂ → F) (c : ℂ) : F :=
  limUnder (𝓝[>] (0 : ℝ)) (fun r ↦ (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, r), f z)

omit [CompleteSpace F] in
/-- Eventually constant normalized circle integrals compute the residue. -/
theorem residue_eq_of_eventually_eq {f : ℂ → F} {c : ℂ} {v : F}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (2 * Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, r), f z) = v) :
    residue f c = v := by
  have he : (fun r ↦ (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, r), f z)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun _ ↦ v) := h
  exact (tendsto_const_nhds.congr' he.symm).limUnder_eq

omit [CompleteSpace F] in
/-- An analytic punctured closed disk has the same integral on every smaller positive circle. -/
theorem circleIntegral_eq_of_analyticOnNhd_punctured_closedBall
    {f : ℂ → F} {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R \ {c})) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, r), f z := by
  apply circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR countable_empty
  · apply hf.continuousOn.mono
    intro z hz
    exact ⟨hz.1, by rintro rfl; exact hz.2 (mem_ball_self hr)⟩
  · intro z hz
    exact (hf z ⟨ball_subset_closedBall hz.1.1, by
      rintro rfl
      exact hz.1.2 (mem_closedBall_self hr.le)⟩).differentiableAt

omit [CompleteSpace F] in
/-- The residue can be computed on any circle bounding a punctured analytic closed disk.

A scalar counterpart appears in Roman Kvasnytskyi's Mathlib PR #29588. See `CREDITS.md`. -/
theorem residue_eq_circleIntegral {f : ℂ → F} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R \ {c})) :
    residue f c = (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, R), f z := by
  apply residue_eq_of_eventually_eq
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  rw [circleIntegral_eq_of_analyticOnNhd_punctured_closedBall hr.1 hr.2.le hf]

omit [CompleteSpace F] in
/-- The residue at the origin is the Laurent coefficient of exponent `-1`. -/
theorem residue_eq_circleLaurentCoeff {f : ℂ → F} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R \ {0})) :
    residue f 0 = circleLaurentCoeff f R (-1) := by
  simpa [circleLaurentCoeff] using residue_eq_circleIntegral hR hf

omit [CompleteSpace F] in
/-- Functions agreeing on a punctured neighborhood have equal residues. -/
theorem residue_congr {f g : ℂ → F} {c : ℂ} (h : f =ᶠ[𝓝[≠] c] g) :
    residue f c = residue g c := by
  obtain ⟨R, hR, hfg⟩ := Metric.mem_nhdsWithin_iff.mp h
  have he : (fun r ↦ (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, r), f z) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r ↦ (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, r), g z) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    congr 1
    apply circleIntegral.integral_congr hr.1.le
    intro z hz
    apply hfg
    exact ⟨by simpa [mem_ball, mem_sphere.mp hz] using hr.2, by
      rintro rfl
      have : r = 0 := by simpa using (mem_sphere.mp hz).symm
      exact hr.1.ne' this⟩
  simp only [residue, limUnder, Filter.map_congr he]

/-- A function analytic at the center has zero residue.

A scalar counterpart appears in Roman Kvasnytskyi's Mathlib PR #29588. See `CREDITS.md`. -/
theorem _root_.AnalyticAt.residue_eq_zero {f : ℂ → F} {c : ℂ}
    (hf : AnalyticAt ℂ f c) : residue f c = 0 := by
  obtain ⟨R, hR, ha⟩ := hf.exists_ball_analyticOnNhd
  apply residue_eq_of_eventually_eq
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hb := ha.mono (closedBall_subset_ball hr.2)
  rw [(hb.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero
    hr.1.le, smul_zero]

/-- Cauchy's kernel with holomorphic numerator has residue equal to the numerator at the pole.

A scalar counterpart appears in Roman Kvasnytskyi's Mathlib PR #29588. See `CREDITS.md`. -/
theorem residue_sub_inv_smul {f : ℂ → F} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    residue (fun z ↦ (z - c)⁻¹ • f z) c = f c := by
  obtain ⟨R, hR, ha⟩ := hf.exists_ball_analyticOnNhd
  apply residue_eq_of_eventually_eq
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hb := ha.mono (closedBall_subset_ball hr.2)
  exact (hb.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
    |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (mem_ball_self hr.1)

/-- Scalar simple-pole computation with a holomorphic numerator.

A scalar counterpart appears in Roman Kvasnytskyi's Mathlib PR #29588. See `CREDITS.md`. -/
theorem residue_div_sub {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    residue (fun z ↦ f z / (z - c)) c = f c := by
  simpa [div_eq_mul_inv, mul_comm] using residue_sub_inv_smul hf

/-- The higher-order Cauchy kernel computes a residue by an iterated derivative. -/
theorem residue_sub_zpow_smul {f : ℂ → F} {c : ℂ} (hf : AnalyticAt ℂ f c) (n : ℕ) :
    residue (fun z ↦ (z - c) ^ (-(n + 1 : ℤ)) • f z) c =
      (n.factorial : ℂ)⁻¹ • iteratedDeriv n f c := by
  obtain ⟨R, hR, ha⟩ := hf.exists_ball_analyticOnNhd
  apply residue_eq_of_eventually_eq
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hb := (ha.mono (closedBall_subset_ball hr.2)).differentiableOn
    |>.mono closure_ball_subset_closedBall |>.diffContOnCl
  rw [hb.iteratedDeriv_eq_circleIntegral_sub_zpow_smul hr.1 n (mem_ball_self hr.1),
    smul_smul, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]

omit [CompleteSpace F] in
/-- Isolated holomorphy supplies a positive punctured closed disk of analyticity. -/
theorem exists_pos_analyticOnNhd_punctured_closedBall {f : ℂ → F} {c : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z) :
    ∃ R > 0, AnalyticOnNhd ℂ f (closedBall c R \ {c}) := by
  obtain ⟨R, hR, ha⟩ := Metric.mem_nhdsWithin_iff.mp hf
  refine ⟨R / 2, half_pos hR, fun z hz ↦ ha ⟨?_, hz.2⟩⟩
  exact (closedBall_subset_ball (half_lt_self hR)) hz.1

omit [CompleteSpace F] in
/-- Near an isolated holomorphic singularity, small-circle integrals exist and compute the residue.
-/
theorem eventually_circleIntegral_eq_residue {f : ℂ → F} {c : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), CircleIntegrable f c r ∧
      (2 * Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, r), f z) = residue f c := by
  obtain ⟨R, hR, ha⟩ := exists_pos_analyticOnNhd_punctured_closedBall hf
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hb : AnalyticOnNhd ℂ f (closedBall c r \ {c}) := ha.mono (by
    intro z hz
    exact ⟨closedBall_subset_closedBall hr.2.le hz.1, hz.2⟩)
  refine ⟨(hb.continuousOn.mono ?_).circleIntegrable hr.1.le,
    (residue_eq_circleIntegral hr.1 hb).symm⟩
  intro z hz
  exact ⟨sphere_subset_closedBall hz, by
    rintro rfl
    have : r = 0 := by simpa using (mem_sphere.mp hz).symm
    exact hr.1.ne' this⟩

omit [CompleteSpace F] in
/-- Residues add for functions holomorphic on punctured neighborhoods. -/
theorem residue_add {f g : ℂ → F} {c : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ g z) :
    residue (fun z ↦ f z + g z) c = residue f c + residue g c := by
  apply residue_eq_of_eventually_eq
  filter_upwards [eventually_circleIntegral_eq_residue hf,
    eventually_circleIntegral_eq_residue hg] with r hr hs
  rw [circleIntegral.integral_add hr.1 hs.1, smul_add, hr.2, hs.2]

omit [CompleteSpace F] in
/-- Residues commute with multiplication by a constant scalar. -/
theorem residue_const_smul {f : ℂ → F} {c : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z) (a : ℂ) :
    residue (fun z ↦ a • f z) c = a • residue f c := by
  apply residue_eq_of_eventually_eq
  filter_upwards [eventually_circleIntegral_eq_residue hf] with r hr
  rw [circleIntegral.integral_smul, smul_comm, hr.2]

omit [CompleteSpace F] in
/-- Residues subtract for functions holomorphic on punctured neighborhoods. -/
theorem residue_sub {f g : ℂ → F} {c : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ g z) :
    residue (fun z ↦ f z - g z) c = residue f c - residue g c := by
  apply residue_eq_of_eventually_eq
  filter_upwards [eventually_circleIntegral_eq_residue hf,
    eventually_circleIntegral_eq_residue hg] with r hr hs
  rw [circleIntegral.integral_sub hr.1 hs.1, smul_sub, hr.2, hs.2]

end Complex
