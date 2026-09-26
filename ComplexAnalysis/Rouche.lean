/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.ArgumentPrinciple
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Rouché's theorem on disks

A strict boundary perturbation preserves the total divisor degree, hence the number
of zeros counted with multiplicity. The proof deforms the function along a line segment;
the normalized logarithmic-derivative integral is continuous and integer-valued.

## Main results

* `Complex.continuous_circleIntegral_logDeriv`: A family of logarithmic-derivative circle
  integrals is continuous when the functions and their derivatives vary continuously on the
  boundary and never vanish there.
* `Complex.sum_divisor_eq_of_norm_sub_lt`: **Rouché's theorem.** Two holomorphic functions with
  `‖g - f‖ < ‖f‖` on a circle have the same number of zeros in the disk, counted with
  multiplicity as divisor degree.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Metric Function MeasureTheory MeromorphicOn
open scoped Topology unitInterval

namespace Complex

/-- A family of logarithmic-derivative circle integrals is continuous when the functions
and their derivatives vary continuously on the boundary and never vanish there. -/
theorem continuous_circleIntegral_logDeriv {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    {f : X → ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn (fun p : X × ℂ ↦ f p.1 p.2) (univ ×ˢ sphere c R))
    (hd : ContinuousOn (fun p : X × ℂ ↦ deriv (f p.1) p.2) (univ ×ˢ sphere c R))
    (hne : ∀ x z, z ∈ sphere c R → f x z ≠ 0) :
    Continuous (fun x ↦ ∮ z in C(c, R), logDeriv (f x) z) := by
  have hmap : ∀ p : X × ℝ, (p.1, circleMap c R p.2) ∈ univ ×ˢ sphere c R :=
    fun p ↦ ⟨mem_univ _, circleMap_mem_sphere c hR p.2⟩
  have hc := hf.comp_continuous (by fun_prop) hmap
  have hc' := hd.comp_continuous (by fun_prop) hmap
  have hk : Continuous (fun p : X × ℝ ↦ deriv (circleMap c R) p.2 *
      (deriv (f p.1) (circleMap c R p.2) / f p.1 (circleMap c R p.2))) := by
    apply Continuous.mul
    · simp only [deriv_circleMap]
      fun_prop
    · exact hc'.div hc (fun p ↦ hne p.1 _ (circleMap_mem_sphere c hR p.2))
  simpa only [circleIntegral_def_Icc, logDeriv_apply, smul_eq_mul] using
    (continuous_parametric_integral_of_continuous (μ := volume) hk
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi))))

/-- **Rouché's theorem.** Two holomorphic functions with `‖g - f‖ < ‖f‖` on a circle
have the same number of zeros in the disk, counted with multiplicity as divisor degree. -/
theorem sum_divisor_eq_of_norm_sub_lt {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hb : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    (∑ᶠ z, divisor f (closedBall c R) z) = ∑ᶠ z, divisor g (closedBall c R) z := by
  let q : I → ℂ → ℂ := fun t z ↦ f z + (t : ℂ) * (g z - f z)
  have hq (t : I) : AnalyticOnNhd ℂ (q t) (closedBall c R) := by
    intro z hz
    exact (hf z hz).add (analyticAt_const.mul ((hg z hz).sub (hf z hz)))
  have hqn (t : I) (z : ℂ) (hz : z ∈ sphere c R) : q t z ≠ 0 := by
    have hsmall : ‖(t : ℂ) * (g z - f z)‖ < ‖f z‖ := by
      calc
        ‖(t : ℂ) * (g z - f z)‖ = (t : ℝ) * ‖g z - f z‖ := by
          rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg t.property.1]
        _ ≤ ‖g z - f z‖ := mul_le_of_le_one_left (norm_nonneg _) t.property.2
        _ < ‖f z‖ := hb z hz
    intro he
    have heq : (t : ℂ) * (g z - f z) = -f z := (eq_neg_iff_add_eq_zero).mpr (by
      simpa [q, add_comm] using he)
    simp [heq] at hsmall
  have hdq (t : I) {z : ℂ} (hz : z ∈ closedBall c R) :
      deriv (q t) z = deriv f z + (t : ℂ) * (deriv g z - deriv f z) := by
    exact ((hf z hz).differentiableAt.hasDerivAt.add
      (((hg z hz).differentiableAt.hasDerivAt.sub
        (hf z hz).differentiableAt.hasDerivAt).const_mul (t : ℂ))).deriv
  have hf' : ContinuousOn (fun p : I × ℂ ↦ f p.2) (univ ×ˢ sphere c R) :=
    (hf.continuousOn.mono sphere_subset_closedBall).comp continuous_snd.continuousOn
      (fun _ hp ↦ hp.2)
  have hg' : ContinuousOn (fun p : I × ℂ ↦ g p.2) (univ ×ˢ sphere c R) :=
    (hg.continuousOn.mono sphere_subset_closedBall).comp continuous_snd.continuousOn
      (fun _ hp ↦ hp.2)
  have hdf : ContinuousOn (fun p : I × ℂ ↦ deriv f p.2) (univ ×ˢ sphere c R) :=
    (hf.deriv.continuousOn.mono sphere_subset_closedBall).comp continuous_snd.continuousOn
      (fun _ hp ↦ hp.2)
  have hdg : ContinuousOn (fun p : I × ℂ ↦ deriv g p.2) (univ ×ˢ sphere c R) :=
    (hg.deriv.continuousOn.mono sphere_subset_closedBall).comp continuous_snd.continuousOn
      (fun _ hp ↦ hp.2)
  have ht : ContinuousOn (fun p : I × ℂ ↦ (p.1 : ℂ)) (univ ×ˢ sphere c R) := by fun_prop
  have hc : Continuous (fun t : I ↦ (2 * Real.pi * Complex.I)⁻¹ *
      (∮ z in C(c, R), logDeriv (q t) z)) := by
    apply continuous_const.mul
    apply continuous_circleIntegral_logDeriv hR.le (hf'.add (ht.mul (hg'.sub hf')))
      _ hqn
    apply (hdf.add (ht.mul (hdg.sub hdf))).congr
    intro p hp
    exact hdq p.1 (sphere_subset_closedBall hp.2)
  have hm : MapsTo (fun t : I ↦ (2 * Real.pi * Complex.I)⁻¹ *
      (∮ z in C(c, R), logDeriv (q t) z)) univ (range ((↑) : ℤ → ℂ)) := by
    intro t _
    exact ⟨∑ᶠ z, divisor (q t) (closedBall c R) z,
      (two_pi_I_inv_mul_circleIntegral_logDeriv_of_analyticOnNhd hR (hq t) (hqn t)).symm⟩
  have he := isPreconnected_univ.constant_of_mapsTo
    isClosedEmbedding_intCast.isEmbedding.isDiscrete_range hc.continuousOn hm
    (mem_univ (0 : I)) (mem_univ (1 : I))
  have hq0 : q 0 = f := by funext z; simp [q]
  have hq1 : q 1 = g := by funext z; simp [q]
  rw [two_pi_I_inv_mul_circleIntegral_logDeriv_of_analyticOnNhd hR (hq 0) (hqn 0),
    two_pi_I_inv_mul_circleIntegral_logDeriv_of_analyticOnNhd hR (hq 1) (hqn 1), hq0, hq1] at he
  exact_mod_cast he

end Complex
