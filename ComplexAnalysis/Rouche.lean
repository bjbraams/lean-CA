/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.ArgumentPrinciple
public import TauCeti.Analysis.Complex.Conformal.Rouche

/-!
# Rouché's theorem on disks

A strict boundary perturbation preserves the total divisor degree, hence the number
of zeros counted with multiplicity. The divisor degree on a closed disk without boundary zeros is
the zero count in the open disk, and Rouché's theorem in that zero-count form is imported from the
Tau Ceti contributors' `TauCeti.Analysis.Complex.Conformal.Rouche`, including the symmetric
hypothesis `‖f - g‖ < ‖f‖ + ‖g‖`.

The continuity of logarithmic-derivative circle integrals in a parameter is also recorded; it
gives the classical homotopy proof of Rouché's theorem.

## Main results

* `Complex.continuous_circleIntegral_logDeriv`: A family of logarithmic-derivative circle
  integrals is continuous when the functions and their derivatives vary continuously on the
  boundary and never vanish there.
* `Complex.finsum_divisor_eq_finsum_analyticOrderNatAt`: the divisor degree on a closed disk
  without boundary zeros counts the zeros in the open disk with multiplicity.
* `Complex.sum_divisor_eq_of_norm_sub_lt_norm_add_norm`: **Rouché's theorem**, symmetric form.
* `Complex.sum_divisor_eq_of_norm_sub_lt`: **Rouché's theorem.** Two holomorphic functions with
  `‖g - f‖ < ‖f‖` on a circle have the same number of zeros in the disk, counted with
  multiplicity as divisor degree.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Metric Function MeasureTheory MeromorphicOn
open scoped Topology

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

/-- On a closed disk whose boundary circle contains no zeros of the analytic function `f`, the
divisor degree of `f` is the number of zeros in the open disk counted with analytic multiplicity.
This connects the divisor form used here with the zero counts of Tau Ceti's Rouché and Hurwitz
theorems. -/
theorem finsum_divisor_eq_finsum_analyticOrderNatAt {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hb : ∀ z ∈ sphere c R, f z ≠ 0) :
    (∑ᶠ z, divisor f (closedBall c R) z) =
      ((∑ᶠ z ∈ ball c R, analyticOrderNatAt f z : ℕ) : ℤ) := by
  have hw : c + (R : ℂ) ∈ sphere c R := by simp [abs_of_pos hR]
  have hne : ∀ z ∈ closedBall c R, analyticOrderAt f z ≠ ⊤ := fun z hz ↦
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
      (sphere_subset_closedBall hw) hz
      (by rw [(hf _ (sphere_subset_closedBall hw)).analyticOrderAt_eq_zero.mpr (hb _ hw)]; simp)
  simp only [finsum_mem_def]
  refine Eq.trans ?_ ((Nat.castAddMonoidHom ℤ).map_finsum_of_injective Nat.cast_injective _).symm
  refine finsum_congr fun z ↦ ?_
  by_cases hz : z ∈ closedBall c R
  · rw [hf.divisor_apply hz]
    by_cases hzb : z ∈ ball c R
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hne z hz)
      simp [indicator_of_mem hzb, analyticOrderNatAt, ← hn]
    · have hzs : z ∈ sphere c R := by
        simp only [mem_closedBall, mem_ball, not_lt] at hz hzb
        exact mem_sphere.mpr (le_antisymm hz hzb)
      simp [indicator_of_notMem hzb, (hf z hz).analyticOrderAt_eq_zero.mpr (hb z hzs)]
  · simp only [indicator_of_notMem fun h ↦ hz (ball_subset_closedBall h), map_zero]
    exact notMem_support.mp fun h ↦ hz ((divisor _ _).supportWithinDomain h)

/-- **Rouché's theorem**, symmetric form. Two holomorphic functions with
`‖f - g‖ < ‖f‖ + ‖g‖` on a circle have the same number of zeros in the disk, counted with
multiplicity as divisor degree.

This adapts the Tau Ceti contributors' `TauCeti.rouche_symm` from
`TauCeti.Analysis.Complex.Conformal.Rouche`; the winding-number proof is imported. -/
theorem sum_divisor_eq_of_norm_sub_lt_norm_add_norm {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hb : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖ + ‖g z‖) :
    (∑ᶠ z, divisor f (closedBall c R) z) = ∑ᶠ z, divisor g (closedBall c R) z := by
  have hf0 : ∀ z ∈ sphere c R, f z ≠ 0 := fun z hz h ↦ by simpa [h] using hb z hz
  have hg0 : ∀ z ∈ sphere c R, g z ≠ 0 := fun z hz h ↦ by simpa [h] using hb z hz
  rw [finsum_divisor_eq_finsum_analyticOrderNatAt hR hf hf0,
    finsum_divisor_eq_finsum_analyticOrderNatAt hR hg hg0, TauCeti.rouche_symm hR hf hg hb]

/-- **Rouché's theorem.** Two holomorphic functions with `‖g - f‖ < ‖f‖` on a circle
have the same number of zeros in the disk, counted with multiplicity as divisor degree. -/
theorem sum_divisor_eq_of_norm_sub_lt {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hb : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    (∑ᶠ z, divisor f (closedBall c R) z) = ∑ᶠ z, divisor g (closedBall c R) z :=
  sum_divisor_eq_of_norm_sub_lt_norm_add_norm hR hf hg fun z hz ↦ by
    rw [norm_sub_rev]
    exact (hb z hz).trans_le (le_add_of_nonneg_right (norm_nonneg _))

end Complex
