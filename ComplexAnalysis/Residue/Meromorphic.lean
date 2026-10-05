/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Residue
public import TauCeti.Analysis.Contour.Residue.Quotient
public import TauCeti.Analysis.Contour.Residue.SimplePole
public import TauCeti.Analysis.Contour.Residue.Theorem

/-!
# Residues of meromorphic germs

The residue `Complex.residue` is defined by normalized integrals over shrinking circles, which
allows Banach-valued functions and essential singularities. For a scalar meromorphic germ it
agrees with the Laurent-coefficient residue `TauCeti.Contour.residue` of the Tau Ceti
contributors (`TauCeti.Analysis.Contour.Residue.Basic`). The agreement follows from Tau Ceti's
residue theorem on a small circle (`TauCeti.Analysis.Contour.Residue.Theorem`), and it transports
the Tau Ceti residue calculus at simple poles to the local definition.

## Main results

* `Complex.residue_eq_contour_residue`: the two residues agree for a meromorphic germ.
* `Complex.residue_eq_of_tendsto_sub_mul`: the residue at a simple pole is the limit of
  `(z - c) * f z`.
* `Complex.residue_div_of_eq_zero_of_deriv_ne_zero`: the residue of `g / h` at a simple zero
  of `h` is `g c / h' c`.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Section V.2.
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace Complex

/-- For a scalar meromorphic germ, the residue defined by shrinking circle integrals agrees with
the Laurent-coefficient residue `TauCeti.Contour.residue` of the Tau Ceti contributors.

The proof applies `TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg` on
a circle small enough that `c` is the only possible pole inside. -/
theorem residue_eq_contour_residue {f : ℂ → ℂ} {c : ℂ} (hf : MeromorphicAt f c) :
    residue f c = TauCeti.Contour.residue f c := by
  have han := hf.eventually_analyticAt
  obtain ⟨R, hR, hRan⟩ := exists_pos_analyticOnNhd_punctured_closedBall han
  obtain ⟨r, ⟨-, hr⟩, hrR⟩ := ((eventually_circleIntegral_eq_residue han).and
    (Ioo_mem_nhdsGT hR)).exists
  have hball : closedBall c r ⊆ closedBall c R := closedBall_subset_closedBall hrR.2.le
  have hmero : MeromorphicOn f (closedBall c r) := fun z hz ↦ by
    by_cases hzc : z = c
    · exact hzc ▸ hf
    · exact (hRan z ⟨hball hz, hzc⟩).meromorphicAt
  have hT := TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hrR.1 {c}
    hmero (by rw [Finset.coe_singleton, Set.singleton_subset_iff]; exact mem_ball_self hrR.1)
    (fun z hz hneg ↦ by
      by_contra hzc
      rw [Finset.mem_singleton] at hzc
      rw [(hRan z ⟨hball hz, hzc⟩).meromorphicOrderAt_eq] at hneg
      cases h : analyticOrderAt f z <;> simp [h] at hneg
      exact absurd hneg (by norm_cast))
  rw [← hr, hT, Finset.sum_singleton, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

/-- The residue at a simple pole is the limit of `(z - c) * f z`.

This transports `TauCeti.Contour.residue_eq_of_tendsto_sub_mul` by the Tau Ceti contributors. -/
theorem residue_eq_of_tendsto_sub_mul {f : ℂ → ℂ} {c L : ℂ} (hf : MeromorphicAt f c)
    (h : Tendsto (fun z ↦ (z - c) * f z) (𝓝[≠] c) (𝓝 L)) :
    residue f c = L := by
  rw [residue_eq_contour_residue hf, TauCeti.Contour.residue_eq_of_tendsto_sub_mul hf h]

/-- The residue of `g / h` at a simple zero `c` of `h` is `g c / deriv h c`.

This transports `TauCeti.Contour.residue_div_of_zero_deriv_ne_zero` by the Tau Ceti
contributors. -/
theorem residue_div_of_eq_zero_of_deriv_ne_zero {g h : ℂ → ℂ} {c : ℂ} (hg : AnalyticAt ℂ g c)
    (hh : AnalyticAt ℂ h c) (hh0 : h c = 0) (hh' : deriv h c ≠ 0) :
    residue (fun z ↦ g z / h z) c = g c / deriv h c := by
  rw [residue_eq_contour_residue (f := fun z ↦ g z / h z)
      (hg.meromorphicAt.div hh.meromorphicAt),
    TauCeti.Contour.residue_div_of_zero_deriv_ne_zero hg hh hh0 hh']

end Complex
