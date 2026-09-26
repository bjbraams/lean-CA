/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Runge.Kernel
public import ComplexAnalysis.Runge.Cutoff

/-!
# Runge's theorem: approximation by sums of simple poles off a compact set

A function holomorphic on an open neighborhood `U` of a compact set `K` is, uniformly on `K`,
a limit of finite sums of simple poles `∑ i, a i * (c i - z)⁻¹` with poles `c i ∈ U \ K`. The
proof combines the Cauchy–Pompeiu representation of `f` on `K` by a Cauchy-type integral with
continuous density supported in `U \ K` and the uniform approximation of such integrals by finite
pole sums.

Moving the poles into prescribed components of the complement of `K`, and replacing the poles
in the unbounded component by polynomials, is the pole-pushing step of Runge's theorem, which
is developed separately.

## Main results

* `Complex.exists_finset_pole_approx`: Runge's theorem with poles in `U \ K`.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem VIII.1.7.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Theorem 1.3.1.
-/

public noncomputable section

open Set MeasureTheory Metric Filter

namespace Complex

/-- **Runge's theorem, first form.** A function holomorphic on an open neighborhood `U` of a
compact set `K` is uniformly approximable on `K` by finite sums of simple poles with poles
in `U \ K`. -/
theorem exists_finset_pole_approx {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c a : Fin n → ℂ), (∀ i, c i ∈ U \ K) ∧
      ∀ z ∈ K, ‖f z - ∑ i, a i * (c i - z)⁻¹‖ ≤ ε := by
  obtain ⟨Ω, g, hΩc, hΩUK, hgc, _, hrep⟩ := exists_cauchyPompeiu_representation hK hU hKU hf
  obtain ⟨C, hC⟩ := hΩc.exists_bound_of_continuousOn hgc.continuousOn
  have hdisj : Disjoint Ω K := disjoint_left.mpr fun w hw hwK ↦ (hΩUK hw).2 hwK
  obtain ⟨n, c, a, hcΩ, happrox⟩ := exists_finset_approx_setIntegral_inv_sub hΩc hK hdisj
    (hgc.continuousOn.integrableOn_compact hΩc) hC hε
  refine ⟨n, c, a, fun i ↦ hΩUK (hcΩ i), fun z hz ↦ ?_⟩
  rw [hrep z hz]
  exact happrox z hz

end Complex

end
