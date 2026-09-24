/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Holomorphic logarithm branches

A continuous logarithm of a holomorphic function is holomorphic, with derivative `g' / g`.
Combining this local fact with Mathlib's covering-space construction gives logarithms on
simply connected open subsets of the plane. A branch can be normalized at a chosen point;
on a connected domain the normalization determines it uniquely.

No principal-branch or slit-plane hypothesis is imposed on the image of the function.

## Main results

* `Complex.hasDerivAt_logBranch`: A continuous local logarithm of a differentiable function has
  derivative `g' / g`.
* `Complex.exists_analyticOnNhd_logBranch`: A nonvanishing holomorphic function on a simply
  connected open set has a holomorphic logarithm.
* `Complex.exists_analyticOnNhd_logBranch_eq`: A holomorphic logarithm can be prescribed at one
  point, provided its exponential has the required value there.
* `Complex.eqOn_logBranch_of_eq`: Two continuous logarithm branches of a holomorphic function on
  a connected open set agree everywhere if they agree at one point.
* `Complex.exists_analyticOnNhd_root`: A nonvanishing holomorphic function on a simply connected
  open set has a holomorphic `n`th root for every nonzero natural number `n`.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public section

open Set Filter
open scoped Topology

namespace Complex

/-- A continuous local logarithm of a differentiable function has derivative `g' / g`. -/
theorem hasDerivAt_logBranch {g L : ℂ → ℂ} {z g' : ℂ}
    (hL : ContinuousAt L z) (hg : HasDerivAt g g' z)
    (heq : exp ∘ L =ᶠ[𝓝 z] g) : HasDerivAt L (g' / g z) z := by
  have h := HasDerivAt.of_comp_left hL (hasDerivAt_exp (L z)) hg (exp_ne_zero _) heq
  simpa only [show exp (L z) = g z from heq.self_of_nhds] using h

/-- Every continuous logarithm branch of a holomorphic function is holomorphic. -/
theorem differentiableOn_logBranch {U : Set ℂ} (hU : IsOpen U) {g L : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (hL : ContinuousOn L U)
    (heq : EqOn (exp ∘ L) g U) : DifferentiableOn ℂ L U := by
  intro z hz
  exact (hasDerivAt_logBranch (hL.continuousAt (hU.mem_nhds hz))
    ((hg z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
    (heq.eventuallyEq_of_mem (hU.mem_nhds hz))).differentiableAt.differentiableWithinAt

/-- The derivative of a continuous logarithm branch is the logarithmic derivative. -/
theorem deriv_logBranch {U : Set ℂ} (hU : IsOpen U) {g L : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (hL : ContinuousOn L U)
    (heq : EqOn (exp ∘ L) g U) {z : ℂ} (hz : z ∈ U) :
    deriv L z = deriv g z / g z :=
  (hasDerivAt_logBranch (hL.continuousAt (hU.mem_nhds hz))
    ((hg z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
    (heq.eventuallyEq_of_mem (hU.mem_nhds hz))).deriv

/-- A nonvanishing holomorphic function on a simply connected open set has a holomorphic
logarithm.

A disk-domain counterpart is formalized in Geoffrey Irving's `ray` project. See `CREDITS.md`. -/
theorem exists_analyticOnNhd_logBranch {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hg0 : ∀ z ∈ U, g z ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L U ∧ EqOn (exp ∘ L) g U := by
  obtain ⟨L, hL, heq⟩ := exists_continuousOn_eqOn_exp_comp hUc hU hg.continuousOn
    (by rintro ⟨z, hz, heq⟩; exact hg0 z hz heq)
  exact ⟨L, (differentiableOn_logBranch hU hg hL heq).analyticOnNhd hU, heq⟩

/-- A holomorphic logarithm can be prescribed at one point, provided its exponential has
the required value there.

A disk-domain counterpart is formalized in Geoffrey Irving's `ray` project. See `CREDITS.md`. -/
theorem exists_analyticOnNhd_logBranch_eq {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hg0 : ∀ z ∈ U, g z ≠ 0) {z₀ w₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hw₀ : exp w₀ = g z₀) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L U ∧ EqOn (exp ∘ L) g U ∧ L z₀ = w₀ := by
  obtain ⟨L, hL, heq⟩ := exists_analyticOnNhd_logBranch hU hUc hg hg0
  refine ⟨fun z => L z + (w₀ - L z₀), hL.add analyticOnNhd_const, ?_, by ring⟩
  intro z hz
  simp only [Function.comp_apply, exp_add, exp_sub]
  change ∀ z ∈ U, exp (L z) = g z at heq
  rw [heq z hz, hw₀, heq z₀ hz₀, div_self (hg0 z₀ hz₀), mul_one]

/-- Two continuous logarithm branches of a holomorphic function on a connected open set
agree everywhere if they agree at one point. -/
theorem eqOn_logBranch_of_eq {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {g L M : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hL : ContinuousOn L U) (hM : ContinuousOn M U)
    (heL : EqOn (exp ∘ L) g U) (heM : EqOn (exp ∘ M) g U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h₀ : L z₀ = M z₀) : EqOn L M U := by
  apply hU.eqOn_of_deriv_eq hUc (differentiableOn_logBranch hU hg hL heL)
    (differentiableOn_logBranch hU hg hM heM) _ hz₀ h₀
  intro z hz
  rw [deriv_logBranch hU hg hL heL hz, deriv_logBranch hU hg hM heM hz]

/-- A nonvanishing holomorphic function on a simply connected open set has a holomorphic
`n`th root for every nonzero natural number `n`. -/
theorem exists_analyticOnNhd_root {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hg0 : ∀ z ∈ U, g z ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r U ∧ ∀ z ∈ U, r z ^ n = g z := by
  obtain ⟨L, hL, heq⟩ := exists_analyticOnNhd_logBranch hU hUc hg hg0
  refine ⟨fun z => exp (L z / n), hL.div_const.cexp, ?_⟩
  intro z hz
  rw [← exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn)]
  exact heq hz

end Complex
