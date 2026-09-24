/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.BranchLog
public import Analysis.Integral.CurveIntegral
public import ComplexAnalysis.HasPrimitives
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Complex curve integrals and primitives

Complex Banach-valued functions are integrated using Mathlib's `curveIntegral`, with the
one-form `ContinuousLinearMap.toSpanSingleton ℂ (f z)`, i.e. `v ↦ v • f z`.
We prove endpoint formulas for primitives, path independence for exact functions, and
Cauchy's integral theorem on simply connected open sets. Logarithm branches give an endpoint formula
for the logarithmic derivative on simply connected open sets.

The integral theorems do not assert the Jordan curve theorem or geometric winding-number formulas.

## Main results

* `Complex.curveIntegrable_of_continuousOn`: A continuous complex Banach-valued function is
  integrable along a `C¹` path in its domain.
* `Complex.curveIntegral_eq_zero_of_differentiableOn_isSimplyConnected`: Cauchy's integral
  theorem on a simply connected open domain, for complex Banach-valued functions. Only
  differentiability of the path and existence of its integral are required.
* `Complex.curveIntegral_eq_of_differentiableOn_isSimplyConnected`: The integral of a
  holomorphic function on a simply connected open domain is independent of the choice of `C¹`
  path between its endpoints.
* `Complex.curveIntegral_logDeriv_eq_sub`: Integrating a logarithmic derivative gives the
  endpoint difference of a continuous logarithm branch. The branch is automatically holomorphic.
* `Complex.curveIntegral_logDeriv_eq_zero_of_isSimplyConnected`: A nonvanishing holomorphic
  function on a simply connected open domain has zero logarithmic-derivative integral along
  every closed `C¹` path in the domain.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public section

open Set MeasureTheory
open scoped unitInterval Topology

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {U : Set ℂ} {f P : ℂ → F} {a b : ℂ} {γ : Path a b}

/-- A continuous complex Banach-valued function is integrable along a `C¹` path in its domain. -/
theorem curveIntegrable_of_continuousOn (hf : ContinuousOn f U)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U) :
    CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ :=
  ((ContinuousLinearMap.toSpanSingletonLIE ℂ F).continuous.comp_continuousOn
      hf).curveIntegrable_of_contDiffOn
    hγ hγU

variable [CompleteSpace F]

/-- The complex integral of a function with a primitive is its primitive's endpoint difference. -/
theorem curveIntegral_eq_sub_of_hasDerivAt
    (hP : ∀ z ∈ U, HasDerivAt P (f z) z)
    (hγ : DifferentiableOn ℝ γ.extend I) (hγU : ∀ t, γ t ∈ U)
    (hint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ = P b - P a :=
  _root_.curveIntegral_eq_sub_of_hasFDerivAt (fun z hz => (hP z hz).hasFDerivAt) hγ hγU hint

/-- A complex function with a primitive has zero integral along every closed differentiable
path on which the integral exists. -/
theorem IsExactOn.curveIntegral_eq_zero (hf : IsExactOn f U) {γ : Path a a}
    (hγ : DifferentiableOn ℝ γ.extend I) (hγU : ∀ t, γ t ∈ U)
    (hint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ = 0 := by
  obtain ⟨P, hP⟩ := hf
  rw [curveIntegral_eq_sub_of_hasDerivAt hP hγ hγU hint, sub_self]

/-- Integrals of a function with a primitive agree on paths with the same endpoints. -/
theorem IsExactOn.curveIntegral_eq (hf : IsExactOn f U) {δ : Path a b}
    (hγ : DifferentiableOn ℝ γ.extend I) (hδ : DifferentiableOn ℝ δ.extend I)
    (hγU : ∀ t, γ t ∈ U) (hδU : ∀ t, δ t ∈ U)
    (hγint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ)
    (hδint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ =
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ := by
  obtain ⟨P, hP⟩ := hf
  rw [curveIntegral_eq_sub_of_hasDerivAt hP hγ hγU hγint,
    curveIntegral_eq_sub_of_hasDerivAt hP hδ hδU hδint]

/-- Cauchy's integral theorem on a convex open domain, for complex Banach-valued functions. -/
theorem curveIntegral_eq_zero_of_differentiableOn_convex (hU : IsOpen U)
    (hUc : Convex ℝ U) (hf : DifferentiableOn ℂ f U) {γ : Path a a}
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ = 0 := by
  obtain ⟨P, hP⟩ := hUc.exists_forall_hasDerivWithinAt hf
  have hex : IsExactOn f U := ⟨P, fun z hz => (hP z hz).hasDerivAt (hU.mem_nhds hz)⟩
  exact hex.curveIntegral_eq_zero (hγ.differentiableOn one_ne_zero) hγU
    (curveIntegrable_of_continuousOn hf.continuousOn hγ hγU)

/-- Cauchy's integral theorem on a simply connected open domain, for complex Banach-valued
functions. Only differentiability of the path and existence of its integral are required. -/
theorem curveIntegral_eq_zero_of_differentiableOn_isSimplyConnected
    (hU : IsOpen U) (hUc : IsSimplyConnected U) (hf : DifferentiableOn ℂ f U)
    {γ : Path a a} (hγ : DifferentiableOn ℝ γ.extend I) (hγU : ∀ t, γ t ∈ U)
    (hint : CurveIntegrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ = 0 :=
  (hf.isExactOn_of_isSimplyConnected hU hUc).curveIntegral_eq_zero hγ hγU hint

/-- The integral of a holomorphic function on a simply connected open domain is independent
of the choice of `C¹` path between its endpoints. -/
theorem curveIntegral_eq_of_differentiableOn_isSimplyConnected
    (hU : IsOpen U) (hUc : IsSimplyConnected U) (hf : DifferentiableOn ℂ f U)
    {δ : Path a b} (hγ : ContDiffOn ℝ 1 γ.extend I) (hδ : ContDiffOn ℝ 1 δ.extend I)
    (hγU : ∀ t, γ t ∈ U) (hδU : ∀ t, δ t ∈ U) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ =
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ :=
  (hf.isExactOn_of_isSimplyConnected hU hUc).curveIntegral_eq
    (hγ.differentiableOn one_ne_zero) (hδ.differentiableOn one_ne_zero) hγU hδU
    (curveIntegrable_of_continuousOn hf.continuousOn hγ hγU)
    (curveIntegrable_of_continuousOn hf.continuousOn hδ hδU)

/-- Integrating a logarithmic derivative gives the endpoint difference of a continuous
logarithm branch. The branch is automatically holomorphic. -/
theorem curveIntegral_logDeriv_eq_sub {g L : ℂ → ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (hL : ContinuousOn L U)
    (heq : EqOn (exp ∘ L) g U)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (deriv g z / g z)) γ =
      L b - L a := by
  have hg0 : ∀ z ∈ U, g z ≠ 0 := fun z hz => by
    rw [← heq hz]
    exact exp_ne_zero _
  have hc : ContinuousOn (fun z => deriv g z / g z) U :=
    (hg.analyticOnNhd hU).deriv.continuousOn.div hg.continuousOn hg0
  apply curveIntegral_eq_sub_of_hasDerivAt (U := U) (P := L) _
    (hγ.differentiableOn one_ne_zero) hγU (curveIntegrable_of_continuousOn hc hγ hγU)
  intro z hz
  exact hasDerivAt_logBranch (hL.continuousAt (hU.mem_nhds hz))
    ((hg z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
    (heq.eventuallyEq_of_mem (hU.mem_nhds hz))

/-- A nonvanishing holomorphic function on a simply connected open domain has zero
logarithmic-derivative integral along every closed `C¹` path in the domain. -/
theorem curveIntegral_logDeriv_eq_zero_of_isSimplyConnected {g : ℂ → ℂ}
    (hU : IsOpen U) (hUc : IsSimplyConnected U) (hg : DifferentiableOn ℂ g U)
    (hg0 : ∀ z ∈ U, g z ≠ 0) {γ : Path a a}
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (deriv g z / g z)) γ = 0 := by
  obtain ⟨L, hL, heq⟩ := exists_analyticOnNhd_logBranch hU hUc hg hg0
  rw [curveIntegral_logDeriv_eq_sub hU hg hL.continuousOn heq hγ hγU, sub_self]

end Complex
