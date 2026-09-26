/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.ExteriorPath
public import Analysis.Integral.CurveIntegral.Improper
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Integrating exact functions along compactified exterior paths

The compactified coordinate increases from infinity to the finite endpoint.
Its reversed Jacobian therefore computes the integral from the finite endpoint
to infinity. For a function with a primitive, this integral is the limiting
primitive value minus its value at the finite endpoint. The target can be any
complex Banach space. Convergence of the potential and integrability of the
pulled-back function are separate, explicit assumptions.

## Main results

* `Complex.hasDerivAt_compactifiedRay_ofReal`: The derivative of an exterior path with respect
  to its real compactifying coordinate.
* `Complex.integral_compactifiedRay_eq_sub`: A compactified exterior integral of an exact
  function is the limiting primitive value minus its value at the finite endpoint. The sign
  corresponds to integration towards infinity.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public section
open Set Filter MeasureTheory
open scoped Topology
namespace Complex

/-- The derivative of an exterior path with respect to its real compactifying coordinate. -/
theorem hasDerivAt_compactifiedRay_ofReal {q : ℂ → ℂ} (t : ℂ) {u : ℝ}
    (hq : DifferentiableAt ℂ q (u : ℂ)) (hu : u ≠ 0) :
    HasDerivAt (fun v : ℝ ↦ compactifiedRay q t (v : ℂ))
      (-compactifiedRayJacobian q (u : ℂ) / (u : ℂ) ^ 2) u :=
  (hasDerivAt_compactifiedRay t hq (ofReal_ne_zero.mpr hu)).comp_ofReal

/-- A compactified exterior integral of an exact function is the limiting primitive value
minus its value at the finite endpoint. The sign corresponds to integration towards infinity. -/
theorem integral_compactifiedRay_eq_sub
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {P f : ℂ → F} {q : ℂ → ℂ} {t : ℂ} {l : F}
    (hP : ∀ z ∈ U, HasDerivAt P (f z) z)
    (hq : ∀ u ∈ Ioc (0 : ℝ) 1, DifferentiableAt ℂ q (u : ℂ))
    (hU : ∀ u ∈ Ioc (0 : ℝ) 1, compactifiedRay q t (u : ℂ) ∈ U)
    (hint : IntervalIntegrable (fun u : ℝ ↦
      (compactifiedRayJacobian q (u : ℂ) / (u : ℂ) ^ 2) •
        f (compactifiedRay q t (u : ℂ))) volume 0 1)
    (hlim : Tendsto (fun u : ℝ ↦ P (compactifiedRay q t (u : ℂ))) (𝓝[>] 0) (𝓝 l)) :
    ∫ u in (0 : ℝ)..1, (compactifiedRayJacobian q (u : ℂ) / (u : ℂ) ^ 2) •
      f (compactifiedRay q t (u : ℂ)) = l - P t := by
  have ht : t ∈ U := by simpa using hU 1 ⟨zero_lt_one, le_rfl⟩
  have hend : Tendsto (fun u : ℝ ↦ P (compactifiedRay q t (u : ℂ)))
      (𝓝[<] 1) (𝓝 (P t)) := by
    have hc := (hasDerivAt_compactifiedRay_ofReal t (hq 1 ⟨zero_lt_one, le_rfl⟩)
      one_ne_zero).continuousAt
    have hc' : Tendsto (fun u : ℝ ↦ compactifiedRay q t (u : ℂ)) (𝓝 1) (𝓝 t) := by
      simpa only [ofReal_one, compactifiedRay_one] using hc.tendsto
    exact ((hP t ht).continuousAt.tendsto.comp hc').mono_left inf_le_left
  have heq := integral_eq_sub_of_hasFDerivAt_of_tendsto zero_lt_one
    (fun z hz ↦ (hP z hz).hasFDerivAt)
    (fun u hu ↦ hasDerivAt_compactifiedRay_ofReal t (hq u ⟨hu.1, hu.2.le⟩) hu.1.ne')
    (fun u hu ↦ hU u ⟨hu.1, hu.2.le⟩)
    (show IntervalIntegrable (fun u : ℝ ↦
      ContinuousLinearMap.toSpanSingleton ℂ (f (compactifiedRay q t (u : ℂ)))
        (-compactifiedRayJacobian q (u : ℂ) / (u : ℂ) ^ 2)) volume 0 1 by
      convert hint.neg using 1
      ext u
      simp only [ContinuousLinearMap.toSpanSingleton_apply, neg_div, neg_smul, Pi.neg_apply])
    hlim hend
  simp only [ContinuousLinearMap.toSpanSingleton_apply, neg_div, neg_smul,
    intervalIntegral.integral_neg] at heq
  exact neg_eq_iff_eq_neg.mp heq |>.trans (neg_sub _ _)

end Complex
