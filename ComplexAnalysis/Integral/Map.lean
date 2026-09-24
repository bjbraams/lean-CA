/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CauchyIntegral

/-!
# Holomorphic changes of variables in curve integrals

Mapping a differentiable path through a holomorphic function pulls back the integrand
with the complex derivative as its scalar factor. Only a neighborhood of the path needs
to belong to the domain of holomorphy.

## Main results

* `Complex.contDiffOn_path_map'`: A holomorphic map preserves the smoothness of a path contained
  in its domain.
* `Complex.curveIntegral_map'`: Holomorphic change of variables for a complex Banach-valued
  curve integral.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section
open Set MeasureTheory
open scoped unitInterval

namespace Complex

/-- A holomorphic map preserves the smoothness of a path contained in its domain. -/
theorem contDiffOn_path_map' {a b : ℂ} (γ : Path a b) {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hγU : range γ ⊆ U)
    {n : WithTop ℕ∞} (hγ : ContDiffOn ℝ n γ.extend I) :
    ContDiffOn ℝ n (γ.map' (hg.continuousOn.mono hγU)).extend I := by
  have hg' : ContDiffOn ℝ n g U :=
    (hg.analyticOnNhd hU).contDiffOn_of_completeSpace.restrict_scalars ℝ
  exact hg'.comp hγ (fun t _ => hγU ⟨projIcc 0 1 zero_le_one t, rfl⟩)

/-- Holomorphic change of variables for a complex Banach-valued curve integral. -/
theorem curveIntegral_map' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {a b : ℂ} (γ : Path a b) {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hγU : range γ ⊆ U)
    (hγ : DifferentiableOn ℝ γ.extend I) (f : ℂ → F) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))
        (γ.map' (hg.continuousOn.mono hγU)) =
      curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (deriv g z • f (g z))) γ := by
  rw [curveIntegral_def, curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hz : γ.extend t ∈ U := hγU ⟨projIcc 0 1 zero_le_one t, rfl⟩
  have hgf := ((hg _ hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hd := hgf.comp_hasDerivWithinAt t (hγ t ht).hasDerivWithinAt
  have he : derivWithin (γ.map' (hg.continuousOn.mono hγU)).extend I t =
      derivWithin γ.extend I t * deriv g (γ.extend t) := by
    have hm : ⇑(γ.map' (hg.continuousOn.mono hγU)).extend = g ∘ γ.extend := rfl
    rw [hm]
    simpa only [ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using
      hd.derivWithin (uniqueDiffOn_Icc_zero_one t ht)
  simp only [curveIntegralFun_def, ContinuousLinearMap.toSpanSingleton_apply, he,
    mul_smul]
  rfl

end Complex
