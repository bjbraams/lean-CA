/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.Integral.CurveIntegral

/-!
# Pullback of one-forms along mapped paths

Mapping a differentiable path through a differentiable function pulls back a
one-form by composition with the derivative. The change-of-variables identity
holds for the totalized curve integral, without continuity of the form or an
integrability assumption. The map need only be differentiable along the path.

## Main results

* `curveIntegral_map'_of_hasFDerivAt`: Change of variables for curve integrals in real or
  complex normed spaces.
* `curveIntegral_map_segment`: Integrating along a parametrized finite interval agrees with the
  integral of the pulled-back form. The endpoints may occur in either order or coincide.

## References

* `ToMathlib.Analysis.Integral.CurveIntegral`: formal background used by this module.
-/

public section
open Set MeasureTheory
open scoped unitInterval

/-- Change of variables for curve integrals in real or complex normed spaces. -/
theorem curveIntegral_map'_of_hasFDerivAt
    {𝕜 E G F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G] [IsScalarTower ℝ 𝕜 G]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {a b : E} (γ : Path a b) {U : Set E} {g : E → G} {g' : E → E →L[𝕜] G}
    (hg : ∀ x ∈ U, HasFDerivAt g (g' x) x) (hγU : range γ ⊆ U)
    (hγ : DifferentiableOn ℝ γ.extend I) (ω : G → G →L[𝕜] F) :
    curveIntegral ω (γ.map' (fun x hx ↦ (hg x (hγU hx)).continuousAt.continuousWithinAt)) =
      curveIntegral (fun x ↦ (ω (g x)).comp (g' x)) γ := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  rw [curveIntegral_def, curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hz : γ.extend t ∈ U := hγU ⟨projIcc 0 1 zero_le_one t, rfl⟩
  have hd := ((hg _ hz).restrictScalars ℝ).comp_hasDerivWithinAt t
    (hγ t ht).hasDerivWithinAt
  have he : derivWithin (g ∘ γ.extend) I t =
      g' (γ.extend t) (derivWithin γ.extend I t) :=
    hd.derivWithin (uniqueDiffOn_Icc_zero_one t ht)
  simp only [curveIntegralFun_def, ContinuousLinearMap.comp_apply]
  change ω (g (γ.extend t)) (derivWithin (g ∘ γ.extend) I t) = _
  rw [he]

/-- Integrating along a parametrized finite interval agrees with the integral of the
pulled-back form. The endpoints may occur in either order or coincide. -/
theorem curveIntegral_map_segment
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} {γ γ' : ℝ → E} (hγ : ∀ t ∈ uIcc a b, HasDerivAt γ (γ' t) t)
    (ω : E → E →L[ℝ] F) :
    curveIntegral ω ((Path.segment a b).map' (fun t ht ↦
      (hγ t (by
        simpa only [Path.range_segment,
            segment_eq_uIcc] using ht)).continuousAt.continuousWithinAt)) =
      ∫ t in a..b, ω (γ t) (γ' t) := by
  rw [curveIntegral_map'_of_hasFDerivAt (Path.segment a b) (U := uIcc a b)
    (g' := fun t ↦ ContinuousLinearMap.toSpanSingleton ℝ (γ' t))
    (fun t ht ↦ (hγ t ht).hasFDerivAt)
    (by simp only [Path.range_segment, segment_eq_uIcc, subset_refl])
    (show DifferentiableOn ℝ (Path.segment a b).extend I from
      (show DifferentiableOn ℝ (AffineMap.lineMap a b : ℝ → ℝ) I by
        intro t _
        exact AffineMap.hasDerivAt_lineMap.differentiableAt.differentiableWithinAt).congr
          (Path.eqOn_extend_segment a b)), curveIntegral_segment]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    map_smul, intervalIntegral.integral_smul, AffineMap.lineMap_apply_ring']
  simp_rw [mul_comm _ (b - a)]
  rw [intervalIntegral.smul_integral_comp_mul_add (f := fun t ↦ ω (γ t) (γ' t))]
  simp
