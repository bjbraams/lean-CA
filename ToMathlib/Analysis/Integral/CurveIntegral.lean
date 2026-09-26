/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Integrating exact one-forms along curves

The fundamental theorem for Mathlib's `curveIntegral`: integration of the derivative of a
potential gives its endpoint difference. The potential may take values in a Banach space and
the source may be any real or complex normed space. The basic result assumes differentiability
of the path and integrability of the form along it; a continuous form on a `C¹` path supplies
the latter automatically.

## Main results

* `curveIntegral_eq_sub_of_hasFDerivAt`: The integral of the derivative of a potential is its
  endpoint difference.
* `curveIntegral_eq_zero_of_hasFDerivAt`: An exact form has zero integral along a closed
  differentiable path.
* `curveIntegral_congr`: Curve integrals depend only on the values of the form along the path.
* `curveIntegral_segment_eq_sub_of_hasFDerivAt`: Integrating a continuous exact form along a
  segment gives its endpoint difference.
* `ContinuousLinearMap.curveIntegral_comp_comm`: A continuous linear map commutes with a curve
  integral.

## References

* `Mathlib.MeasureTheory.Integral.CurveIntegral.Basic`: formal background used by this module.
* `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`: formal background used by
  this module.
* `Mathlib.Analysis.Calculus.ContDiff.Operations`: formal background used by this module.
-/

public section

open Set MeasureTheory
open scoped unitInterval Topology

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {a b : E} {U : Set E} {f : E → F} {ω : E → E →L[𝕜] F} {γ : Path a b}

/-- The integral of the derivative of a potential is its endpoint difference. -/
theorem curveIntegral_eq_sub_of_hasFDerivAt
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (hf : ∀ x ∈ U, HasFDerivAt f (ω x) x)
    (hγ : DifferentiableOn ℝ γ.extend I) (hγU : ∀ t, γ t ∈ U)
    (hint : CurveIntegrable ω γ) : curveIntegral ω γ = f b - f a := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  have hmap : MapsTo γ.extend I U := fun t ht ↦ by
    rw [γ.extend_apply ht]
    exact hγU _
  have hc : ContinuousOn (f ∘ γ.extend) I :=
    (show ContinuousOn f U from fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt).comp
      γ.continuous_extend.continuousOn hmap
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (f ∘ γ.extend) (curveIntegralFun ω γ t) t := by
    have htI : t ∈ I := ⟨ht.1.le, ht.2.le⟩
    rw [curveIntegralFun_def, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact ((hf _ (hmap htI)).restrictScalars ℝ).comp_hasDerivAt t
      ((hγ t htI).differentiableAt (Icc_mem_nhds ht.1 ht.2)).hasDerivAt
  simpa only [curveIntegral_def, Function.comp_apply, γ.extend_one, γ.extend_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hd hint

/-- A continuous exact form integrates to the endpoint difference along every `C¹` path. -/
theorem curveIntegral_eq_sub_of_hasFDerivAt_of_contDiffOn
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (hf : ∀ x ∈ U, HasFDerivAt f (ω x) x) (hω : ContinuousOn ω U)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ t, γ t ∈ U) :
    curveIntegral ω γ = f b - f a :=
  curveIntegral_eq_sub_of_hasFDerivAt hf (hγ.differentiableOn one_ne_zero) hγU
    (hω.curveIntegrable_of_contDiffOn hγ hγU)

/-- An exact form has zero integral along a closed differentiable path. -/
theorem curveIntegral_eq_zero_of_hasFDerivAt
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] {γ : Path a a}
    (hf : ∀ x ∈ U, HasFDerivAt f (ω x) x)
    (hγ : DifferentiableOn ℝ γ.extend I) (hγU : ∀ t, γ t ∈ U)
    (hint : CurveIntegrable ω γ) : curveIntegral ω γ = 0 := by
  rw [curveIntegral_eq_sub_of_hasFDerivAt hf hγ hγU hint, sub_self]

omit [CompleteSpace F] in
/-- Curve integrals depend only on the values of the form along the path. -/
theorem curveIntegral_congr {ω₁ ω₂ : E → E →L[𝕜] F}
    (h : ∀ t, ω₁ (γ t) = ω₂ (γ t)) : curveIntegral ω₁ γ = curveIntegral ω₂ γ := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  rw [curveIntegral_def, curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  simp only [curveIntegralFun_def, γ.extend_apply ht, h ⟨t, ht⟩]

/-- Integrating a continuous exact form along a segment gives its endpoint difference. -/
theorem curveIntegral_segment_eq_sub_of_hasFDerivAt
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    (hf : ∀ x ∈ U, HasFDerivAt f (ω x) x) (hω : ContinuousOn ω U)
    (hab : segment ℝ a b ⊆ U) : curveIntegral ω (Path.segment a b) = f b - f a := by
  apply curveIntegral_eq_sub_of_hasFDerivAt_of_contDiffOn hf hω
  · exact (show ContDiff ℝ 1 (AffineMap.lineMap a b : ℝ → E) by
      change ContDiff ℝ 1 (fun t : ℝ ↦ t • (b - a) + a)
      fun_prop).contDiffOn.congr
      (Path.eqOn_extend_segment a b)
  · intro t
    exact hab (by simpa using (Convex.lineMap_mem (convex_segment a b)
      (left_mem_segment ℝ a b) (right_mem_segment ℝ a b) t.2))

/-- A continuous linear map commutes with a curve integral. -/
theorem ContinuousLinearMap.curveIntegral_comp_comm
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    (L : F →L[𝕜] G) (hint : CurveIntegrable ω γ) :
    curveIntegral (fun x ↦ L.comp (ω x)) γ = L (curveIntegral ω γ) := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  let : NormedSpace ℝ G := .restrictScalars ℝ 𝕜 G
  simpa only [curveIntegral_def, curveIntegralFun_def, ContinuousLinearMap.comp_apply] using
    L.intervalIntegral_comp_comm hint
