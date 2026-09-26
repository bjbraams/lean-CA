/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CauchyIntegral

/-!
# Cauchy's theorem under smooth path deformation

Holomorphic Banach-valued functions define closed complex one-forms. Mathlib's
deformation theorem for closed forms therefore gives Cauchy's theorem for a `C²`
homotopy whose image stays in the domain of holomorphy. The domain need not be
simply connected. We first retain the two endpoint tracks, then specialize to a
homotopy relative to the endpoints.

Smoothness is expressed using Mathlib's extensions of continuous homotopies to
the real unit square. No smoothness or analyticity outside that square is assumed.

## Main results

* `Complex.curveIntegral_add_curveIntegral_eq_of_homotopy`: Cauchy's theorem for the boundary of
  a smooth homotopy, including its endpoint tracks.
* `Complex.curveIntegral_eq_of_homotopy`: Holomorphic curve integrals are invariant under a `C²`
  homotopy fixing the endpoints. Only the image of the homotopy must lie in the open domain of
  holomorphy.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public section
open Set MeasureTheory
open scoped unitInterval

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {U : Set ℂ} {f : ℂ → F} {a b c d : ℂ}

/-- Cauchy's theorem for the boundary of a smooth homotopy, including its endpoint tracks. -/
theorem curveIntegral_add_curveIntegral_eq_of_homotopy
    {γ : Path a b} {δ : Path c d} (H : (γ : C(I, ℂ)).Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hH : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ ↦ IccExtend zero_le_one (H.extend p.1) p.2) (Icc 0 1)) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ +
        curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 1) =
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ +
        curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) (H.evalAt 0) := by
  let : NormedSpace ℝ F := .restrictScalars ℝ ℂ F
  have hd (z : ℂ) (hz : z ∈ range H) :
      HasFDerivAt (fun w ↦ ContinuousLinearMap.toSpanSingleton ℂ (f w))
        ((ContinuousLinearMap.toSpanSingleton ℂ
          (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z))).restrictScalars ℝ) z :=
    (ContinuousLinearMap.smulRightL ℂ ℂ F 1).hasFDerivAt
      |>.comp_hasDerivAt z ((hf z (hHU hz)).differentiableAt (hU.mem_nhds (hHU hz))).hasDerivAt
      |>.restrictScalars ℝ
  apply H.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt (t := range H)
    (fun _ _ _ _ ↦ mem_range_self _) (fun z hz ↦ (hd z hz).hasFDerivWithinAt)
  · rw [(isCompact_range H.continuous).isClosed.closure_eq]
    exact ((ContinuousLinearMap.toSpanSingletonLIE ℂ F).continuous.comp_continuousOn
      hf.continuousOn).mono hHU
  · intro z hz u _ v _
    simpa using smul_comm u v (deriv f z)
  · exact hH

/-- Holomorphic curve integrals are invariant under a `C²` homotopy fixing the endpoints.
Only the image of the homotopy must lie in the open domain of holomorphy. -/
theorem curveIntegral_eq_of_homotopy {γ δ : Path a b} (H : γ.Homotopy δ)
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hHU : range H ⊆ U)
    (hH : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ ↦ IccExtend zero_le_one (H.toHomotopy.extend p.1) p.2) (Icc 0 1)) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ =
      curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z)) δ := by
  have hzero : H.toHomotopy.evalAt 0 = (Path.refl a).cast γ.source δ.source := by
    ext t
    exact H.source t
  have hone : H.toHomotopy.evalAt 1 = (Path.refl b).cast γ.target δ.target := by
    ext t
    exact H.target t
  simpa only [hzero, hone, curveIntegral_cast, curveIntegral_refl, add_zero] using
    curveIntegral_add_curveIntegral_eq_of_homotopy H.toHomotopy hU hf hHU hH

end Complex
