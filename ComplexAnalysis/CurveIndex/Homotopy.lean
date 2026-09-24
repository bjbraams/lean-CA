/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CurveIndex
public import ComplexAnalysis.Integral.Homotopy
public import ComplexAnalysis.Integral.ContinuousHomotopy

/-!
# Homotopy invariance of the analytic curve index

The analytic index of `C¹` loops is unchanged by a continuous based homotopy
avoiding the pole. In particular it vanishes for a loop contractible in the
punctured plane. The older `C²` homotopy statements remain available. These are
statements about the analytic curve index; no index for arbitrary continuous
loops is introduced here.

## Main results

* `Complex.curveIndex_eq_of_homotopy`: The analytic index is invariant under a smooth based
  homotopy avoiding the pole.
* `Complex.curveIndex_eq_zero_of_nullhomotopy`: A loop admitting a smooth contraction away from
  the pole has analytic index zero.
* `Complex.curveIndex_eq_of_continuous_homotopy`: The analytic index of `C¹` loops is invariant
  under any continuous based homotopy avoiding the pole. Intermediate loops need not be
  differentiable.
* `Complex.curveIndex_eq_zero_of_continuous_nullhomotopy`: A `C¹` loop contractible in the
  punctured plane has analytic index zero, without a smoothness assumption on the contraction.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public section
open Set
open scoped unitInterval
namespace Complex

/-- The analytic index is invariant under a smooth based homotopy avoiding the pole. -/
theorem curveIndex_eq_of_homotopy {a w : ℂ} {γ δ : Path a a} (H : γ.Homotopy δ)
    (hw : ∀ p, H p ≠ w)
    (hH : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => IccExtend zero_le_one (H.toHomotopy.extend p.1) p.2) (Icc 0 1)) :
    curveIndex γ w = curveIndex δ w := by
  apply congrArg ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ·)
  exact curveIntegral_eq_of_homotopy H (isOpen_compl_singleton (x := w))
    ((differentiableOn_id.sub_const w).inv (fun z hz => sub_ne_zero.mpr hz))
    (by rintro _ ⟨p, rfl⟩; exact hw p) hH

/-- A loop admitting a smooth contraction away from the pole has analytic index zero. -/
theorem curveIndex_eq_zero_of_nullhomotopy {a w : ℂ} {γ : Path a a}
    (H : γ.Homotopy (Path.refl a)) (hw : ∀ p, H p ≠ w)
    (hH : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => IccExtend zero_le_one (H.toHomotopy.extend p.1) p.2) (Icc 0 1)) :
    curveIndex γ w = 0 := by
  rw [curveIndex_eq_of_homotopy H hw hH, curveIndex_refl]

/-- The analytic index of `C¹` loops is invariant under any continuous based homotopy
avoiding the pole. Intermediate loops need not be differentiable. -/
theorem curveIndex_eq_of_continuous_homotopy {a w : ℂ} {γ δ : Path a a}
    (H : γ.Homotopy δ) (hw : ∀ p, H p ≠ w)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hδ : ContDiffOn ℝ 1 δ.extend I) :
    curveIndex γ w = curveIndex δ w := by
  apply congrArg ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ·)
  exact curveIntegral_eq_of_continuous_homotopy_of_contDiffOn H
    (isOpen_compl_singleton (x := w))
    ((differentiableOn_id.sub_const w).inv (fun z hz => sub_ne_zero.mpr hz))
    (by rintro _ ⟨p, rfl⟩; exact hw p) hγ hδ

/-- A `C¹` loop contractible in the punctured plane has analytic index zero,
without a smoothness assumption on the contraction. -/
theorem curveIndex_eq_zero_of_continuous_nullhomotopy {a w : ℂ} {γ : Path a a}
    (H : γ.Homotopy (Path.refl a)) (hw : ∀ p, H p ≠ w)
    (hγ : ContDiffOn ℝ 1 γ.extend I) : curveIndex γ w = 0 := by
  rw [curveIndex_eq_of_continuous_homotopy H hw hγ (by simp; fun_prop), curveIndex_refl]

end Complex
