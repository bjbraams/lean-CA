/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Cycle.Parallelogram

/-!
# The boundary integral of a doubly periodic function over a period parallelogram vanishes

For `f` periodic with respect to both `w1` and `w2` and continuous on the boundary of the
parallelogram `c, c + w1, c + w1 + w2, c + w2`, the contour integral of `f` around that
boundary vanishes: the contributions of opposite edges cancel exactly, since one edge is the
periodic translate of the other, traversed in the opposite direction. This is the elementary
half of Liouville's second and third theorems for elliptic functions (the sum of residues in a
period parallelogram is zero, and the number of zeros equals the number of poles); the other
half is the residue theorem / argument principle for cycles, applied using the parallelogram's
index (`Complex.curveIndex_parallelogramLoop_eq_one` / `_eq_zero`, `Cycle.Parallelogram`).

The parallelogram loop is the closed polygon through its vertices (`Complex.Loop.polygon`), so
its integral is the sum of four edge integrals over `[0, 1]` in the affine parametrization
(`Complex.Loop.curveIntegral_polygon`). Opposite edges cancel by the substitution `t ↦ 1 - t`
and periodicity; this step needs no continuity of `f`.

## Main results

* `Complex.integral_segment_add_integral_opposite_segment_eq_zero`: the integrals over an edge
  and over its periodic translate traversed backwards cancel.
* `Complex.curveIntegral_toSpanSingleton_parallelogramLoop_eq_zero`: the boundary integral of a
  doubly periodic function over a period parallelogram vanishes.

## References

* R. Remmert, *Theory of Complex Functions*, Chapter 9, Section 1.
-/

public noncomputable section

open Set MeasureTheory ContinuousLinearMap

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Opposite edges cancel.** For `f` periodic with period `w`, the integral over the edge from
`a` to `b` and the integral over its translate by `w` traversed from `b + w` to `a + w` cancel.
The edge integrals are written in the affine parametrization over `[0, 1]`. -/
theorem integral_segment_add_integral_opposite_segment_eq_zero {f : ℂ → F} {w : ℂ}
    (hper : Function.Periodic f w) {a b a' b' : ℂ} (ha' : a' = b + w) (hb' : b' = a + w) :
    (∫ t in (0 : ℝ)..1, (b - a) • f (AffineMap.lineMap a b t)) +
      ∫ t in (0 : ℝ)..1, (b' - a') • f (AffineMap.lineMap a' b' t) = 0 := by
  have hrev := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ ↦ (b - a) • f (AffineMap.lineMap a b t)) (1 : ℝ) (a := 0) (b := 1)
  simp only [sub_self, sub_zero] at hrev
  have hsecond : (∫ t in (0 : ℝ)..1, (b' - a') • f (AffineMap.lineMap a' b' t)) =
      ∫ t in (0 : ℝ)..1, -((b - a) • f (AffineMap.lineMap a b (1 - t))) := by
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    have hline : AffineMap.lineMap a' b' t = AffineMap.lineMap a b (1 - t) + w := by
      simp only [ha', hb', AffineMap.lineMap_apply_module]
      module
    rw [hline, hper, ha', hb', ← neg_smul]
    congr 1
    ring
  rw [hsecond, intervalIntegral.integral_neg, hrev, add_neg_cancel]

/-- **The boundary integral of a doubly periodic function over a period parallelogram
vanishes.** Opposite edges cancel exactly: each is the periodic translate of the other,
traversed in the opposite direction. Only continuity on the boundary is assumed. -/
theorem curveIntegral_toSpanSingleton_parallelogramLoop_eq_zero {c w1 w2 : ℂ} {f : ℂ → F}
    (hf : ContinuousOn f (parallelogramBoundary c w1 w2)) (hper1 : Function.Periodic f w1)
    (hper2 : Function.Periodic f w2) :
    curveIntegral (fun z ↦ toSpanSingleton ℂ (f z)) (parallelogramLoop c w1 w2) = 0 := by
  rw [curveIntegral_parallelogramLoop (fun z ↦ toSpanSingleton ℂ (f z))
    ((toSpanSingletonLIE ℂ F).continuous.comp_continuousOn hf), Fin.sum_univ_four]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [toSpanSingleton_apply, parallelogramVertex, Fin.val_zero, Fin.val_one, Fin.val_two,
    h3, Fin.isValue]
  have h13 := integral_segment_add_integral_opposite_segment_eq_zero hper2
    (a := c) (b := c + w1) (a' := c + w1 + w2) (b' := c + w2) rfl rfl
  have h24 := integral_segment_add_integral_opposite_segment_eq_zero hper1.neg
    (a := c + w1) (b := c + w1 + w2) (a' := c + w2) (b' := c) (by ring) (by ring)
  have h := congrArg₂ (· + ·) h13 h24
  simp only [add_zero] at h
  rw [← h]
  abel

end Complex

end
