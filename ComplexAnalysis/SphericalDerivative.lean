/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import ComplexAnalysis.ChordalMetric

/-!
# The spherical derivative

The spherical derivative `f#(z) = |f'(z)| / (1 + |f(z)|²)` of a holomorphic function measures
the local distortion of the chordal metric (`ChordalMetric.lean`) under `f`: it is the
infinitesimal ratio of chordal length in the target to Euclidean length in the source,
`f#(z) = lim_{w → z} chordalDist (f w) (f z) / ‖w - z‖` (this limit characterization is not
proved here). Unlike the ordinary derivative, the spherical derivative is unchanged under
post-composition with the inversion `w ↦ 1/w`, reflecting that inversion is a chordal isometry
of the sphere — this is the one structural property proved in this file.

## Main definitions

* `Complex.sphericalDeriv f z = ‖deriv f z‖ / (1 + ‖f z‖ ^ 2)`.

## Main results

* `Complex.sphericalDeriv_nonneg`.
* `Complex.sphericalDeriv_inv`: the spherical derivative of `1 / f` agrees with that of `f`
  wherever `f` is differentiable and nonzero.

## References

* L. V. Ahlfors, *Complex Analysis*, Chapter 1, Section 2.3; Chapter 5, Section 3.2.
* J. B. Conway, *Functions of One Complex Variable*, Chapter 1, Section 6.
-/

public noncomputable section

namespace Complex

/-- **The spherical derivative.** The local distortion factor of the chordal metric under a
holomorphic function `f` at `z`. -/
def sphericalDeriv (f : ℂ → ℂ) (z : ℂ) : ℝ := ‖deriv f z‖ / (1 + ‖f z‖ ^ 2)

/-- The spherical derivative is nonnegative. -/
theorem sphericalDeriv_nonneg (f : ℂ → ℂ) (z : ℂ) : 0 ≤ sphericalDeriv f z :=
  div_nonneg (norm_nonneg _) (by positivity)

/-- **The spherical derivative is invariant under inversion.** Since `w ↦ 1/w` is an isometry of
the chordal metric, the spherical derivative of `1/f` agrees with that of `f` wherever `f` is
differentiable and nonzero. -/
theorem sphericalDeriv_inv (f : ℂ → ℂ) {z : ℂ} (hd : DifferentiableAt ℂ f z) (hz : f z ≠ 0) :
    sphericalDeriv (fun w ↦ (f w)⁻¹) z = sphericalDeriv f z := by
  have h1 : HasDerivAt f (deriv f z) z := hd.hasDerivAt
  have h2 : HasDerivAt (fun w ↦ (f w)⁻¹) (-deriv f z / (f z) ^ 2) z := h1.inv hz
  have hfz : (0:ℝ) < ‖f z‖ := norm_pos_iff.mpr hz
  unfold sphericalDeriv
  rw [h2.deriv, norm_div, norm_neg, norm_pow, norm_inv,
    show (1:ℝ) + (‖f z‖⁻¹) ^ 2 = (‖f z‖ ^ 2 + 1) / ‖f z‖ ^ 2 by field_simp]
  have hfz2 : (‖f z‖ ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end Complex
end
