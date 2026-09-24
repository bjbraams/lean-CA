/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Möbius transformations: cross ratio and generalized circles

A **Möbius transformation** `mobiusMap a b c d z = (a z + b) / (c z + d)`, with `a d - b c ≠ 0`,
is a fractional linear transformation. The **cross ratio** of four points,
`crossRatio z₁ z₂ z₃ z₄ = (z₁ - z₃)(z₂ - z₄) / ((z₁ - z₄)(z₂ - z₃))`, is invariant under every
Möbius transformation, by direct algebra on the individual differences `M zᵢ - M zⱼ`.

A **generalized circle** (an ordinary circle, or, in the limit of infinite radius, a line) is
the zero set of `A |z|² + 2 Re(conj B z) + C` for real `A`, `C` and complex `B` (the case `A = 0`
gives a line; `A ≠ 0` with `‖B‖² > A C` gives a genuine circle). Every Möbius transformation
sends generalized circles to generalized circles: this is proved by decomposing an arbitrary
Möbius map into translations, scalings/rotations, and the inversion `z ↦ 1 / z`, each of which
is checked directly to preserve the defining quadratic equation.

Symmetric points with respect to a generalized circle are not treated here.

## Main definitions

* `Complex.mobiusMap a b c d z`: the Möbius transformation `(a z + b) / (c z + d)`.
* `Complex.crossRatio z₁ z₂ z₃ z₄`: the cross ratio of four points.
* `Complex.IsGenCircle A B C z`: `z` lies on the generalized circle with parameters `A, B, C`.

## Main results

* `Complex.crossRatio_mobiusMap`: **invariance of the cross ratio** under Möbius transformations.
* `Complex.isGenCircle_mobiusMap`: **Möbius transformations send generalized circles to
  generalized circles**.

## References

* B. Simon, *Basic Complex Analysis*, Section 7.3.
* R. Remmert, *Theory of Complex Functions*, Chapter 9, Section 1.
-/

public noncomputable section

open Set
open scoped ComplexConjugate

namespace Complex

/-! ### Möbius transformations and the cross ratio -/

/-- The Möbius transformation `z ↦ (a z + b) / (c z + d)`. -/
def mobiusMap (a b c d z : ℂ) : ℂ := (a * z + b) / (c * z + d)

/-- The cross ratio of four points. -/
def crossRatio (z₁ z₂ z₃ z₄ : ℂ) : ℂ := (z₁ - z₃) * (z₂ - z₄) / ((z₁ - z₄) * (z₂ - z₃))

/-- The difference of a Möbius transformation at two points. -/
theorem sub_mobiusMap {a b c d z w : ℂ} (hz : c * z + d ≠ 0) (hw : c * w + d ≠ 0) :
    mobiusMap a b c d z - mobiusMap a b c d w =
      (a * d - b * c) * (z - w) / ((c * z + d) * (c * w + d)) := by
  unfold mobiusMap
  rw [div_sub_div _ _ hz hw]
  congr 1
  ring

/-- **Invariance of the cross ratio** under Möbius transformations. -/
theorem crossRatio_mobiusMap {a b c d : ℂ} (had : a * d - b * c ≠ 0) {z₁ z₂ z₃ z₄ : ℂ}
    (h1 : c * z₁ + d ≠ 0) (h2 : c * z₂ + d ≠ 0) (h3 : c * z₃ + d ≠ 0) (h4 : c * z₄ + d ≠ 0)
    (h13 : z₁ ≠ z₃) (h14 : z₁ ≠ z₄) (h23 : z₂ ≠ z₃) (h24 : z₂ ≠ z₄) :
    crossRatio (mobiusMap a b c d z₁) (mobiusMap a b c d z₂) (mobiusMap a b c d z₃)
      (mobiusMap a b c d z₄) = crossRatio z₁ z₂ z₃ z₄ := by
  unfold crossRatio
  rw [sub_mobiusMap h1 h3, sub_mobiusMap h2 h4, sub_mobiusMap h1 h4, sub_mobiusMap h2 h3]
  have h13' : z₁ - z₃ ≠ 0 := sub_ne_zero.mpr h13
  have h14' : z₁ - z₄ ≠ 0 := sub_ne_zero.mpr h14
  have h23' : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h23
  have h24' : z₂ - z₄ ≠ 0 := sub_ne_zero.mpr h24
  field_simp


/-! ### Generalized circles -/

/-- `z` lies on the generalized circle (circle or line) with parameters `A, B, C`:
`A ‖z‖ ^ 2 + 2 Re (conj B * z) + C = 0`. `A = 0` gives a line; `A ≠ 0` with `‖B‖ ^ 2 > A * C`
gives a genuine circle. -/
def IsGenCircle (A : ℝ) (B : ℂ) (C : ℝ) (z : ℂ) : Prop :=
  A * normSq z + 2 * (conj B * z).re + C = 0

/-- Translation preserves generalized circles. -/
theorem isGenCircle_add_const (A : ℝ) (B : ℂ) (C : ℝ) (b : ℂ) {z : ℂ}
    (h : IsGenCircle A B C z) :
    IsGenCircle A (B - A * b) (C + A * normSq b - 2 * (conj B * b).re) (z + b) := by
  unfold IsGenCircle at h ⊢
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im] at h ⊢
  nlinarith [h]

/-- Scaling by a nonzero complex number preserves generalized circles. -/
theorem isGenCircle_const_mul (A : ℝ) (B : ℂ) (C : ℝ) {a z : ℂ} (ha : a ≠ 0)
    (h : IsGenCircle A B C z) :
    IsGenCircle (A / normSq a) (B / conj a) C (a * z) := by
  unfold IsGenCircle at h ⊢
  have hna : normSq a ≠ 0 := by simpa using ha
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.conj_re, Complex.conj_im] at h ⊢
  have hna' : a.re ^ 2 + a.im ^ 2 ≠ 0 := by
    intro hc; apply hna; simp only [Complex.normSq_apply]; nlinarith
  field_simp [hna']
  nlinarith [h]

/-- Inversion preserves generalized circles, swapping the roles of `A` and `C`. -/
theorem isGenCircle_inv {A : ℝ} {B : ℂ} {C : ℝ} {z : ℂ} (hz : z ≠ 0)
    (h : IsGenCircle A B C z) : IsGenCircle C (conj B) A (z⁻¹) := by
  unfold IsGenCircle at h ⊢
  have hz2 : normSq z ≠ 0 := by simpa using hz
  have hz2' : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
    intro hc; apply hz2; simp only [Complex.normSq_apply]; nlinarith
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.conj_re, Complex.conj_im] at h ⊢
  field_simp [hz2']
  nlinarith [h]

/-- A Möbius transformation with nonzero `c`, at a point away from its pole, decomposes as a
translation, an inversion, a scaling, and a further translation. -/
theorem mobiusMap_eq_of_ne_zero {a b c d z : ℂ} (hc : c ≠ 0) (hz : c * z + d ≠ 0) :
    mobiusMap a b c d z = a / c - (a * d - b * c) / c ^ 2 * (z + d / c)⁻¹ := by
  unfold mobiusMap
  have h1 : z + d / c ≠ 0 := by
    intro h0
    apply hz
    have h2 : c * (z + d / c) = 0 := by rw [h0]; ring
    rwa [mul_add, mul_div_cancel₀ d hc] at h2
  rw [inv_eq_one_div, eq_sub_iff_add_eq, div_mul_div_comm, mul_one, div_add_div _ _ hz
    (mul_ne_zero (pow_ne_zero 2 hc) h1), div_eq_div_iff (mul_ne_zero hz (mul_ne_zero
    (pow_ne_zero 2 hc) h1)) hc]
  field_simp
  ring


/-- **Möbius transformations send generalized circles to generalized circles.** -/
theorem isGenCircle_mobiusMap {a b c d : ℂ} (had : a * d - b * c ≠ 0) {A : ℝ} {B : ℂ} {C : ℝ}
    {z : ℂ} (hz : c * z + d ≠ 0) (h : IsGenCircle A B C z) :
    ∃ (A' : ℝ) (B' : ℂ) (C' : ℝ), IsGenCircle A' B' C' (mobiusMap a b c d z) := by
  rcases eq_or_ne c 0 with hc | hc
  · -- the affine case: `mobiusMap a b 0 d z = (a / d) * z + (b / d)`
    have hd : d ≠ 0 := by rintro rfl; simp [hc] at had
    have heq : mobiusMap a b c d z = (a / d) * z + (b / d) := by
      unfold mobiusMap
      rw [hc, zero_mul, zero_add]
      field_simp
    rw [heq]
    have had0 : a / d ≠ 0 := by
      have ha0 : a ≠ 0 := by rintro rfl; simp [hc] at had
      exact div_ne_zero ha0 hd
    exact ⟨_, _, _, isGenCircle_add_const _ (B / conj (a / d)) C (b / d)
      (isGenCircle_const_mul A B C had0 h)⟩
  · -- the genuine Möbius case: translate, invert, scale, translate
    rw [mobiusMap_eq_of_ne_zero hc hz]
    have h1 : z + d / c ≠ 0 := by
      intro h0
      apply hz
      have h2 : c * (z + d / c) = 0 := by rw [h0]; ring
      rwa [mul_add, mul_div_cancel₀ d hc] at h2
    have step1 := isGenCircle_add_const A B C (d / c) h
    have step2 := isGenCircle_inv h1 step1
    have hne0 : -(a * d - b * c) / c ^ 2 ≠ 0 := by
      simp only [ne_eq, div_eq_zero_iff, neg_eq_zero]
      push Not
      exact ⟨had, pow_ne_zero 2 hc⟩
    have step3 := isGenCircle_const_mul _ _ _ hne0 step2
    have step4 := isGenCircle_add_const _ _ _ (a / c) step3
    have hpt : -(a * d - b * c) / c ^ 2 * (z + d / c)⁻¹ + a / c =
        a / c - (a * d - b * c) / c ^ 2 * (z + d / c)⁻¹ := by ring
    rw [hpt] at step4
    exact ⟨_, _, _, step4⟩


/-! ### Symmetric points -/

/-- `star` is symmetric to `z` with respect to the generalized circle through the three
distinct points `z₁, z₂, z₃`: the cross ratio of `star, z₁, z₂, z₃` is the complex conjugate of
the cross ratio of `z, z₁, z₂, z₃`. For a genuine circle this recovers the classical notion of
inverse points; the connection to that geometric description is not proved here. -/
def IsSymmetricWrt (z star z₁ z₂ z₃ : ℂ) : Prop :=
  crossRatio star z₁ z₂ z₃ = conj (crossRatio z z₁ z₂ z₃)

/-- **Möbius transformations preserve the symmetric-point relation.** -/
theorem isSymmetricWrt_mobiusMap {a b c d : ℂ} (had : a * d - b * c ≠ 0) {z star z₁ z₂ z₃ : ℂ}
    (hcs : c * star + d ≠ 0) (hc1 : c * z₁ + d ≠ 0) (hc2 : c * z₂ + d ≠ 0)
    (hc3 : c * z₃ + d ≠ 0) (hcz : c * z + d ≠ 0) (hs2 : star ≠ z₂) (hs3 : star ≠ z₃)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (hz2 : z ≠ z₂) (hz3 : z ≠ z₃)
    (h : IsSymmetricWrt z star z₁ z₂ z₃) :
    IsSymmetricWrt (mobiusMap a b c d z) (mobiusMap a b c d star) (mobiusMap a b c d z₁)
      (mobiusMap a b c d z₂) (mobiusMap a b c d z₃) := by
  unfold IsSymmetricWrt at h ⊢
  rw [crossRatio_mobiusMap had hcs hc1 hc2 hc3 hs2 hs3 h12 h13,
    crossRatio_mobiusMap had hcz hc1 hc2 hc3 hz2 hz3 h12 h13, h]

end Complex

end
