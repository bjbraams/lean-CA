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
gives a line when `B ≠ 0`; `A ≠ 0` with `‖B‖² > A C` gives a genuine circle). The parameters are
nondegenerate when `A C < ‖B‖²`. Every Möbius transformation sends generalized circles to
generalized circles: writing the equation as the Hermitian form of `H = [[A, B], [conj B, C]]`
on `(z, 1)`, the image circle has matrix `Nᴴ H N`, where `N = [[d, -b], [-c, a]]` is the adjugate
of the matrix of the transformation. This gives explicit image parameters, independent of the
point, and the discriminant is multiplied by `‖a d - b c‖²`, so nondegeneracy is preserved.
Translations, scalings/rotations, and the inversion `z ↦ 1 / z` are also treated separately.

Two points are symmetric with respect to the generalized circle through three given points when
their cross ratios with those points are complex conjugates; Möbius transformations preserve
this relation.

## Main definitions

* `Complex.mobiusMap a b c d z`: the Möbius transformation `(a z + b) / (c z + d)`.
* `Complex.crossRatio z₁ z₂ z₃ z₄`: the cross ratio of four points.
* `Complex.IsGenCircle A B C z`: `z` lies on the generalized circle with parameters `A, B, C`.
* `Complex.IsSymmetricWrt z star z₁ z₂ z₃`: `z` and `star` are symmetric with respect to the
  generalized circle through `z₁, z₂, z₃`.

## Main results

* `Complex.crossRatio_mobiusMap`: **invariance of the cross ratio** under Möbius transformations.
* `Complex.isGenCircle_mobiusMap_iff`: explicit parameters of the image of a generalized circle.
* `Complex.exists_isGenCircle_mobiusMap`: **Möbius transformations send nondegenerate generalized
  circles to nondegenerate generalized circles**.
* `Complex.isSymmetricWrt_mobiusMap`: Möbius transformations preserve symmetric points.

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
`A ‖z‖ ^ 2 + 2 Re (conj B * z) + C = 0`. The parameters are nondegenerate when
`A * C < normSq B`; then `A = 0` (forcing `B ≠ 0`) gives a line and `A ≠ 0` gives a circle of
positive radius. No nondegeneracy is imposed by this predicate; for instance `A = B = C = 0`
gives all of `ℂ`. -/
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


/-- **Explicit image of a generalized circle under a Möbius transformation.** Away from the
pole, `z` lies on the generalized circle with parameters `A, B, C` if and only if
`mobiusMap a b c d z` lies on the generalized circle whose parameters are the entries of the
Hermitian matrix `Nᴴ H N`, where `H = [[A, B], [conj B, C]]` and `N = [[d, -b], [-c, a]]` is the
adjugate of the matrix of the transformation. The underlying identity multiplies the defining
expression of the image circle at `mobiusMap a b c d z` by `normSq (c * z + d)` to obtain
`normSq (a * d - b * c)` times the defining expression of the original circle at `z`. -/
theorem isGenCircle_mobiusMap_iff {a b c d : ℂ} (had : a * d - b * c ≠ 0) {A : ℝ} {B : ℂ}
    {C : ℝ} {z : ℂ} (hz : c * z + d ≠ 0) :
    IsGenCircle (A * normSq d - 2 * (B * conj d * c).re + C * normSq c)
        (B * a * conj d - A * b * conj d + conj B * b * conj c - C * a * conj c)
        (A * normSq b - 2 * (B * a * conj b).re + C * normSq a) (mobiusMap a b c d z) ↔
      IsGenCircle A B C z := by
  have key : ((A * normSq d - 2 * (B * conj d * c).re + C * normSq c) *
        normSq (mobiusMap a b c d z) +
      2 * (conj (B * a * conj d - A * b * conj d + conj B * b * conj c - C * a * conj c) *
        mobiusMap a b c d z).re +
      (A * normSq b - 2 * (B * a * conj b).re + C * normSq a)) * normSq (c * z + d) =
      normSq (a * d - b * c) * (A * normSq z + 2 * (conj B * z).re + C) := by
    apply ofReal_injective
    have hz' : conj c * conj z + conj d ≠ 0 := by
      rw [← map_mul, ← map_add]; exact (map_ne_zero _).mpr hz
    push_cast
    simp only [re_eq_add_conj, ← mul_conj]
    simp only [mobiusMap, map_mul, map_sub, map_add, map_div₀, conj_conj, conj_ofReal]
    field_simp
    ring
  have hq : normSq (c * z + d) ≠ 0 := normSq_eq_zero.not.mpr hz
  have hΔ : normSq (a * d - b * c) ≠ 0 := normSq_eq_zero.not.mpr had
  unfold IsGenCircle
  constructor
  · intro h
    rw [h, zero_mul] at key
    exact (mul_eq_zero.mp key.symm).resolve_left hΔ
  · intro h
    rw [h, mul_zero] at key
    exact (mul_eq_zero.mp key).resolve_right hq

/-- **Möbius transformations send generalized circles to generalized circles.** For a
nondegenerate generalized circle (`A * C < normSq B`) and a Möbius transformation, there is a
single nondegenerate generalized circle such that every point `z` away from the pole lies on the
original circle if and only if `mobiusMap a b c d z` lies on the new one. -/
theorem exists_isGenCircle_mobiusMap {a b c d : ℂ} (had : a * d - b * c ≠ 0) {A : ℝ} {B : ℂ}
    {C : ℝ} (hABC : A * C < normSq B) :
    ∃ (A' : ℝ) (B' : ℂ) (C' : ℝ), A' * C' < normSq B' ∧
      ∀ z, c * z + d ≠ 0 → (IsGenCircle A' B' C' (mobiusMap a b c d z) ↔ IsGenCircle A B C z) := by
  refine ⟨_, _, _, ?_, fun z hz ↦ isGenCircle_mobiusMap_iff had hz⟩
  have hdisc : (A * normSq d - 2 * (B * conj d * c).re + C * normSq c) *
      (A * normSq b - 2 * (B * a * conj b).re + C * normSq a) -
      normSq (B * a * conj d - A * b * conj d + conj B * b * conj c - C * a * conj c) =
      normSq (a * d - b * c) * (A * C - normSq B) := by
    apply ofReal_injective
    push_cast
    simp only [re_eq_add_conj, ← mul_conj, map_mul, map_sub, map_add, conj_conj, conj_ofReal]
    ring
  have hΔ : 0 < normSq (a * d - b * c) := normSq_pos.mpr had
  have : normSq (a * d - b * c) * (A * C - normSq B) < 0 :=
    mul_neg_of_pos_of_neg hΔ (sub_neg.mpr hABC)
  linarith


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
