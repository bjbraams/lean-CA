/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Analysis.Contour.Winding.EndpointRatio
public import TauCeti.Analysis.Contour.Winding.Number.Homotopy

/-!
# Integrals of logarithmic derivatives along curves

Exponentiating the integral of the logarithmic derivative of a nonvanishing complex-valued
function on a real interval gives the ratio of its endpoint values. For a closed curve this
implies that its Cauchy-kernel integral is an integer multiple of `2 * π * I`.
The interval theorem uses an explicitly supplied derivative, and needs no choice of a
logarithm branch along the curve.

The curve-integral results allow piecewise `C¹` paths. They identify the Cauchy-kernel integral
with `2πi` times the winding number of the Tau Ceti contributors'
`TauCeti.Analysis.Contour.Winding`, and import its endpoint-ratio identity
(`TauCeti.Analysis.Contour.Winding.EndpointRatio`).

## Main results

* `Complex.exp_integral_div_of_hasDerivAt`: Exponentiating a logarithmic-derivative integral
  gives the ratio of endpoint values. Continuity of the derivative is required only on the
  closed interval.
* `Complex.curveIntegral_sub_inv_eq_two_pi_I_mul_windingNumber`: the Cauchy-kernel curve
  integral is `2πi` times the Tau Ceti winding number.
* `Complex.exp_curveIntegral_sub_inv`: The exponential of a Cauchy-kernel integral along a
  piecewise `C¹` path avoiding the pole is the ratio of the displaced endpoint values.
* `Complex.exists_int_curveIntegral_sub_inv`: A closed piecewise `C¹` curve avoiding a point has
  Cauchy-kernel integral equal to an integer multiple of `2πi`. No simplicity assumption is
  needed.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

open Set MeasureTheory Filter
open scoped Topology unitInterval

public noncomputable section
namespace Complex

/-- Exponentiating a logarithmic-derivative integral gives the ratio of endpoint values.
Continuity of the derivative is required only on the closed interval. -/
theorem exp_integral_div_of_hasDerivAt {g g' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t)
    (h0 : ∀ t ∈ Icc a b, g t ≠ 0) :
    exp (∫ t in a..b, g' t / g t) = g b / g a := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp [h0 a ⟨le_rfl, le_rfl⟩]
  let v : ℝ → ℂ := fun t ↦ g' t / g t
  have hv : ContinuousOn v (Icc a b) := hg'.div hg h0
  have hi : IntervalIntegrable v volume a b := hv.intervalIntegrable_of_Icc hab
  let J : ℝ → ℂ := fun t ↦ ∫ s in a..t, v s
  have hJ : ContinuousOn J (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc)
  have hdJ (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt J (v t) t := by
    have hit : IntervalIntegrable v volume a t :=
      (hv.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
    apply intervalIntegral.integral_hasDerivAt_right hit
    · exact (hv.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
    · exact hv.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have haux : ∀ t ∈ Ioo a b, HasDerivAt (fun s ↦ exp (-J s) * g s) 0 t := by
    intro t ht
    have h := ((hdJ t ht).neg.cexp).mul (hd t ht)
    convert h using 1
    dsimp [v]
    field_simp [h0 t (Ioo_subset_Icc_self ht)]
    all_goals ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hJ.neg.cexp.mul hg) haux
    (intervalIntegrable_const : IntervalIntegrable (fun _ ↦ (0 : ℂ)) volume a b)
  have he' : exp (-J b) * g b = g a := by
    apply sub_eq_zero.mp
    simpa only [Pi.mul_apply, Pi.neg_apply, J, intervalIntegral.integral_same, neg_zero,
      exp_zero, one_mul, intervalIntegral.integral_zero] using he.symm
  apply (eq_div_iff (h0 a (left_mem_Icc.mpr hab))).mpr
  change exp (J b) * g a = g b
  rw [← he', ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/-- The extension of a `C¹` path is piecewise `C¹` on `[0, 1]` in the sense of the Tau Ceti
contour library. -/
theorem isPiecewiseC1On_extend_of_contDiffOn {a b : ℂ} {γ : Path a b}
    (hγ : ContDiffOn ℝ 1 γ.extend I) : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1 :=
  .of_contDiffOn (by rwa [uIcc_of_le zero_le_one])

/-- The Cauchy-kernel curve integral along a piecewise `C¹` path avoiding `w` is `2πi` times the
winding number `TauCeti.Contour.windingNumber` of the Tau Ceti contributors.

This is `TauCeti.Contour.windingNumber_eq_two_pi_I_inv_mul_curveIntegral`, rewritten for the
kernel `ContinuousLinearMap.toSpanSingleton ℂ (z - w)⁻¹`. -/
theorem curveIntegral_sub_inv_eq_two_pi_I_mul_windingNumber {a b w : ℂ} {γ : Path a b}
    (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) (hw : ∀ t, γ t ≠ w) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ =
      (2 * (Real.pi : ℂ) * Complex.I) * TauCeti.Contour.windingNumber γ.extend 0 1 w := by
  rw [TauCeti.Contour.windingNumber_eq_two_pi_I_inv_mul_curveIntegral hγ hw, ← mul_assoc,
    mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]
  congr 1
  funext z
  ext
  simp

/-- The exponential of a Cauchy-kernel integral along a piecewise `C¹` path avoiding `w` is the
ratio of the displaced endpoint values.

This adapts `TauCeti.Contour.IsPiecewiseC1On.exp_two_pi_I_mul_windingNumber` by the Tau Ceti
contributors. -/
theorem exp_curveIntegral_sub_inv {a b w : ℂ} (γ : Path a b)
    (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) (hw : ∀ t, γ t ≠ w) :
    exp (curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ) =
      (b - w) / (a - w) := by
  have havoid : ∀ t ∈ uIcc (0 : ℝ) 1, γ.extend t ≠ w := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    rw [γ.extend_apply ht]
    exact hw ⟨t, ht⟩
  rw [curveIntegral_sub_inv_eq_two_pi_I_mul_windingNumber hγ hw,
    hγ.exp_two_pi_I_mul_windingNumber havoid, γ.extend_one, γ.extend_zero]

/-- A closed piecewise `C¹` curve avoiding a point has Cauchy-kernel integral equal to an
integer multiple of `2πi`. No simplicity assumption is needed. -/
theorem exists_int_curveIntegral_sub_inv {a w : ℂ} (γ : Path a a)
    (hγ : TauCeti.Contour.IsPiecewiseC1On γ.extend 0 1) (hw : ∀ t, γ t ≠ w) :
    ∃ n : ℤ, curveIntegral
      (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ =
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  apply exp_eq_one_iff.mp
  rw [exp_curveIntegral_sub_inv γ hγ hw, div_self]
  exact sub_ne_zero.mpr (by simpa using hw 0)

end Complex
