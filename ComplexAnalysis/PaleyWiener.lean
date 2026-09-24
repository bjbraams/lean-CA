/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Paley–Wiener theorem: holomorphic extension of a compactly supported transform

The full Paley–Wiener theorem identifies the entire functions of exponential type with
square-integrable restriction to `ℝ` exactly with the Fourier-type transforms of functions
supported on a bounded interval. This file proves the classical *holomorphic extension* half of
that identification (Stein–Shakarchi's preliminary step, SS 4.1): if `f : ℝ → ℂ` is integrable
on `[-τ, τ]`, the transform
`paleyWienerTransform f τ z = ∫ t in -τ..τ, f t * exp (I z t)`,
which restricts on `ℝ` to the (unnormalized, `e^{izt}`-kernel) Fourier-type transform of `f`
extended by zero outside `[-τ, τ]`, extends holomorphically to an entire function of exponential
type at most `τ`.

Entire-ness is obtained by differentiating under the integral sign in the complex parameter `z`
(Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, instantiated with the parameter
space `H = ℂ`, so that the resulting `HasDerivAt` is genuine complex differentiability), with a
locally uniform bound on the derivative of the kernel `exp (I z t)` coming from `t` ranging over
the fixed compact interval `[-τ, τ]`. The exponential type bound is the elementary estimate
`‖exp (I z t)‖ = exp (-t * z.im) ≤ exp (τ * ‖z‖)` for `t ∈ [-τ, τ]`.

**Not proved here** (see `COVERAGE.md`, item D): that `paleyWienerTransform f τ` restricted to
`ℝ` lies in `L²(ℝ)` when `f` does — this is Plancherel's theorem for this transform, and bridging
it to Mathlib's abstract `L²` Fourier isometry (`MeasureTheory.Lp.fourierTransformₗᵢ`, built by
continuous extension from Schwartz functions, with a `2π`-normalized kernel) would need a
currently-missing lemma identifying that isometry with the concrete integral on `L¹ ∩ L²`
functions. Also not proved: the converse ("hard") direction, that every entire function of
exponential type `τ` with `L²` restriction to `ℝ` arises this way — the classical proof needs a
mean-square bound on `∫ ‖F (x + iy)‖² dx` uniform in `y`, obtained from the sub-mean-value
property of the subharmonic function `‖F‖²` (mean value over a disc) together with the growth
bound, which is a substantial argument beyond the scope of this file.

## Main definitions

* `Complex.paleyWienerTransform f τ z`.

## Main results

* `Complex.hasDerivAt_paleyWienerTransform`, `Complex.differentiable_paleyWienerTransform`:
  `paleyWienerTransform f τ` is entire.
* `Complex.norm_paleyWienerTransform_le`: the exponential type bound.

## References

* E. M. Stein and R. Shakarchi, *Complex Analysis*, Chapter 4, Section 1.
* E. C. Titchmarsh, *The Theory of Functions*, Section 5.3 (Paley–Wiener).
-/

public noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology

namespace Complex

/-- **The Paley–Wiener transform.** The Fourier-type integral of `f` (with kernel `exp (I z t)`,
the unnormalized convention) over `[-τ, τ]`, evaluated at a complex point `z`: on `ℝ` this is the
Fourier-type transform of `f` extended by zero outside `[-τ, τ]`, and off `ℝ` it is the
holomorphic extension studied by the Paley–Wiener theorem. -/
def paleyWienerTransform (f : ℝ → ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (-τ : ℝ)..τ, f t * Complex.exp (Complex.I * z * t)

variable {f : ℝ → ℂ} {τ : ℝ}

/-- The kernel `exp (I z t)` is bounded by `exp (τ * (‖z₀‖ + 1))` uniformly for `z` within `1` of
`z₀` and `t ∈ [-τ, τ]`. -/
private theorem norm_exp_I_mul_mul_le {τ : ℝ} (z₀ : ℂ) {z : ℂ} (hz : z ∈ ball z₀ 1) {t : ℝ}
    (htτ : t ∈ Set.Ioc (-τ) τ) :
    ‖Complex.exp (Complex.I * z * (t : ℂ))‖ ≤ Real.exp (τ * (‖z₀‖ + 1)) := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * z * (t : ℂ)).re = -(t * z.im) := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  rw [hre]
  have hz1 : ‖z‖ ≤ ‖z₀‖ + 1 := by
    have hd : ‖z - z₀‖ < 1 := mem_ball_iff_norm.mp hz
    calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by congr 1; abel
      _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + 1 := by linarith
  have ht' : |t| ≤ τ := abs_le.mpr ⟨htτ.1.le, htτ.2⟩
  have hzim : |z.im| ≤ ‖z₀‖ + 1 := (Complex.abs_im_le_norm z).trans hz1
  apply Real.exp_le_exp.mpr
  calc -(t * z.im) ≤ |t * z.im| := neg_le_abs _
    _ = |t| * |z.im| := abs_mul t z.im
    _ ≤ τ * (‖z₀‖ + 1) := mul_le_mul ht' hzim (abs_nonneg _) (by linarith [htτ.1, htτ.2])

/-- Differentiation under the integral sign: `paleyWienerTransform f τ` has complex derivative
`∫ t in -τ..τ, f t * (I t) * exp (I z t)` at every point. -/
theorem hasDerivAt_paleyWienerTransform (hτ : 0 ≤ τ)
    (hf : IntervalIntegrable f volume (-τ) τ) (z₀ : ℂ) :
    HasDerivAt (paleyWienerTransform f τ)
      (∫ t in (-τ : ℝ)..τ, f t * (Complex.I * t) * Complex.exp (Complex.I * z₀ * t)) z₀ := by
  have hτ' : -τ ≤ τ := by linarith
  set μ : Measure ℝ := volume.restrict (Set.Ioc (-τ) τ) with hμ_def
  set F : ℂ → ℝ → ℂ := fun z t => f t * Complex.exp (Complex.I * z * t) with hF_def
  set F' : ℂ → ℝ → ℂ := fun z t => f t * (Complex.I * t) * Complex.exp (Complex.I * z * t)
    with hF'_def
  have hint_eq : ∀ g : ℝ → ℂ, (∫ t in (-τ : ℝ)..τ, g t) = ∫ t, g t ∂μ := by
    intro g
    rw [hμ_def, intervalIntegral.integral_of_le hτ']
  have hFeq : paleyWienerTransform f τ = fun z => ∫ t, F z t ∂μ := by
    funext z; exact hint_eq (F z)
  rw [hFeq, hint_eq (F' z₀)]
  have hfInt : Integrable f μ := by
    rw [hμ_def]; exact hf.def'.mono_set (by rw [uIoc_of_le hτ'])
  have hae_mem : ∀ᵐ t ∂μ, t ∈ Set.Ioc (-τ) τ := ae_restrict_mem measurableSet_Ioc
  have hcont : ∀ z : ℂ, Continuous (fun t : ℝ => Complex.exp (Complex.I * z * t)) := fun z => by
    fun_prop
  have hcont' : Continuous (fun t : ℝ => Complex.I * (t : ℂ)) := by fun_prop
  set C : ℝ := Real.exp (τ * (‖z₀‖ + 1)) with hC_def
  have hFint : Integrable (F z₀) μ :=
    hfInt.mul_bdd (hcont z₀).aestronglyMeasurable
      (hae_mem.mono fun t ht => norm_exp_I_mul_mul_le z₀ (mem_ball_self one_pos) ht)
  have hF'meas : AEStronglyMeasurable (F' z₀) μ :=
    (hfInt.1.mul hcont'.aestronglyMeasurable).mul (hcont z₀).aestronglyMeasurable
  have hderiv : ∀ t : ℝ, ∀ z : ℂ,
      HasDerivAt (fun w : ℂ => f t * Complex.exp (Complex.I * w * t)) (F' z t) z := by
    intro t z
    have h1 : HasDerivAt (fun w : ℂ => Complex.I * w * (t : ℂ)) (Complex.I * t) z := by
      simpa using ((hasDerivAt_id z).const_mul Complex.I).mul_const (t : ℂ)
    have h2 := (Complex.hasDerivAt_exp (Complex.I * z * t)).comp z h1
    have h3 := h2.const_mul (f t)
    have h3' : HasDerivAt (fun w : ℂ => f t * Complex.exp (Complex.I * w * t))
        (f t * (Complex.exp (Complex.I * z * t) * (Complex.I * t))) z := h3
    rw [hF'_def]
    dsimp only
    have heq : f t * (Complex.I * t) * Complex.exp (Complex.I * z * t) =
        f t * (Complex.exp (Complex.I * z * t) * (Complex.I * t)) := by ring
    rw [heq]
    exact h3'
  have hbound : ∀ᵐ t ∂μ, ∀ z ∈ ball z₀ 1, ‖F' z t‖ ≤ ‖f t‖ * τ * C := by
    filter_upwards [hae_mem] with t ht z hz
    rw [hF'_def]
    dsimp only
    calc ‖f t * (Complex.I * t) * Complex.exp (Complex.I * z * t)‖
        = ‖f t‖ * ‖(Complex.I * (t : ℂ))‖ * ‖Complex.exp (Complex.I * z * t)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖f t‖ * τ * C := by
          have h1 : ‖(Complex.I * (t : ℂ))‖ = |t| := by
            rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
          rw [h1]
          have ht' : |t| ≤ τ := abs_le.mpr ⟨ht.1.le, ht.2⟩
          gcongr
          exact norm_exp_I_mul_mul_le z₀ hz ht
  have hbound_int : Integrable (fun t => ‖f t‖ * τ * C) μ := (hfInt.norm.mul_const τ).mul_const C
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (bound := fun t => ‖f t‖ * τ * C)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => hfInt.1.mul (hcont z).aestronglyMeasurable)
    hFint (F' := F') hF'meas hbound hbound_int
    (Eventually.of_forall fun t z _ => hderiv t z)).2

/-- **`paleyWienerTransform f τ` is entire.** -/
theorem differentiable_paleyWienerTransform (hτ : 0 ≤ τ)
    (hf : IntervalIntegrable f volume (-τ) τ) :
    Differentiable ℂ (paleyWienerTransform f τ) :=
  fun z => (hasDerivAt_paleyWienerTransform hτ hf z).differentiableAt

/-- **The exponential type bound.** `paleyWienerTransform f τ` has exponential type at most `τ`,
with the natural constant `∫ ‖f‖`. -/
theorem norm_paleyWienerTransform_le (hτ : 0 ≤ τ)
    (hf : IntervalIntegrable f volume (-τ) τ) (z : ℂ) :
    ‖paleyWienerTransform f τ z‖ ≤ (∫ t in (-τ : ℝ)..τ, ‖f t‖) * Real.exp (τ * ‖z‖) := by
  have hτ' : -τ ≤ τ := by linarith
  rw [paleyWienerTransform]
  have hg : IntervalIntegrable (fun t => ‖f t‖ * Real.exp (τ * ‖z‖)) volume (-τ) τ :=
    (hf.norm).mul_const _
  refine (intervalIntegral.norm_integral_le_of_norm_le hτ'
    (Eventually.of_forall fun t ht => ?_) hg).trans_eq ?_
  · rw [norm_mul]
    have h1 : ‖Complex.exp (Complex.I * z * (t : ℂ))‖ ≤ Real.exp (τ * ‖z‖) := by
      rw [Complex.norm_exp]
      have hre : (Complex.I * z * (t : ℂ)).re = -(t * z.im) := by
        simp [Complex.mul_re, Complex.mul_im]; ring
      rw [hre]
      apply Real.exp_le_exp.mpr
      have ht' : |t| ≤ τ := abs_le.mpr ⟨ht.1.le, ht.2⟩
      have hzim : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      calc -(t * z.im) ≤ |t * z.im| := neg_le_abs _
        _ = |t| * |z.im| := abs_mul t z.im
        _ ≤ τ * ‖z‖ := mul_le_mul ht' hzim (abs_nonneg _) hτ
    gcongr
  · exact intervalIntegral.integral_mul_const _ _

/-- `HasExponentialTypeLE f τ`: `f` has exponential type at most `τ`, i.e. `‖f z‖ ≤ A * exp (τ *
‖z‖)` for some constant `A ≥ 0`. Sharper than `Complex.HasOrderLE f 1` (`FiniteOrder.lean`) in
that it names the exact constant `τ` rather than merely asserting order at most `1`. -/
def HasExponentialTypeLE (f : ℂ → ℂ) (τ : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ z, ‖f z‖ ≤ A * Real.exp (τ * ‖z‖)

/-- **`paleyWienerTransform f τ` has exponential type at most `τ`.** -/
theorem hasExponentialTypeLE_paleyWienerTransform (hτ : 0 ≤ τ)
    (hf : IntervalIntegrable f volume (-τ) τ) :
    HasExponentialTypeLE (paleyWienerTransform f τ) τ :=
  ⟨∫ t in (-τ : ℝ)..τ, ‖f t‖,
    intervalIntegral.integral_nonneg (by linarith) fun t _ => norm_nonneg _,
    norm_paleyWienerTransform_le hτ hf⟩

end Complex
end
