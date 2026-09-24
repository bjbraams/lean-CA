/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Norm bounds and vanishing criteria for curve integrals

The operator norm of a one-form and the speed of a path control the norm of
its curve integral. These estimates apply to forms on real or complex normed
spaces and require no completeness hypothesis. A family of connecting paths
has vanishing integrals when the products of the form and speed bounds tend
to zero, even if the paths themselves become longer. Power decay faster than
the reciprocal radius suffices when the speed grows at most linearly in the radius.

## Main results

* `norm_curveIntegral_le_mul_integral_norm_derivWithin`: The norm of a curve integral is bounded
  by a bound on the form times the integral of the speed. Only integrability of the speed is
  needed for this norm estimate.
* `norm_curveIntegral_le_mul_of_derivWithin_le`: Bounds on the form and path speed give the
  usual product estimate for a curve integral.
* `tendsto_curveIntegral_zero_of_bounds`: Connecting-path integrals vanish if the products of
  form and speed bounds tend to zero.
* `norm_curveIntegral_le_rpow`: A power bound on the form and a linear bound on speed give an
  explicit decay rate for the curve integral.
* `tendsto_curveIntegral_zero_of_rpow_bounds`: Forms decaying faster than the reciprocal radius
  have vanishing integrals along families of paths whose speeds grow at most linearly with that
  radius.

## References

* `Mathlib.MeasureTheory.Integral.CurveIntegral.Basic`: formal background used by this module.
* `Mathlib.Analysis.Normed.Group.Continuity`: formal background used by this module.
* `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`: formal background used by this module.
-/

public section
open Set Filter MeasureTheory
open scoped Topology unitInterval

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {a b : E} {γ : Path a b} {ω : E → E →L[𝕜] F} {C L : ℝ}

/-- The norm of a curve integral is bounded by a bound on the form times the integral
of the speed. Only integrability of the speed is needed for this norm estimate. -/
theorem norm_curveIntegral_le_mul_integral_norm_derivWithin
    (hω : ∀ t, ‖ω (γ t)‖ ≤ C)
    (hγ : IntervalIntegrable (fun t => ‖derivWithin γ.extend I t‖) volume 0 1) :
    ‖curveIntegral ω γ‖ ≤ C * ∫ t in (0 : ℝ)..1, ‖derivWithin γ.extend I t‖ := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  rw [curveIntegral_def, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one _ (hγ.const_mul C)
  apply ae_of_all
  intro t ht
  have htI : t ∈ I := ⟨ht.1.le, ht.2⟩
  rw [curveIntegralFun_def, γ.extend_apply htI]
  exact (ω (γ ⟨t, htI⟩)).le_of_opNorm_le (hω ⟨t, htI⟩) _

/-- Bounds on the form and path speed give the usual product estimate for a curve integral. -/
theorem norm_curveIntegral_le_mul_of_derivWithin_le (hC : 0 ≤ C)
    (hω : ∀ t, ‖ω (γ t)‖ ≤ C) (hγ : ∀ t ∈ I, ‖derivWithin γ.extend I t‖ ≤ L) :
    ‖curveIntegral ω γ‖ ≤ C * L := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  rw [curveIntegral_def]
  simpa only [sub_zero, abs_one, mul_one] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := curveIntegralFun ω γ) (C := C * L) (fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        have htI : t ∈ I := ⟨ht.1.le, ht.2⟩
        rw [curveIntegralFun_def, γ.extend_apply htI]
        exact ((ω (γ ⟨t, htI⟩)).le_of_opNorm_le (hω ⟨t, htI⟩) _).trans
          (mul_le_mul_of_nonneg_left (hγ t htI) hC)))

/-- Connecting-path integrals vanish if the products of form and speed bounds tend to zero. -/
theorem tendsto_curveIntegral_zero_of_bounds
    {α : Type*} {ℱ : Filter α} {x y : α → E} {η : ∀ i, Path (x i) (y i)}
    {ω : α → E → E →L[𝕜] F} {C L : α → ℝ} (hC : ∀ i, 0 ≤ C i)
    (hω : ∀ i t, ‖ω i (η i t)‖ ≤ C i)
    (hη : ∀ i t, t ∈ I → ‖derivWithin (η i).extend I t‖ ≤ L i)
    (hlim : Tendsto (fun i => C i * L i) ℱ (𝓝 0)) :
    Tendsto (fun i => curveIntegral (ω i) (η i)) ℱ (𝓝 0) :=
  squeeze_zero_norm
    (fun i => norm_curveIntegral_le_mul_of_derivWithin_le (hC i) (hω i) (hη i)) hlim

/-- A power bound on the form and a linear bound on speed give an explicit decay rate
for the curve integral. -/
theorem norm_curveIntegral_le_rpow {R p K : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hω : ∀ t, ‖ω (γ t)‖ ≤ C * R ^ (-p))
    (hγ : ∀ t ∈ I, ‖derivWithin γ.extend I t‖ ≤ K * R) :
    ‖curveIntegral ω γ‖ ≤ (C * K) * R ^ (1 - p) := by
  convert norm_curveIntegral_le_mul_of_derivWithin_le
    (mul_nonneg hC (Real.rpow_nonneg hR.le _)) hω hγ using 1
  rw [show 1 - p = -p + 1 by ring, Real.rpow_add_one hR.ne']
  ring

/-- Forms decaying faster than the reciprocal radius have vanishing integrals along
families of paths whose speeds grow at most linearly with that radius. -/
theorem tendsto_curveIntegral_zero_of_rpow_bounds
    {α : Type*} {ℱ : Filter α} {x y : α → E} {η : ∀ i, Path (x i) (y i)}
    {ω : α → E → E →L[𝕜] F} {R : α → ℝ} {p K : ℝ} (hp : 1 < p) (hC : 0 ≤ C)
    (hR : ∀ i, 0 < R i) (hRlim : Tendsto R ℱ atTop)
    (hω : ∀ i t, ‖ω i (η i t)‖ ≤ C * (R i) ^ (-p))
    (hη : ∀ i t, t ∈ I → ‖derivWithin (η i).extend I t‖ ≤ K * R i) :
    Tendsto (fun i => curveIntegral (ω i) (η i)) ℱ (𝓝 0) := by
  apply squeeze_zero_norm (fun i => norm_curveIntegral_le_rpow (hR i) hC (hω i) (hη i))
  simpa only [neg_sub, mul_zero, Function.comp_apply] using
    ((tendsto_rpow_neg_atTop (sub_pos.mpr hp)).comp hRlim).const_mul (C * K)
