/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Hadamard's three-circle theorem

Let `f` be holomorphic on the open annulus `r₁ < ‖z‖ < r₂` and continuous on the closed annulus
`r₁ ≤ ‖z‖ ≤ r₂`, with values in a complex normed space. If `‖f‖ ≤ M₁` on the circle `‖z‖ = r₁`
and `‖f‖ ≤ M₂` on the circle `‖z‖ = r₂`, then `‖f z‖ ≤ M₁ ^ t * M₂ ^ (1 - t)` on the circle
`‖z‖ = r`, where `t = (log r₂ - log r) / (log r₂ - log r₁)`; i.e. `log M(r)` is a convex
function of `log r`. No nonvanishing hypothesis is needed.

The proof transports Mathlib's **Hadamard three-lines theorem**
(`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`) along the exponential
map, which sends the vertical strip `log r₁ ≤ re w ≤ log r₂` onto the closed annulus.

## Main results

* `Complex.norm_le_rpow_mul_rpow_of_mem_sphere`: **Hadamard's three-circle theorem**.

## References

* B. Simon, *Basic Complex Analysis*, Section 5.2.
* R. Remmert, *Theory of Complex Functions*, Chapter 9, Section 3.4.
-/

public noncomputable section

open Set Metric

namespace Complex

open HadamardThreeLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The exponential maps the vertical strip `a ≤ re w ≤ b` into the closed annulus
`exp a ≤ ‖z‖ ≤ exp b`. -/
theorem mapsTo_exp_verticalClosedStrip (a b : ℝ) :
    MapsTo exp (verticalClosedStrip a b) (closedBall 0 (Real.exp b) \ ball 0 (Real.exp a)) :=
  fun w hw ↦ ⟨by simpa [norm_exp] using hw.2, by simpa [norm_exp] using hw.1⟩

/-- The exponential maps the open vertical strip `a < re w < b` into the open annulus
`exp a < ‖z‖ < exp b`. -/
theorem mapsTo_exp_verticalStrip (a b : ℝ) :
    MapsTo exp (verticalStrip a b) (ball 0 (Real.exp b) \ closedBall 0 (Real.exp a)) :=
  fun w hw ↦ ⟨by simpa [norm_exp] using hw.2, by simpa [norm_exp] using hw.1⟩

/-- **Hadamard's three-circle theorem.** For `f` holomorphic on the open annulus
`r₁ < ‖z‖ < r₂` and continuous on the closed annulus, bounded by `M₁` on `‖z‖ = r₁` and by `M₂`
on `‖z‖ = r₂`, the bound on `‖z‖ = r` is the weighted geometric mean
`M₁ ^ ((log r₂ - log r) / (log r₂ - log r₁)) * M₂ ^ ((log r - log r₁) / (log r₂ - log r₁))`. -/
theorem norm_le_rpow_mul_rpow_of_mem_sphere {f : ℂ → E} {r₁ r₂ r : ℝ} (hr₁ : 0 < r₁)
    (hr₁₂ : r₁ < r₂) (hf : DifferentiableOn ℂ f (ball 0 r₂ \ closedBall 0 r₁))
    (hfc : ContinuousOn f (closedBall 0 r₂ \ ball 0 r₁)) (hrr₁ : r₁ ≤ r) (hrr₂ : r ≤ r₂)
    {M₁ M₂ : ℝ} (hM₁ : ∀ z ∈ sphere (0 : ℂ) r₁, ‖f z‖ ≤ M₁)
    (hM₂ : ∀ z ∈ sphere (0 : ℂ) r₂, ‖f z‖ ≤ M₂) {z : ℂ} (hz : z ∈ sphere (0 : ℂ) r) :
    ‖f z‖ ≤ M₁ ^ ((Real.log r₂ - Real.log r) / (Real.log r₂ - Real.log r₁)) *
      M₂ ^ ((Real.log r - Real.log r₁) / (Real.log r₂ - Real.log r₁)) := by
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have hr : 0 < r := hr₁.trans_le hrr₁
  set l := Real.log r₁
  set u := Real.log r₂
  have hlu : l < u := Real.log_lt_log hr₁ hr₁₂
  have hel : Real.exp l = r₁ := Real.exp_log hr₁
  have heu : Real.exp u = r₂ := Real.exp_log hr₂
  have hcl : ContinuousOn (fun w ↦ f (exp w)) (verticalClosedStrip l u) :=
    hfc.comp continuous_exp.continuousOn
      (by simpa [hel, heu] using mapsTo_exp_verticalClosedStrip l u)
  have hd : DiffContOnCl ℂ (fun w ↦ f (exp w)) (verticalStrip l u) := by
    refine ⟨hf.comp differentiable_exp.differentiableOn
      (by simpa [hel, heu] using mapsTo_exp_verticalStrip l u), ?_⟩
    rwa [verticalStrip, closure_preimage_re, closure_Ioo hlu.ne]
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall (0 : ℂ) r₂).diff isOpen_ball).exists_bound_of_continuousOn hfc
  have hB : BddAbove ((norm ∘ fun w ↦ f (exp w)) '' verticalClosedStrip l u) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hC _ (by simpa [hel, heu] using mapsTo_exp_verticalClosedStrip l u hw)
  have hz0 : z ≠ 0 := ne_zero_of_mem_sphere hr.ne' ⟨z, hz⟩
  have hzr : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
  have hlog : (log z).re = Real.log r := by rw [log_re, hzr]
  have key := norm_le_interp_of_mem_verticalClosedStrip' (a := M₁) (b := M₂) hlu
    (z := log z) (by simpa [verticalClosedStrip, hlog] using
      ⟨Real.log_le_log hr₁ hrr₁, Real.log_le_log hr hrr₂⟩) hd hB
    (fun w hw ↦ hM₁ _ (by simp_all [norm_exp]))
    (fun w hw ↦ hM₂ _ (by simp_all [norm_exp]))
  rw [exp_log hz0, hlog] at key
  refine key.trans_eq ?_
  congr 2
  field_simp [(sub_pos.mpr hlu).ne']
  ring

end Complex

end
