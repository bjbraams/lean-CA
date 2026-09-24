/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Holomorphic gluing across the real axis

A continuous function on an open planar domain which is holomorphic off the real axis
is holomorphic throughout the domain. Rectangular Morera integrals split at the axis;
Cauchy–Goursat applies to the two pieces. Banach-valued functions are allowed.

## Main results

* `Complex.wedgeIntegral_boundary_split_im`: A horizontal cut splits a rectangular boundary
  integral into the two boundary integrals.
* `Complex.differentiableOn_of_continuousOn_off_real`: A continuous Banach-valued function
  holomorphic off the real axis is holomorphic on the whole open domain.
* `Complex.analyticOnNhd_of_continuousOn_off_real`: The analytic formulation of holomorphic
  gluing across the real axis.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Metric MeasureTheory
open scoped Topology Interval

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- A horizontal cut splits a rectangular boundary integral into the two boundary integrals. -/
theorem wedgeIntegral_boundary_split_im {f : ℂ → F} {z w : ℂ} {t : ℝ}
    (hc : ContinuousOn f (Rectangle z w)) (ht : t ∈ [[z.im, w.im]]) :
    wedgeIntegral z w f + wedgeIntegral w z f =
      (wedgeIntegral z (w.re + t * I) f + wedgeIntegral (w.re + t * I) z f) +
      (wedgeIntegral (z.re + t * I) w f + wedgeIntegral w (z.re + t * I) f) := by
  have hi (x : ℝ) (hx : x ∈ [[z.re, w.re]]) :
      IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume z.im w.im := by
    apply ContinuousOn.intervalIntegrable
    apply hc.comp (by fun_prop)
    intro y hy
    simpa [Rectangle, mem_reProdIm] using And.intro hx hy
  have hw := intervalIntegral.integral_add_adjacent_intervals
    ((hi w.re (right_mem_uIcc)).mono_set (uIcc_subset_uIcc_left ht))
    ((hi w.re (right_mem_uIcc)).mono_set (uIcc_subset_uIcc_right ht))
  have hz := intervalIntegral.integral_add_adjacent_intervals
    ((hi z.re (left_mem_uIcc)).mono_set (uIcc_subset_uIcc_left ht))
    ((hi z.re (left_mem_uIcc)).mono_set (uIcc_subset_uIcc_right ht))
  simp only [wedgeIntegral_add_wedgeIntegral_eq, add_re, ofReal_re, mul_re,
    ofReal_im, I_re, mul_zero, I_im, sub_self, add_zero,
    add_im, mul_im, mul_one, zero_add] at hw hz ⊢
  rw [← hw, ← hz, smul_add, smul_add]
  abel

omit [CompleteSpace F] in
/-- A rectangle lying on one side of the real axis has zero boundary integral when the
function is continuous on the rectangle and holomorphic off the axis. -/
private theorem boundary_eq_zero_of_im_sameSide {f : ℂ → F} {z w : ℂ}
    (hc : ContinuousOn f (Rectangle z w))
    (hd : ∀ x ∈ Rectangle z w, x.im ≠ 0 → DifferentiableAt ℂ f x)
    (hs : 0 ≤ min z.im w.im ∨ max z.im w.im ≤ 0) :
    wedgeIntegral z w f + wedgeIntegral w z f = 0 := by
  rw [wedgeIntegral_add_wedgeIntegral_eq]
  apply integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f z w ∅ countable_empty hc
  intro x hx
  have hmem : x ∈ Rectangle z w := ⟨Ioo_subset_Icc_self hx.1.1,
    Ioo_subset_Icc_self hx.1.2⟩
  apply hd x hmem
  rcases hs with hs | hs
  · exact ne_of_gt (hs.trans_lt hx.1.2.1)
  · exact ne_of_lt (hx.1.2.2.trans_le hs)

/-- A continuous Banach-valued function holomorphic off the real axis is holomorphic
on the whole open domain. -/
theorem differentiableOn_of_continuousOn_off_real {U : Set ℂ} {f : ℂ → F}
    (hU : IsOpen U) (hc : ContinuousOn f U)
    (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ f z) : DifferentiableOn ℂ f U := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_, hc⟩
  intro z w hrect
  rw [← add_eq_zero_iff_eq_neg]
  wlog hzw : z.im ≤ w.im generalizing z w
  · have he := this w z (by simpa [Rectangle, uIcc_comm] using hrect) (le_of_not_ge hzw)
    simpa [add_comm] using he
  by_cases hz : 0 ≤ z.im
  · exact boundary_eq_zero_of_im_sameSide (hc.mono hrect)
      (fun x hx => hd x (hrect hx)) (Or.inl (by simpa [min_eq_left hzw] using hz))
  by_cases hw : w.im ≤ 0
  · exact boundary_eq_zero_of_im_sameSide (hc.mono hrect)
      (fun x hx => hd x (hrect hx)) (Or.inr (by simpa [max_eq_right hzw] using hw))
  have hz0 : z.im ≤ 0 := le_of_lt (lt_of_not_ge hz)
  have hw0 : 0 ≤ w.im := le_of_lt (lt_of_not_ge hw)
  have hlo : Rectangle z (w.re : ℂ) ⊆ Rectangle z w := by
    intro x hx
    change x.re ∈ [[z.re, w.re]] ∧ x.im ∈ [[z.im, w.im]]
    simp only [Rectangle, mem_reProdIm, ofReal_re, ofReal_im,
      uIcc_of_le hz0, mem_Icc] at hx
    exact ⟨hx.1, (uIcc_of_le hzw).symm ▸ ⟨hx.2.1, hx.2.2.trans hw0⟩⟩
  have hhi : Rectangle (z.re : ℂ) w ⊆ Rectangle z w := by
    intro x hx
    change x.re ∈ [[z.re, w.re]] ∧ x.im ∈ [[z.im, w.im]]
    simp only [Rectangle, mem_reProdIm, ofReal_re, ofReal_im,
      uIcc_of_le hw0, mem_Icc] at hx
    exact ⟨hx.1, (uIcc_of_le hzw).symm ▸ ⟨hz0.trans hx.2.1, hx.2.2⟩⟩
  have h1 := boundary_eq_zero_of_im_sameSide (hc.mono (hlo.trans hrect))
    (fun x hx => hd x (hrect (hlo hx))) (Or.inr (by simpa using hz0))
  have h2 := boundary_eq_zero_of_im_sameSide (hc.mono (hhi.trans hrect))
    (fun x hx => hd x (hrect (hhi hx))) (Or.inl (by simpa using hw0))
  have hs := wedgeIntegral_boundary_split_im (hc.mono hrect)
    (show (0 : ℝ) ∈ [[z.im, w.im]] by simpa [uIcc_of_le hzw] using And.intro hz0 hw0)
  simpa only [ofReal_zero, zero_mul, add_zero, h1, h2, add_zero] using hs

/-- The analytic formulation of holomorphic gluing across the real axis. -/
theorem analyticOnNhd_of_continuousOn_off_real {U : Set ℂ} {f : ℂ → F}
    (hU : IsOpen U) (hc : ContinuousOn f U)
    (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ f z) : AnalyticOnNhd ℂ f U :=
  (differentiableOn_of_continuousOn_off_real hU hc hd).analyticOnNhd hU

end Complex
