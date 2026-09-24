/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Cycle.Residue
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

The cancellation uses one algebraic fact about the gluing function `Real.smoothTransition` not
recorded where it is defined: `smoothTransition (1 - x) = 1 - smoothTransition x`, immediate
from its own defining formula `expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))`.

## Main results

* `Complex.curveIntegral_toSpanSingleton_parallelogramLoop_eq_zero`: the boundary integral of a
  doubly periodic function over a period parallelogram vanishes.

## References

* R. Remmert, *Theory of Complex Functions*, Chapter 9, Section 1.
-/

public noncomputable section

open Set MeasureTheory Metric Filter ContinuousLinearMap
open scoped Topology unitInterval

namespace Complex

/-- `smoothTransition (1 - x) = 1 - smoothTransition x`: the gluing function is symmetric
about `1/2`. -/
theorem smoothTransition_one_sub (x : ℝ) :
    Real.smoothTransition (1 - x) = 1 - Real.smoothTransition x := by
  unfold Real.smoothTransition
  rw [show (1:ℝ) - (1 - x) = x by ring]
  have h1 : expNegInvGlue x + expNegInvGlue (1 - x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  have h2 : expNegInvGlue (1 - x) + expNegInvGlue x ≠ 0 := by
    have := (Real.smoothTransition.pos_denom (1 - x)).ne'
    simpa using this
  field_simp
  ring

/-- The derivative of `Real.smoothTransition` is symmetric about `1/2`. -/
theorem deriv_smoothTransition_one_sub (x : ℝ) :
    deriv Real.smoothTransition (1 - x) = deriv Real.smoothTransition x := by
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).differentiable (by norm_num)
  have h1 : HasDerivAt (fun y : ℝ => Real.smoothTransition (1 - y))
      (deriv Real.smoothTransition (1 - x) * (-1)) x := by
    have ha : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (1 - x)) (1 - x) :=
      (hdiff (1 - x)).hasDerivAt
    have hb : HasDerivAt (fun y : ℝ => (1:ℝ) - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1:ℝ)
    exact ha.comp x hb
  have h2 : HasDerivAt (fun x => (1:ℝ) - Real.smoothTransition x)
      (-(deriv Real.smoothTransition x)) x :=
    ((hdiff x).hasDerivAt).const_sub 1
  rw [funext smoothTransition_one_sub] at h1
  have huniq := h1.unique h2
  linarith

/-- The parallelogram loop's derivative on the open first edge `(0, 1/4)`. -/
theorem hasDerivAt_parallelogramFun_edge1 (c w1 w2 : ℂ) {t : ℝ} (ht : t < 1 / 4) :
    HasDerivAt (parallelogramFun c w1 w2)
      ((4 * deriv Real.smoothTransition (4 * t) : ℝ) * w1) t := by
  have heqf : parallelogramFun c w1 w2 =ᶠ[𝓝 t]
      (fun s => c + (Real.smoothTransition (4 * s) : ℂ) * w1) :=
    Filter.eventually_of_mem (isOpen_Iio.mem_nhds ht)
      (fun s hs => parallelogramFun_eq_edge1 c w1 w2 hs.le)
  have hst : HasDerivAt (fun s : ℝ => Real.smoothTransition (4 * s))
      (deriv Real.smoothTransition (4 * t) * 4) t := by
    have ha : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (4 * t)) (4 * t) :=
      ((Real.smoothTransition.contDiff (n := ⊤)).differentiable
        (by norm_num)).differentiableAt.hasDerivAt
    have hb : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4:ℝ)
    exact ha.comp t hb
  have haff : HasDerivAt (fun s : ℝ => c + (Real.smoothTransition (4 * s) : ℂ) * w1)
      (((deriv Real.smoothTransition (4 * t) * 4 : ℝ) : ℂ) * w1) t := by
    have h1 : HasDerivAt (fun s : ℝ => (Real.smoothTransition (4 * s) : ℂ))
        ((deriv Real.smoothTransition (4 * t) * 4 : ℝ) : ℂ) t := hst.ofReal_comp
    simpa using (h1.mul_const w1).const_add c
  have := haff.congr_of_eventuallyEq heqf
  convert this using 1
  push_cast; ring

/-- The parallelogram loop's derivative on the open third edge `(1/2, 3/4)`. -/
theorem hasDerivAt_parallelogramFun_edge3 (c w1 w2 : ℂ) {t : ℝ}
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4)) :
    HasDerivAt (parallelogramFun c w1 w2)
      ((4 * deriv Real.smoothTransition (4 * t - 2) : ℝ) * (-w1)) t := by
  have heqf : parallelogramFun c w1 w2 =ᶠ[𝓝 t]
      (fun s => c + w1 + w2 + (Real.smoothTransition (4 * s - 2) : ℂ) * (-w1)) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht)
      (fun s hs => parallelogramFun_eq_edge3 c w1 w2 hs.1.le hs.2.le)
  have hst : HasDerivAt (fun s : ℝ => Real.smoothTransition (4 * s - 2))
      (deriv Real.smoothTransition (4 * t - 2) * 4) t := by
    have ha : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (4 * t - 2))
        (4 * t - 2) :=
      ((Real.smoothTransition.contDiff (n := ⊤)).differentiable
        (by norm_num)).differentiableAt.hasDerivAt
    have hb : HasDerivAt (fun s : ℝ => 4 * s - 2) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4:ℝ) |>.sub_const (2:ℝ)
    exact ha.comp t hb
  have haff : HasDerivAt
      (fun s : ℝ => c + w1 + w2 + (Real.smoothTransition (4 * s - 2) : ℂ) * (-w1))
      (((deriv Real.smoothTransition (4 * t - 2) * 4 : ℝ) : ℂ) * (-w1)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (Real.smoothTransition (4 * s - 2) : ℂ))
        ((deriv Real.smoothTransition (4 * t - 2) * 4 : ℝ) : ℂ) t := hst.ofReal_comp
    simpa using (h1.mul_const (-w1)).const_add (c + w1 + w2)
  have := haff.congr_of_eventuallyEq heqf
  convert this using 1
  push_cast; ring

/-- The parallelogram loop's derivative on the open second edge `(1/4, 1/2)`. -/
theorem hasDerivAt_parallelogramFun_edge2 (c w1 w2 : ℂ) {t : ℝ}
    (ht : t ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) :
    HasDerivAt (parallelogramFun c w1 w2)
      ((4 * deriv Real.smoothTransition (4 * t - 1) : ℝ) * w2) t := by
  have heqf : parallelogramFun c w1 w2 =ᶠ[𝓝 t]
      (fun s => c + w1 + (Real.smoothTransition (4 * s - 1) : ℂ) * w2) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht)
      (fun s hs => parallelogramFun_eq_edge2 c w1 w2 hs.1.le hs.2.le)
  have hst : HasDerivAt (fun s : ℝ => Real.smoothTransition (4 * s - 1))
      (deriv Real.smoothTransition (4 * t - 1) * 4) t := by
    have ha : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (4 * t - 1))
        (4 * t - 1) :=
      ((Real.smoothTransition.contDiff (n := ⊤)).differentiable
        (by norm_num)).differentiableAt.hasDerivAt
    have hb : HasDerivAt (fun s : ℝ => 4 * s - 1) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4:ℝ) |>.sub_const (1:ℝ)
    exact ha.comp t hb
  have haff : HasDerivAt (fun s : ℝ => c + w1 + (Real.smoothTransition (4 * s - 1) : ℂ) * w2)
      (((deriv Real.smoothTransition (4 * t - 1) * 4 : ℝ) : ℂ) * w2) t := by
    have h1 : HasDerivAt (fun s : ℝ => (Real.smoothTransition (4 * s - 1) : ℂ))
        ((deriv Real.smoothTransition (4 * t - 1) * 4 : ℝ) : ℂ) t := hst.ofReal_comp
    simpa using (h1.mul_const w2).const_add (c + w1)
  have := haff.congr_of_eventuallyEq heqf
  convert this using 1
  push_cast; ring

/-- The parallelogram loop's derivative on the open fourth edge `(3/4, 1)`. -/
theorem hasDerivAt_parallelogramFun_edge4 (c w1 w2 : ℂ) {t : ℝ} (ht : 3 / 4 < t) :
    HasDerivAt (parallelogramFun c w1 w2)
      ((4 * deriv Real.smoothTransition (4 * t - 3) : ℝ) * (-w2)) t := by
  have heqf : parallelogramFun c w1 w2 =ᶠ[𝓝 t]
      (fun s => c + w2 + (Real.smoothTransition (4 * s - 3) : ℂ) * (-w2)) :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht)
      (fun s hs => parallelogramFun_eq_edge4 c w1 w2 hs.le)
  have hst : HasDerivAt (fun s : ℝ => Real.smoothTransition (4 * s - 3))
      (deriv Real.smoothTransition (4 * t - 3) * 4) t := by
    have ha : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (4 * t - 3))
        (4 * t - 3) :=
      ((Real.smoothTransition.contDiff (n := ⊤)).differentiable
        (by norm_num)).differentiableAt.hasDerivAt
    have hb : HasDerivAt (fun s : ℝ => 4 * s - 3) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4:ℝ) |>.sub_const (3:ℝ)
    exact ha.comp t hb
  have haff : HasDerivAt (fun s : ℝ => c + w2 + (Real.smoothTransition (4 * s - 3) : ℂ) * (-w2))
      (((deriv Real.smoothTransition (4 * t - 3) * 4 : ℝ) : ℂ) * (-w2)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (Real.smoothTransition (4 * s - 3) : ℂ))
        ((deriv Real.smoothTransition (4 * t - 3) * 4 : ℝ) : ℂ) t := hst.ofReal_comp
    simpa using (h1.mul_const (-w2)).const_add (c + w2)
  have := haff.congr_of_eventuallyEq heqf
  convert this using 1
  push_cast; ring


/-- The first edge's contribution to the boundary integral of `f`, rewritten as an integral
over the gluing parameter `v ∈ [0, 1]`. -/
theorem integral_edge1_eq (c w1 w2 : ℂ) (f : ℂ → ℂ) :
    (∫ t in (0:ℝ)..(1/4), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) =
      ∫ v in (0:ℝ)..1, f (c + (Real.smoothTransition v : ℂ) * w1) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * w1 := by
  have hpt : ∀ t ∈ Set.Ioo (0:ℝ) (1/4),
      f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t =
        (4:ℂ) * (f (c + (Real.smoothTransition (4*t) : ℂ) * w1) *
          ((deriv Real.smoothTransition (4*t) : ℝ) : ℂ) * w1) := by
    intro t ht
    rw [parallelogramFun_eq_edge1 c w1 w2 ht.2.le,
      (hasDerivAt_parallelogramFun_edge1 c w1 w2 ht.2).deriv]
    push_cast; ring
  have hcong : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc (0:ℝ) (1/4) →
      f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t =
        (4:ℂ) * (f (c + (Real.smoothTransition (4*t) : ℂ) * w1) *
          ((deriv Real.smoothTransition (4*t) : ℝ) : ℂ) * w1) := by
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/4), MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := {(1/4:ℝ)}) ?_ Real.volume_singleton
    intro t ht
    simp only [Set.mem_ofPred_eq, not_imp] at ht
    obtain ⟨ht1, ht2⟩ := ht
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact ht2 (hpt t ⟨ht1.1, lt_of_le_of_ne ht1.2 hne⟩)
  rw [intervalIntegral.integral_congr_ae hcong, intervalIntegral.integral_const_mul]
  rw [show ((4:ℂ) * ∫ t in (0:ℝ)..(1/4), f (c + (Real.smoothTransition (4*t) : ℂ) * w1) *
        ((deriv Real.smoothTransition (4*t) : ℝ) : ℂ) * w1) =
      (4:ℝ) • ∫ t in (0:ℝ)..(1/4), f (c + (Real.smoothTransition (4*t) : ℂ) * w1) *
        ((deriv Real.smoothTransition (4*t) : ℝ) : ℂ) * w1 by rw [Complex.real_smul]; norm_num]
  rw [intervalIntegral.smul_integral_comp_mul_left
    (fun v => f (c + (Real.smoothTransition v : ℂ) * w1) *
      ((deriv Real.smoothTransition v : ℝ) : ℂ) * w1) (4:ℝ)]
  norm_num

/-- The second edge's contribution to the boundary integral of `f`, rewritten as an integral
over the gluing parameter `v ∈ [0, 1]`. -/
theorem integral_edge2_eq (c w1 w2 : ℂ) (f : ℂ → ℂ) :
    (∫ t in (1/4:ℝ)..(1/2), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) =
      ∫ v in (0:ℝ)..1, f (c + w1 + (Real.smoothTransition v : ℂ) * (w2)) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * (w2) := by
  have hpt : ∀ t ∈ Set.Ioo (1/4:ℝ) (1/2),
      f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t =
        (4:ℂ) * (f (c + w1 + (Real.smoothTransition (4*t + (-1)) : ℂ) * (w2)) *
          ((deriv Real.smoothTransition (4*t + (-1)) : ℝ) : ℂ) * (w2)) := by
    intro t ht
    rw [parallelogramFun_eq_edge2 c w1 w2 ht.1.le ht.2.le,
      (hasDerivAt_parallelogramFun_edge2 c w1 w2 ht).deriv]
    push_cast; ring_nf
  have hcong : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc (1/4:ℝ) (1/2) →
      f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t =
        (4:ℂ) * (f (c + w1 + (Real.smoothTransition (4*t + (-1)) : ℂ) * (w2)) *
          ((deriv Real.smoothTransition (4*t + (-1)) : ℝ) : ℂ) * (w2)) := by
    rw [Set.uIoc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2), MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := {(1/2:ℝ)}) ?_ Real.volume_singleton
    intro t ht
    simp only [Set.mem_ofPred_eq, not_imp] at ht
    obtain ⟨ht1, ht2⟩ := ht
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact ht2 (hpt t ⟨ht1.1, lt_of_le_of_ne ht1.2 hne⟩)
  rw [intervalIntegral.integral_congr_ae hcong, intervalIntegral.integral_const_mul]
  rw [show ((4:ℂ) * ∫ t in (1/4:ℝ)..(1/2),
        f (c + w1 + (Real.smoothTransition (4*t + (-1)) : ℂ) * (w2)) *
        ((deriv Real.smoothTransition (4*t + (-1)) : ℝ) : ℂ) * (w2)) =
      (4:ℝ) • ∫ t in (1/4:ℝ)..(1/2),
        f (c + w1 + (Real.smoothTransition (4*t + (-1)) : ℂ) * (w2)) *
        ((deriv Real.smoothTransition (4*t + (-1)) : ℝ) : ℂ) * (w2) by
    rw [Complex.real_smul]; norm_num]
  rw [intervalIntegral.smul_integral_comp_mul_add
    (fun v => f (c + w1 + (Real.smoothTransition v : ℂ) * (w2)) *
      ((deriv Real.smoothTransition v : ℝ) : ℂ) * (w2)) (4:ℝ) (-1)]
  norm_num

/-- The third edge's contribution to the boundary integral of `f`, rewritten as an integral
over the gluing parameter `v ∈ [0, 1]`. -/
theorem integral_edge3_eq (c w1 w2 : ℂ) (f : ℂ → ℂ) :
    (∫ t in (1/2:ℝ)..(3/4), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) =
      ∫ v in (0:ℝ)..1, f (c + w1 + w2 + (Real.smoothTransition v : ℂ) * (-w1)) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * (-w1) := by
  have hpt : ∀ t ∈ Set.Ioo (1/2:ℝ) (3/4),
      f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t =
        (4:ℂ) * (f (c + w1 + w2 + (Real.smoothTransition (4*t + (-2)) : ℂ) * (-w1)) *
          ((deriv Real.smoothTransition (4*t + (-2)) : ℝ) : ℂ) * (-w1)) := by
    intro t ht
    rw [parallelogramFun_eq_edge3 c w1 w2 ht.1.le ht.2.le,
      (hasDerivAt_parallelogramFun_edge3 c w1 w2 ht).deriv]
    push_cast; ring_nf
  have hcong : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc (1/2:ℝ) (3/4) →
      f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t =
        (4:ℂ) * (f (c + w1 + w2 + (Real.smoothTransition (4*t + (-2)) : ℂ) * (-w1)) *
          ((deriv Real.smoothTransition (4*t + (-2)) : ℝ) : ℂ) * (-w1)) := by
    rw [Set.uIoc_of_le (by norm_num : (1/2:ℝ) ≤ 3/4), MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := {(3/4:ℝ)}) ?_ Real.volume_singleton
    intro t ht
    simp only [Set.mem_ofPred_eq, not_imp] at ht
    obtain ⟨ht1, ht2⟩ := ht
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact ht2 (hpt t ⟨ht1.1, lt_of_le_of_ne ht1.2 hne⟩)
  rw [intervalIntegral.integral_congr_ae hcong, intervalIntegral.integral_const_mul]
  rw [show ((4:ℂ) * ∫ t in (1/2:ℝ)..(3/4),
        f (c + w1 + w2 + (Real.smoothTransition (4*t + (-2)) : ℂ) * (-w1)) *
        ((deriv Real.smoothTransition (4*t + (-2)) : ℝ) : ℂ) * (-w1)) =
      (4:ℝ) • ∫ t in (1/2:ℝ)..(3/4),
        f (c + w1 + w2 + (Real.smoothTransition (4*t + (-2)) : ℂ) * (-w1)) *
        ((deriv Real.smoothTransition (4*t + (-2)) : ℝ) : ℂ) * (-w1) by
    rw [Complex.real_smul]; norm_num]
  rw [intervalIntegral.smul_integral_comp_mul_add
    (fun v => f (c + w1 + w2 + (Real.smoothTransition v : ℂ) * (-w1)) *
      ((deriv Real.smoothTransition v : ℝ) : ℂ) * (-w1)) (4:ℝ) (-2)]
  norm_num

/-- The fourth edge's contribution to the boundary integral of `f`, rewritten as an integral
over the gluing parameter `v ∈ [0, 1]`. -/
theorem integral_edge4_eq (c w1 w2 : ℂ) (f : ℂ → ℂ) :
    (∫ t in (3/4:ℝ)..(1), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) =
      ∫ v in (0:ℝ)..1, f (c + w2 + (Real.smoothTransition v : ℂ) * (-w2)) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * (-w2) := by
  have hpt : ∀ t ∈ Set.Ioo (3/4:ℝ) (1),
      f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t =
        (4:ℂ) * (f (c + w2 + (Real.smoothTransition (4*t + (-3)) : ℂ) * (-w2)) *
          ((deriv Real.smoothTransition (4*t + (-3)) : ℝ) : ℂ) * (-w2)) := by
    intro t ht
    rw [parallelogramFun_eq_edge4 c w1 w2 ht.1.le,
      (hasDerivAt_parallelogramFun_edge4 c w1 w2 ht.1).deriv]
    push_cast; ring_nf
  have hcong : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc (3/4:ℝ) (1) →
      f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t =
        (4:ℂ) * (f (c + w2 + (Real.smoothTransition (4*t + (-3)) : ℂ) * (-w2)) *
          ((deriv Real.smoothTransition (4*t + (-3)) : ℝ) : ℂ) * (-w2)) := by
    rw [Set.uIoc_of_le (by norm_num : (3/4:ℝ) ≤ 1), MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := {(1:ℝ)}) ?_ Real.volume_singleton
    intro t ht
    simp only [Set.mem_ofPred_eq, not_imp] at ht
    obtain ⟨ht1, ht2⟩ := ht
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact ht2 (hpt t ⟨ht1.1, lt_of_le_of_ne ht1.2 hne⟩)
  rw [intervalIntegral.integral_congr_ae hcong, intervalIntegral.integral_const_mul]
  rw [show ((4:ℂ) * ∫ t in (3/4:ℝ)..(1),
        f (c + w2 + (Real.smoothTransition (4*t + (-3)) : ℂ) * (-w2)) *
        ((deriv Real.smoothTransition (4*t + (-3)) : ℝ) : ℂ) * (-w2)) =
      (4:ℝ) • ∫ t in (3/4:ℝ)..(1),
        f (c + w2 + (Real.smoothTransition (4*t + (-3)) : ℂ) * (-w2)) *
        ((deriv Real.smoothTransition (4*t + (-3)) : ℝ) : ℂ) * (-w2) by
    rw [Complex.real_smul]; norm_num]
  rw [intervalIntegral.smul_integral_comp_mul_add
    (fun v => f (c + w2 + (Real.smoothTransition v : ℂ) * (-w2)) *
      ((deriv Real.smoothTransition v : ℝ) : ℂ) * (-w2)) (4:ℝ) (-3)]
  norm_num


/-- Edges 1 and 3, offset by periodicity in `w2`, cancel exactly. -/
theorem integral_edge1_add_edge3_eq_zero (c w1 w2 : ℂ) {f : ℂ → ℂ}
    (hper2 : Function.Periodic f w2) :
    (∫ t in (0:ℝ)..(1/4), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) +
    (∫ t in (1/2:ℝ)..(3/4), f (parallelogramFun c w1 w2 t) *
      deriv (parallelogramFun c w1 w2) t) = 0 := by
  rw [integral_edge1_eq, integral_edge3_eq]
  have hrev : (∫ v in (0:ℝ)..1, f (c + w1 + w2 + (Real.smoothTransition v : ℂ) * (-w1)) *
      ((deriv Real.smoothTransition v : ℝ) : ℂ) * (-w1)) =
      ∫ v in (0:ℝ)..1, f (c + w1 + w2 + (Real.smoothTransition (1 - v) : ℂ) * (-w1)) *
        ((deriv Real.smoothTransition (1 - v) : ℝ) : ℂ) * (-w1) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (fun v => f (c + w1 + w2 + (Real.smoothTransition v : ℂ) * (-w1)) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * (-w1)) (1:ℝ) (a := (0:ℝ)) (b := 1)
    simpa using hcomp.symm
  rw [hrev]
  have hpt : ∀ v : ℝ, f (c + w1 + w2 + (Real.smoothTransition (1 - v) : ℂ) * (-w1)) *
      ((deriv Real.smoothTransition (1 - v) : ℝ) : ℂ) * (-w1) =
      -(f (c + (Real.smoothTransition v : ℂ) * w1) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * w1) := by
    intro v
    rw [smoothTransition_one_sub, deriv_smoothTransition_one_sub]
    have hz : c + w1 + w2 + (((1:ℝ) - Real.smoothTransition v : ℝ) : ℂ) * (-w1) =
        (c + (Real.smoothTransition v : ℂ) * w1) + w2 := by push_cast; ring
    rw [hz, hper2]
    ring
  rw [intervalIntegral.integral_congr (fun v _ => hpt v)]
  rw [intervalIntegral.integral_neg]
  ring


/-- Edges 2 and 4, offset by periodicity in `w1`, cancel exactly. -/
theorem integral_edge2_add_edge4_eq_zero (c w1 w2 : ℂ) {f : ℂ → ℂ}
    (hper1 : Function.Periodic f w1) :
    (∫ t in (1/4:ℝ)..(1/2), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) +
    (∫ t in (3/4:ℝ)..1, f (parallelogramFun c w1 w2 t) *
      deriv (parallelogramFun c w1 w2) t) = 0 := by
  rw [integral_edge2_eq, integral_edge4_eq]
  have hrev : (∫ v in (0:ℝ)..1, f (c + w2 + (Real.smoothTransition v : ℂ) * (-w2)) *
      ((deriv Real.smoothTransition v : ℝ) : ℂ) * (-w2)) =
      ∫ v in (0:ℝ)..1, f (c + w2 + (Real.smoothTransition (1 - v) : ℂ) * (-w2)) *
        ((deriv Real.smoothTransition (1 - v) : ℝ) : ℂ) * (-w2) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (fun v => f (c + w2 + (Real.smoothTransition v : ℂ) * (-w2)) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * (-w2)) (1:ℝ) (a := (0:ℝ)) (b := 1)
    simpa using hcomp.symm
  rw [hrev]
  have hpt : ∀ v : ℝ, f (c + w2 + (Real.smoothTransition (1 - v) : ℂ) * (-w2)) *
      ((deriv Real.smoothTransition (1 - v) : ℝ) : ℂ) * (-w2) =
      -(f (c + w1 + (Real.smoothTransition v : ℂ) * w2) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * w2) := by
    intro v
    rw [smoothTransition_one_sub, deriv_smoothTransition_one_sub]
    have hz1 : c + w2 + (((1:ℝ) - Real.smoothTransition v : ℝ) : ℂ) * (-w2) =
        c + (Real.smoothTransition v : ℂ) * w2 := by push_cast; ring
    have hz2 : c + w1 + (Real.smoothTransition v : ℂ) * w2 =
        (c + (Real.smoothTransition v : ℂ) * w2) + w1 := by ring
    rw [hz1, hz2, hper1]
    ring
  rw [intervalIntegral.integral_congr (fun v _ => hpt v)]
  rw [intervalIntegral.integral_neg]
  ring


/-- **The boundary integral of a doubly periodic function over a period parallelogram
vanishes.** Opposite edges cancel exactly: each is the periodic translate of the other,
traversed in the opposite direction. -/
theorem curveIntegral_toSpanSingleton_parallelogramLoop_eq_zero {c w1 w2 : ℂ} {f : ℂ → ℂ}
    (hf : Continuous f) (hper1 : Function.Periodic f w1) (hper2 : Function.Periodic f w2) :
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))
      (parallelogramLoop c w1 w2) = 0 := by
  have hCIeq : curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))
      (parallelogramLoop c w1 w2) =
      ∫ t in (0:ℝ)..1, f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t := by
    rw [curveIntegral_eq_intervalIntegral_deriv, parallelogramLoop_extend]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    exact intervalIntegral.integral_congr (fun t _ => mul_comm _ _)
  rw [hCIeq]
  have hcontg : Continuous (fun t => f (parallelogramFun c w1 w2 t) *
      deriv (parallelogramFun c w1 w2) t) :=
    (hf.comp (continuous_parallelogramFun c w1 w2)).mul
      ((contDiff_parallelogramFun c w1 w2).iterate_deriv 1).continuous
  have hInt : ∀ a b : ℝ, IntervalIntegrable
      (fun t => f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t)
      MeasureTheory.volume a b := fun a b => hcontg.intervalIntegrable a b
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hInt 0 (1/4)) (hInt (1/4) (1/2))
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hInt 0 (1/2)) (hInt (1/2) (3/4))
  have hsplit3 := intervalIntegral.integral_add_adjacent_intervals
    (hInt 0 (3/4)) (hInt (3/4) 1)
  rw [← hsplit3, ← hsplit2, ← hsplit1]
  have h13 := integral_edge1_add_edge3_eq_zero c w1 w2 hper2
  have h24 := integral_edge2_add_edge4_eq_zero c w1 w2 hper1
  have hre : (∫ t in (0:ℝ)..(1/4), f (parallelogramFun c w1 w2 t) *
        deriv (parallelogramFun c w1 w2) t) +
      (∫ t in (1/4:ℝ)..(1/2), f (parallelogramFun c w1 w2 t) *
        deriv (parallelogramFun c w1 w2) t) +
      (∫ t in (1/2:ℝ)..(3/4), f (parallelogramFun c w1 w2 t) *
        deriv (parallelogramFun c w1 w2) t) +
      (∫ t in (3/4:ℝ)..1, f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) =
      ((∫ t in (0:ℝ)..(1/4), f (parallelogramFun c w1 w2 t) *
          deriv (parallelogramFun c w1 w2) t) +
        (∫ t in (1/2:ℝ)..(3/4), f (parallelogramFun c w1 w2 t) *
          deriv (parallelogramFun c w1 w2) t)) +
      ((∫ t in (1/4:ℝ)..(1/2), f (parallelogramFun c w1 w2 t) *
          deriv (parallelogramFun c w1 w2) t) +
        (∫ t in (3/4:ℝ)..1, f (parallelogramFun c w1 w2 t) *
          deriv (parallelogramFun c w1 w2) t)) := by ring
  rw [hre, h13, h24]
  ring

end Complex
end
