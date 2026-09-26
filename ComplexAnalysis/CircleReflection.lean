/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Reflection

/-!
# Reflection across a circle

The Schwarz reflection principle (`Reflection.lean`) is specific to the real axis. This file
proves the next classical instance of reflection across an *analytic arc*: reflection across a
circle `‖z‖ = r`, the first genuinely curved case.

The proof reduces to the real-axis case via the Cayley-type Möbius map
`cayleyCircle r z = I * (r - z) / (r + z)`,
which sends the circle `‖z‖ = r` to the real axis, the disc `‖z‖ < r` to the upper half-plane,
and the exterior `‖z‖ > r` to the lower half-plane — all three facts following from a single
closed-form identity for its imaginary part,
`(cayleyCircle r z).im = (r ^ 2 - ‖z‖ ^ 2) / ‖z + r‖ ^ 2`.
Crucially, `cayleyCircle r` conjugates circle inversion `z ↦ r ^ 2 / conj z` to complex
conjugation: `cayleyCircle r (r ^ 2 / conj z) = conj (cayleyCircle r z)`. Consequently, for `f`
holomorphic inside the circle, continuous up to it, and real-valued on it, the function
`g := f ∘ cayleyCircleInv r` is holomorphic in the upper half-plane, continuous up to `ℝ`, and
real-valued there, so `Reflection.lean`'s `schwarzReflection g` is entire (on the transported
domain) by the existing theorem; pulling back along `cayleyCircle r` (itself holomorphic away
from its pole `-r`) shows `circleReflection r f = schwarzReflection g ∘ cayleyCircle r` is
holomorphic on the original domain.

The domain hypotheses mirror `Reflection.lean`'s: an open, inversion-invariant set `U` avoiding
the inversion pole `0` and the Möbius pole `-r`.

## Main definitions

* `Complex.cayleyCircle`, `Complex.cayleyCircleInv`: the Cayley-type map and its inverse.
* `Complex.circleReflection`: the reflected extension of `f` across `‖z‖ = r`.

## Main results

* `Complex.analyticOnNhd_circleReflection`: **reflection across a circle**.

## References

* L. V. Ahlfors, *Complex Analysis*, Chapter 4, Section 6.5.
* S. Lang, *Complex Analysis*, Chapter IX, Section 2.
-/

public noncomputable section

open Set Filter Metric Function
open scoped Topology ComplexConjugate

namespace Complex

/-- A Cayley-type Möbius map sending the circle `‖z‖ = r` to the real axis and the disc
`‖z‖ < r` to the upper half-plane. Its pole is at `z = -r`. -/
def cayleyCircle (r : ℝ) (z : ℂ) : ℂ := Complex.I * ((r : ℂ) - z) / ((r : ℂ) + z)

/-- The inverse of `cayleyCircle r`. Its pole is at `w = -I`. -/
def cayleyCircleInv (r : ℝ) (w : ℂ) : ℂ := (r : ℂ) * (Complex.I - w) / (w + Complex.I)

variable {r : ℝ}

/-- **The imaginary part of `cayleyCircle r z` in closed form.** The source of every geometric
fact about `cayleyCircle` used below. -/
theorem im_cayleyCircle (r : ℝ) (z : ℂ) :
    (cayleyCircle r z).im = (r ^ 2 - normSq z) / normSq (z + (r : ℂ)) := by
  unfold cayleyCircle
  rw [Complex.div_im]
  have hare : (Complex.I * ((r : ℂ) - z)).re = z.im := by simp [Complex.mul_re]
  have haim : (Complex.I * ((r : ℂ) - z)).im = r - z.re := by simp [Complex.mul_im]
  rw [hare, haim, show z + (r : ℂ) = (r : ℂ) + z from by ring]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- `‖z‖ ^ 2` in terms of `normSq`. -/
private theorem normSq_eq_norm_sq' (z : ℂ) : normSq z = ‖z‖ ^ 2 := (Complex.sq_norm z).symm

/-- The denominator `‖z + r‖ ^ 2` of `im_cayleyCircle` vanishes only at the pole `z = -r`. -/
theorem normSq_add_ofReal_pos_of_ne {z : ℂ} (hz : z ≠ -(r : ℂ)) : 0 < normSq (z + (r : ℂ)) := by
  rw [normSq_pos]
  intro h
  apply hz
  linear_combination h

/-- `cayleyCircle r` sends the interior of the circle into the upper half-plane. -/
theorem cayleyCircle_im_pos_of_norm_lt {z : ℂ} (hz : ‖z‖ < r) :
    0 < (cayleyCircle r z).im := by
  have hzr : z ≠ -(r : ℂ) := by
    intro h; rw [h] at hz; simp at hz; linarith [le_abs_self r]
  rw [im_cayleyCircle]
  apply div_pos _ (normSq_add_ofReal_pos_of_ne hzr)
  rw [normSq_eq_norm_sq']
  nlinarith [norm_nonneg z]

/-- `cayleyCircle r` sends the circle itself to the real axis. -/
@[simp] theorem cayleyCircle_im_eq_zero_of_norm_eq {z : ℂ} (hz : ‖z‖ = r) :
    (cayleyCircle r z).im = 0 := by
  rw [im_cayleyCircle, normSq_eq_norm_sq', hz]
  simp

/-- `cayleyCircle r` sends the exterior of the circle into the lower half-plane. -/
theorem cayleyCircle_im_neg_of_lt_norm {z : ℂ} (hr : 0 ≤ r) (hz : r < ‖z‖) :
    (cayleyCircle r z).im < 0 := by
  have hzr : z ≠ -(r : ℂ) := by
    intro h; rw [h] at hz; simp at hz; linarith [abs_of_nonneg hr]
  rw [im_cayleyCircle]
  apply div_neg_of_neg_of_pos _ (normSq_add_ofReal_pos_of_ne hzr)
  rw [normSq_eq_norm_sq']
  nlinarith [norm_nonneg z]

/-- `cayleyCircleInv r` is a left inverse of `cayleyCircle r` away from the pole `-r`. -/
theorem cayleyCircleInv_cayleyCircle (hr : 0 < r) {z : ℂ} (hz : z ≠ -(r : ℂ)) :
    cayleyCircleInv r (cayleyCircle r z) = z := by
  have hrz : (r : ℂ) + z ≠ 0 := fun h ↦ hz (by linear_combination h)
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hWI : cayleyCircle r z + Complex.I = 2 * Complex.I * r / ((r : ℂ) + z) := by
    unfold cayleyCircle; field_simp; ring
  have hWmI : Complex.I - cayleyCircle r z = 2 * Complex.I * z / ((r : ℂ) + z) := by
    unfold cayleyCircle; field_simp; ring
  unfold cayleyCircleInv
  rw [hWmI, hWI]
  have hIr : (2 : ℂ) * Complex.I * r ≠ 0 := by simp [hr0]
  field_simp

/-- `cayleyCircleInv r` is a right inverse of `cayleyCircle r` away from the pole `-I`. -/
theorem cayleyCircle_cayleyCircleInv (hr : 0 < r) {w : ℂ} (hw : w ≠ -Complex.I) :
    cayleyCircle r (cayleyCircleInv r w) = w := by
  have hwI : w + Complex.I ≠ 0 := fun h ↦ hw (by linear_combination h)
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsub : (r : ℂ) - cayleyCircleInv r w = 2 * r * w / (w + Complex.I) := by
    unfold cayleyCircleInv; field_simp; ring
  have hadd : (r : ℂ) + cayleyCircleInv r w = 2 * r * Complex.I / (w + Complex.I) := by
    unfold cayleyCircleInv; field_simp; ring
  unfold cayleyCircle
  rw [hsub, hadd]
  have hrI : (2 : ℂ) * r * Complex.I ≠ 0 := by simp [hr0]
  field_simp

/-- `cayleyCircle r` is differentiable away from its pole `-r`. -/
theorem differentiableAt_cayleyCircle {z : ℂ} (hz : (r : ℂ) + z ≠ 0) :
    DifferentiableAt ℂ (cayleyCircle r) z := by
  unfold cayleyCircle
  exact (((differentiableAt_const (r : ℂ)).sub differentiableAt_id).const_mul _).div
    ((differentiableAt_const (r : ℂ)).add differentiableAt_id) hz

/-- `cayleyCircleInv r` is differentiable away from its pole `-I`. -/
theorem differentiableAt_cayleyCircleInv (r : ℝ) {w : ℂ} (hw : w + Complex.I ≠ 0) :
    DifferentiableAt ℂ (cayleyCircleInv r) w := by
  unfold cayleyCircleInv
  exact (((differentiableAt_const Complex.I).sub differentiableAt_id).const_mul (r : ℂ)).div
    (differentiableAt_id.add (differentiableAt_const Complex.I)) hw

/-- **`cayleyCircle r` conjugates circle inversion to complex conjugation.** The algebraic heart
of the reduction to `Reflection.lean`'s real-axis case. -/
theorem cayleyCircle_inv_conj (hr : 0 < r) {z : ℂ} (hz0 : z ≠ 0) (hzr : z ≠ -(r : ℂ)) :
    cayleyCircle r ((r : ℂ) ^ 2 / conj z) = conj (cayleyCircle r z) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcz0 : conj z ≠ 0 := by simpa using hz0
  have hczr : (r : ℂ) + conj z ≠ 0 := by
    intro h
    apply hzr
    have h' : conj ((r : ℂ) + conj z) = conj 0 := by rw [h]
    simp only [map_add, Complex.conj_ofReal, Complex.conj_conj, map_zero] at h'
    linear_combination h'
  have hLden : (r : ℂ) + (r : ℂ) ^ 2 / conj z ≠ 0 := by
    have heq : (r : ℂ) + (r : ℂ) ^ 2 / conj z = (r * (conj z + r)) / conj z := by
      field_simp
    rw [heq]
    exact div_ne_zero (mul_ne_zero hr0 (add_comm (r : ℂ) (conj z) ▸ hczr)) hcz0
  unfold cayleyCircle
  rw [map_div₀, map_mul, map_sub, Complex.conj_I, map_add, Complex.conj_ofReal,
    div_eq_div_iff hLden hczr]
  field_simp
  ring

/-- **The reflected extension of `f` across the circle `‖z‖ = r`.** -/
def circleReflection (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ r then f z else conj (f ((r : ℂ) ^ 2 / conj z))

/-- The reflection preserves all values inside and on the circle. -/
@[simp] theorem circleReflection_of_le {f : ℂ → ℂ} {z : ℂ} (hz : ‖z‖ ≤ r) :
    circleReflection r f z = f z := by
  unfold circleReflection; simp [hz]

/-- Outside the circle the reflected value is the conjugate of the value at the inverse point. -/
theorem circleReflection_of_gt {f : ℂ → ℂ} {z : ℂ} (hz : r < ‖z‖) :
    circleReflection r f z = conj (f ((r : ℂ) ^ 2 / conj z)) := by
  unfold circleReflection; simp [not_le.mpr hz]

/-- `cayleyCircle r` never hits `-I`: its image misses the pole of `cayleyCircleInv r`. -/
theorem cayleyCircle_ne_neg_I (hr : 0 < r) (z : ℂ) : cayleyCircle r z ≠ -Complex.I := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold cayleyCircle
  rcases eq_or_ne ((r : ℂ) + z) 0 with h0 | h0
  · rw [h0, div_zero]
    intro h
    exact Complex.I_ne_zero (neg_eq_zero.mp h.symm)
  · intro heq
    rw [div_eq_iff h0] at heq
    have hr2I : (r : ℂ) * (2 * Complex.I) = 0 := by linear_combination heq
    have h2I : (2 : ℂ) * Complex.I ≠ 0 := by simp
    exact hr0 ((mul_eq_zero.mp hr2I).resolve_right h2I)

/-- `cayleyCircleInv r` never hits `-r`: its image misses the pole of `cayleyCircle r`. -/
theorem cayleyCircleInv_ne_neg_ofReal (hr : 0 < r) (w : ℂ) :
    cayleyCircleInv r w ≠ -(r : ℂ) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold cayleyCircleInv
  rcases eq_or_ne (w + Complex.I) 0 with h0 | h0
  · rw [h0, div_zero]
    intro h
    exact hr0 (neg_eq_zero.mp h.symm)
  · intro heq
    rw [div_eq_iff h0] at heq
    have hr2I : (r : ℂ) * (2 * Complex.I) = 0 := by linear_combination heq
    have h2I : (2 : ℂ) * Complex.I ≠ 0 := by simp
    exact hr0 ((mul_eq_zero.mp hr2I).resolve_right h2I)

/-- **The norm relation transported through `cayleyCircleInv`.** The sign of `w.im` controls
whether `cayleyCircleInv r w` lands inside, on, or outside the circle of radius `r`. -/
theorem normSq_cayleyCircleInv (hr : 0 < r) {w : ℂ} (hw : w ≠ -Complex.I) :
    normSq (cayleyCircleInv r w) =
      r ^ 2 - w.im * normSq (cayleyCircleInv r w + (r : ℂ)) := by
  have h := im_cayleyCircle r (cayleyCircleInv r w)
  rw [cayleyCircle_cayleyCircleInv hr hw] at h
  have hd : (0:ℝ) < normSq (cayleyCircleInv r w + (r : ℂ)) :=
    normSq_add_ofReal_pos_of_ne (cayleyCircleInv_ne_neg_ofReal hr w)
  rw [eq_div_iff hd.ne'] at h
  linarith [h]

/-- `cayleyCircleInv r` sends the closed upper half-plane into the closed disc. -/
theorem norm_cayleyCircleInv_le_of_im_nonneg (hr : 0 < r) {w : ℂ} (hw : 0 ≤ w.im) :
    ‖cayleyCircleInv r w‖ ≤ r := by
  have hwI : w ≠ -Complex.I := by
    intro h; rw [h] at hw; simp at hw; linarith
  have h := normSq_cayleyCircleInv hr hwI
  rw [← Complex.sq_norm] at h
  nlinarith [normSq_nonneg (cayleyCircleInv r w + (r : ℂ)), norm_nonneg (cayleyCircleInv r w)]

/-- `cayleyCircleInv r` sends the open upper half-plane into the open disc. -/
theorem norm_cayleyCircleInv_lt_of_im_pos (hr : 0 < r) {w : ℂ} (hw : 0 < w.im) :
    ‖cayleyCircleInv r w‖ < r := by
  have hwI : w ≠ -Complex.I := by
    intro h; rw [h] at hw; simp at hw; linarith
  have h := normSq_cayleyCircleInv hr hwI
  rw [← Complex.sq_norm] at h
  have hd : (0:ℝ) < normSq (cayleyCircleInv r w + (r : ℂ)) :=
    normSq_add_ofReal_pos_of_ne (cayleyCircleInv_ne_neg_ofReal hr w)
  nlinarith [norm_nonneg (cayleyCircleInv r w)]

/-- `cayleyCircleInv r` sends the real axis onto the circle. -/
theorem norm_cayleyCircleInv_eq_of_im_eq_zero (hr : 0 < r) {w : ℂ} (hw : w.im = 0) :
    ‖cayleyCircleInv r w‖ = r := by
  have hwI : w ≠ -Complex.I := by
    intro h; rw [h] at hw; simp at hw
  have h := normSq_cayleyCircleInv hr hwI
  rw [← Complex.sq_norm, hw, zero_mul, sub_zero] at h
  nlinarith [norm_nonneg (cayleyCircleInv r w), hr.le]

/-- `r ^ 2 / conj z` never hits `-r`, away from the pole `0` and the fixed point `-r` of
inversion. -/
private theorem sq_div_conj_ne_neg_ofReal (hr : 0 < r) {z : ℂ} (hz0 : z ≠ 0)
    (hzr : z ≠ -(r : ℂ)) : (r : ℂ) ^ 2 / conj z ≠ -(r : ℂ) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcz0 : conj z ≠ 0 := by simpa using hz0
  intro h
  rw [div_eq_iff hcz0] at h
  apply hzr
  have hcz : conj z = -(r : ℂ) := by
    apply mul_left_cancel₀ hr0
    linear_combination h
  have h2 := congrArg conj hcz
  simpa using h2

/-- **Reflection across a circle.** Analogue of `Complex.analyticOnNhd_schwarzReflection` for
the circle `‖z‖ = r` in place of the real axis: on an open, inversion-invariant domain `U`
avoiding the inversion pole `0` and the Möbius pole `-r`, a function holomorphic inside the
circle, continuous up to it, and real-valued on it extends holomorphically across the circle. -/
theorem analyticOnNhd_circleReflection {r : ℝ} (hr : 0 < r) {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (h0 : (0 : ℂ) ∉ U) (hmr : -(r : ℂ) ∉ U)
    (hs : MapsTo (fun z ↦ (r : ℂ) ^ 2 / conj z) U U)
    (hc : ContinuousOn f (U ∩ closedBall 0 r))
    (hd : DifferentiableOn ℂ f (U ∩ ball 0 r))
    (hreal : ∀ z ∈ U, ‖z‖ = r → (f z).im = 0) :
    AnalyticOnNhd ℂ (circleReflection r f) U := by
  set ψ : ℂ → ℂ := cayleyCircleInv r with hψ_def
  set φ : ℂ → ℂ := cayleyCircle r with hφ_def
  set V : Set ℂ := {w : ℂ | w ≠ -Complex.I} ∩ ψ ⁻¹' U
  set g : ℂ → ℂ := f ∘ ψ with hg_def
  have hψcont : ContinuousOn ψ {w : ℂ | w ≠ -Complex.I} := fun w hw ↦
    (differentiableAt_cayleyCircleInv r
      (fun h ↦ hw (by linear_combination h))).continuousAt.continuousWithinAt
  have hφV : MapsTo φ U V := by
    intro z hz
    have hzr : z ≠ -(r : ℂ) := fun h ↦ hmr (h ▸ hz)
    refine ⟨cayleyCircle_ne_neg_I hr z, ?_⟩
    rw [Set.mem_preimage, hψ_def, hφ_def, cayleyCircleInv_cayleyCircle hr hzr]
    exact hz
  have hVopen : IsOpen V := hψcont.isOpen_inter_preimage isOpen_ne hU
  have hVconj : MapsTo (starRingEnd ℂ) V V := by
    intro w hw
    obtain ⟨hwI, hwU⟩ := hw
    have hzU : ψ w ∈ U := hwU
    have hz0 : ψ w ≠ 0 := fun h ↦ h0 (h ▸ hzU)
    have hzr : ψ w ≠ -(r : ℂ) := fun h ↦ hmr (h ▸ hzU)
    have hwφz : φ (ψ w) = w := cayleyCircle_cayleyCircleInv hr hwI
    have hconjw : conj w = φ ((r : ℂ) ^ 2 / conj (ψ w)) := by
      conv_lhs => rw [← hwφz]
      exact (cayleyCircle_inv_conj hr hz0 hzr).symm
    refine ⟨?_, ?_⟩
    · rw [hconjw]; exact cayleyCircle_ne_neg_I hr _
    · rw [Set.mem_preimage, hconjw, hψ_def, hφ_def,
        cayleyCircleInv_cayleyCircle hr (sq_div_conj_ne_neg_ofReal hr hz0 hzr)]
      exact hs hzU
  have hψmapsC : MapsTo ψ (V ∩ {z : ℂ | 0 ≤ z.im}) (U ∩ closedBall 0 r) := by
    rintro w ⟨⟨_, hwU⟩, hwim⟩
    exact ⟨hwU, mem_closedBall_zero_iff.mpr (norm_cayleyCircleInv_le_of_im_nonneg hr hwim)⟩
  have hψmapsO : MapsTo ψ (V ∩ {z : ℂ | 0 < z.im}) (U ∩ ball 0 r) := by
    rintro w ⟨⟨_, hwU⟩, hwim⟩
    exact ⟨hwU, mem_ball_zero_iff.mpr (norm_cayleyCircleInv_lt_of_im_pos hr hwim)⟩
  have hgcont : ContinuousOn g (V ∩ {z : ℂ | 0 ≤ z.im}) :=
    hc.comp (hψcont.mono (fun w hw ↦ hw.1.1)) hψmapsC
  have hgdiff : DifferentiableOn ℂ g (V ∩ {z : ℂ | 0 < z.im}) := by
    intro w hw
    have h1 : DifferentiableWithinAt ℂ ψ (V ∩ {z : ℂ | 0 < z.im}) w :=
      (differentiableAt_cayleyCircleInv r
        (fun h ↦ hw.1.1 (by linear_combination h))).differentiableWithinAt
    exact DifferentiableWithinAt.comp (f := ψ) (x := w) (hd (ψ w) (hψmapsO hw)) h1 hψmapsO
  have hgreal : ∀ w ∈ V, w.im = 0 → (g w).im = 0 := by
    intro w hw himeq
    exact hreal (ψ w) hw.2 (norm_cayleyCircleInv_eq_of_im_eq_zero hr himeq)
  have hgan : AnalyticOnNhd ℂ (schwarzReflection g) V :=
    analyticOnNhd_schwarzReflection hVopen hVconj hgcont hgdiff hgreal
  have hφan : AnalyticOnNhd ℂ φ U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hzne : (r : ℂ) + z ≠ 0 := by
      intro h
      apply hmr
      have hz' : z = -(r : ℂ) := by linear_combination h
      rwa [hz'] at hz
    exact (differentiableAt_cayleyCircle hzne).differentiableWithinAt
  have hcomp : AnalyticOnNhd ℂ (schwarzReflection g ∘ φ) U := hgan.comp hφan hφV
  have heq : Set.EqOn (circleReflection r f) (schwarzReflection g ∘ φ) U := by
    intro z hz
    have hzr : z ≠ -(r : ℂ) := fun h ↦ hmr (h ▸ hz)
    simp only [Function.comp_apply]
    by_cases hzle : ‖z‖ ≤ r
    · rw [circleReflection_of_le hzle]
      have him : 0 ≤ (φ z).im := by
        rcases hzle.lt_or_eq with h | h
        · exact (cayleyCircle_im_pos_of_norm_lt h).le
        · exact (cayleyCircle_im_eq_zero_of_norm_eq h).ge
      rw [schwarzReflection_of_nonneg him, hg_def]
      simp only [Function.comp_apply]
      rw [hψ_def, hφ_def, cayleyCircleInv_cayleyCircle hr hzr]
    · rw [not_le] at hzle
      rw [circleReflection_of_gt hzle]
      have him : (φ z).im < 0 := cayleyCircle_im_neg_of_lt_norm hr.le hzle
      have hz0 : z ≠ 0 := fun h ↦ h0 (h ▸ hz)
      rw [schwarzReflection_of_neg him, hg_def]
      simp only [Function.comp_apply]
      congr 1
      congr 1
      have hkey : conj (φ z) = φ ((r : ℂ) ^ 2 / conj z) := by
        rw [hφ_def, cayleyCircle_inv_conj hr hz0 hzr]
      rw [hkey, hψ_def, hφ_def,
        cayleyCircleInv_cayleyCircle hr (sq_div_conj_ne_neg_ofReal hr hz0 hzr)]
  exact hcomp.congr hU heq.symm

end Complex
end
