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
  have h1 : HasDerivAt (fun y : ℝ ↦ Real.smoothTransition (1 - y))
      (deriv Real.smoothTransition (1 - x) * (-1)) x := by
    have ha : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (1 - x)) (1 - x) :=
      (hdiff (1 - x)).hasDerivAt
    have hb : HasDerivAt (fun y : ℝ ↦ (1:ℝ) - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1:ℝ)
    exact ha.comp x hb
  have h2 : HasDerivAt (fun x ↦ (1:ℝ) - Real.smoothTransition x)
      (-(deriv Real.smoothTransition x)) x :=
    ((hdiff x).hasDerivAt).const_sub 1
  rw [funext smoothTransition_one_sub] at h1
  have huniq := h1.unique h2
  linarith

/-- The derivative of an edge `s ↦ p + smoothTransition (4 * s - k) * v` of the parallelogram
loop. -/
theorem hasDerivAt_smoothTransition_edge (p v : ℂ) (k t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ p + (Real.smoothTransition (4 * s - k) : ℂ) * v)
      ((4 * deriv Real.smoothTransition (4 * t - k) : ℝ) * v) t := by
  have ha : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (4 * t - k))
      (4 * t - k) :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  have hb : HasDerivAt (fun s : ℝ ↦ 4 * s - k) 4 t := by
    simpa using ((hasDerivAt_id t).const_mul (4 : ℝ)).sub_const k
  have hst : HasDerivAt (fun s : ℝ ↦ Real.smoothTransition (4 * s - k))
      (deriv Real.smoothTransition (4 * t - k) * 4) t := by
    exact ha.comp t hb
  have h1 : HasDerivAt (fun s : ℝ ↦ (Real.smoothTransition (4 * s - k) : ℂ))
      ((deriv Real.smoothTransition (4 * t - k) * 4 : ℝ) : ℂ) t := hst.ofReal_comp
  convert (h1.mul_const v).const_add p using 1
  push_cast
  ring

/-- The parallelogram loop's derivative on the open first edge `(0, 1/4)`. -/
theorem hasDerivAt_parallelogramFun_edge1 (c w1 w2 : ℂ) {t : ℝ} (ht : t < 1 / 4) :
    HasDerivAt (parallelogramFun c w1 w2)
      ((4 * deriv Real.smoothTransition (4 * t) : ℝ) * w1) t := by
  simpa using (hasDerivAt_smoothTransition_edge c w1 0 t).congr_of_eventuallyEq
    (Filter.eventually_of_mem (isOpen_Iio.mem_nhds ht)
      fun s hs ↦ by simpa using parallelogramFun_eq_edge1 c w1 w2 (le_of_lt hs))

/-- The parallelogram loop's derivative on the open second edge `(1/4, 1/2)`. -/
theorem hasDerivAt_parallelogramFun_edge2 (c w1 w2 : ℂ) {t : ℝ}
    (ht : t ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2)) :
    HasDerivAt (parallelogramFun c w1 w2)
      ((4 * deriv Real.smoothTransition (4 * t - 1) : ℝ) * w2) t :=
  (hasDerivAt_smoothTransition_edge (c + w1) w2 1 t).congr_of_eventuallyEq
    (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht)
      fun _ hs ↦ parallelogramFun_eq_edge2 c w1 w2 hs.1.le hs.2.le)

/-- The parallelogram loop's derivative on the open third edge `(1/2, 3/4)`. -/
theorem hasDerivAt_parallelogramFun_edge3 (c w1 w2 : ℂ) {t : ℝ}
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4)) :
    HasDerivAt (parallelogramFun c w1 w2)
      ((4 * deriv Real.smoothTransition (4 * t - 2) : ℝ) * (-w1)) t :=
  (hasDerivAt_smoothTransition_edge (c + w1 + w2) (-w1) 2 t).congr_of_eventuallyEq
    (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht)
      fun _ hs ↦ parallelogramFun_eq_edge3 c w1 w2 hs.1.le hs.2.le)

/-- The parallelogram loop's derivative on the open fourth edge `(3/4, 1)`. -/
theorem hasDerivAt_parallelogramFun_edge4 (c w1 w2 : ℂ) {t : ℝ} (ht : 3 / 4 < t) :
    HasDerivAt (parallelogramFun c w1 w2)
      ((4 * deriv Real.smoothTransition (4 * t - 3) : ℝ) * (-w2)) t :=
  (hasDerivAt_smoothTransition_edge (c + w2) (-w2) 3 t).congr_of_eventuallyEq
    (Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht)
      fun _ hs ↦ parallelogramFun_eq_edge4 c w1 w2 (le_of_lt hs))

/-- An edge integral of the parallelogram loop, over a parameter interval `[a, b]` of length
`1/4` on which the loop is `p + smoothTransition (4 * t - k) * v`, rewritten as an integral over
the gluing parameter `u ∈ [0, 1]`. -/
theorem integral_edge_eq (f : ℂ → ℂ) (γ : ℝ → ℂ) (p v : ℂ) {a b k : ℝ} (hab : a ≤ b)
    (ha : 4 * a - k = 0) (hb : 4 * b - k = 1)
    (hγ : ∀ t ∈ Set.Ioo a b, γ t = p + (Real.smoothTransition (4 * t - k) : ℂ) * v ∧
      HasDerivAt γ ((4 * deriv Real.smoothTransition (4 * t - k) : ℝ) * v) t) :
    (∫ t in a..b, f (γ t) * deriv γ t) =
      ∫ u in (0 : ℝ)..1, f (p + (Real.smoothTransition u : ℂ) * v) *
        ((deriv Real.smoothTransition u : ℝ) : ℂ) * v := by
  set g : ℝ → ℂ := fun u ↦ f (p + (Real.smoothTransition u : ℂ) * v) *
    ((deriv Real.smoothTransition u : ℝ) : ℂ) * v
  have hcong : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → f (γ t) * deriv γ t = (4 : ℝ) • g (4 * t + -k) := by
    rw [Set.uIoc_of_le hab, ae_iff]
    refine measure_mono_null (t := {b}) (fun t ht ↦ ?_) Real.volume_singleton
    simp only [Set.mem_ofPred_eq, not_imp] at ht
    by_contra hne
    obtain ⟨hγt, hdt⟩ := hγ t ⟨ht.1.1, lt_of_le_of_ne ht.1.2 hne⟩
    refine ht.2 ?_
    rw [hγt, hdt.deriv, ← sub_eq_add_neg, Complex.real_smul]
    push_cast
    ring
  rw [intervalIntegral.integral_congr_ae hcong, intervalIntegral.integral_smul,
    intervalIntegral.smul_integral_comp_mul_add g, ← sub_eq_add_neg, ← sub_eq_add_neg, ha, hb]

/-- The first edge's contribution to the boundary integral of `f`, rewritten as an integral
over the gluing parameter `v ∈ [0, 1]`. -/
theorem integral_edge1_eq (c w1 w2 : ℂ) (f : ℂ → ℂ) :
    (∫ t in (0:ℝ)..(1/4), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) =
      ∫ v in (0:ℝ)..1, f (c + (Real.smoothTransition v : ℂ) * w1) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * w1 :=
  integral_edge_eq f _ c w1 (k := 0) (by norm_num) (by norm_num) (by norm_num) fun t ht ↦
    ⟨by simpa using parallelogramFun_eq_edge1 c w1 w2 ht.2.le,
      by simpa using hasDerivAt_parallelogramFun_edge1 c w1 w2 ht.2⟩

/-- The second edge's contribution to the boundary integral of `f`, rewritten as an integral
over the gluing parameter `v ∈ [0, 1]`. -/
theorem integral_edge2_eq (c w1 w2 : ℂ) (f : ℂ → ℂ) :
    (∫ t in (1/4:ℝ)..(1/2), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) =
      ∫ v in (0:ℝ)..1, f (c + w1 + (Real.smoothTransition v : ℂ) * (w2)) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * (w2) :=
  integral_edge_eq f _ (c + w1) w2 (k := 1) (by norm_num) (by norm_num) (by norm_num) fun t ht ↦
    ⟨parallelogramFun_eq_edge2 c w1 w2 ht.1.le ht.2.le,
      hasDerivAt_parallelogramFun_edge2 c w1 w2 ht⟩

/-- The third edge's contribution to the boundary integral of `f`, rewritten as an integral
over the gluing parameter `v ∈ [0, 1]`. -/
theorem integral_edge3_eq (c w1 w2 : ℂ) (f : ℂ → ℂ) :
    (∫ t in (1/2:ℝ)..(3/4), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) =
      ∫ v in (0:ℝ)..1, f (c + w1 + w2 + (Real.smoothTransition v : ℂ) * (-w1)) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * (-w1) :=
  integral_edge_eq f _ (c + w1 + w2) (-w1) (k := 2) (by norm_num) (by norm_num) (by norm_num)
    fun t ht ↦ ⟨parallelogramFun_eq_edge3 c w1 w2 ht.1.le ht.2.le,
      hasDerivAt_parallelogramFun_edge3 c w1 w2 ht⟩

/-- The fourth edge's contribution to the boundary integral of `f`, rewritten as an integral
over the gluing parameter `v ∈ [0, 1]`. -/
theorem integral_edge4_eq (c w1 w2 : ℂ) (f : ℂ → ℂ) :
    (∫ t in (3/4:ℝ)..(1), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) =
      ∫ v in (0:ℝ)..1, f (c + w2 + (Real.smoothTransition v : ℂ) * (-w2)) *
        ((deriv Real.smoothTransition v : ℝ) : ℂ) * (-w2) :=
  integral_edge_eq f _ (c + w2) (-w2) (k := 3) (by norm_num) (by norm_num) (by norm_num)
    fun t ht ↦ ⟨parallelogramFun_eq_edge4 c w1 w2 ht.1.le,
      hasDerivAt_parallelogramFun_edge4 c w1 w2 ht.1⟩

/-- **Opposite edges cancel.** For `f` periodic with period `w`, the edge from `p` in direction
`v` and the edge from `q = p + v + w` in direction `-v` contribute opposite integrals. -/
theorem integral_edge_add_integral_opposite_edge_eq_zero {f : ℂ → ℂ} {w : ℂ}
    (hper : Function.Periodic f w) (p v q : ℂ) (hq : q = p + v + w) :
    (∫ u in (0:ℝ)..1, f (p + (Real.smoothTransition u : ℂ) * v) *
        ((deriv Real.smoothTransition u : ℝ) : ℂ) * v) +
      (∫ u in (0:ℝ)..1, f (q + (Real.smoothTransition u : ℂ) * (-v)) *
        ((deriv Real.smoothTransition u : ℝ) : ℂ) * (-v)) = 0 := by
  have hrev := intervalIntegral.integral_comp_sub_left
    (fun u ↦ f (q + (Real.smoothTransition u : ℂ) * (-v)) *
      ((deriv Real.smoothTransition u : ℝ) : ℂ) * (-v)) (1 : ℝ) (a := 0) (b := 1)
  simp only [sub_self, sub_zero] at hrev
  have hsecond : (∫ u in (0 : ℝ)..1, f (q + (Real.smoothTransition (1 - u) : ℂ) * (-v)) *
      ((deriv Real.smoothTransition (1 - u) : ℝ) : ℂ) * (-v)) =
      ∫ u in (0 : ℝ)..1, -(f (p + (Real.smoothTransition u : ℂ) * v) *
        ((deriv Real.smoothTransition u : ℝ) : ℂ) * v) := by
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    simp only [smoothTransition_one_sub, deriv_smoothTransition_one_sub, hq]
    rw [show p + v + w + (((1 : ℝ) - Real.smoothTransition u : ℝ) : ℂ) * (-v) =
      (p + (Real.smoothTransition u : ℂ) * v) + w by push_cast; ring, hper]
    ring
  rw [← hrev, hsecond, intervalIntegral.integral_neg, add_neg_cancel]

/-- Edges 1 and 3, offset by periodicity in `w2`, cancel exactly. -/
theorem integral_edge1_add_edge3_eq_zero (c w1 w2 : ℂ) {f : ℂ → ℂ}
    (hper2 : Function.Periodic f w2) :
    (∫ t in (0:ℝ)..(1/4), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) +
    (∫ t in (1/2:ℝ)..(3/4), f (parallelogramFun c w1 w2 t) *
      deriv (parallelogramFun c w1 w2) t) = 0 := by
  rw [integral_edge1_eq, integral_edge3_eq]
  exact integral_edge_add_integral_opposite_edge_eq_zero hper2 c w1 _ rfl

/-- Edges 2 and 4, offset by periodicity in `w1`, cancel exactly. -/
theorem integral_edge2_add_edge4_eq_zero (c w1 w2 : ℂ) {f : ℂ → ℂ}
    (hper1 : Function.Periodic f w1) :
    (∫ t in (1/4:ℝ)..(1/2), f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t) +
    (∫ t in (3/4:ℝ)..1, f (parallelogramFun c w1 w2 t) *
      deriv (parallelogramFun c w1 w2) t) = 0 := by
  rw [integral_edge2_eq, integral_edge4_eq]
  exact integral_edge_add_integral_opposite_edge_eq_zero hper1.neg (c + w1) w2 _ (by ring)

/-- **The boundary integral of a doubly periodic function over a period parallelogram
vanishes.** Opposite edges cancel exactly: each is the periodic translate of the other,
traversed in the opposite direction. -/
theorem curveIntegral_toSpanSingleton_parallelogramLoop_eq_zero {c w1 w2 : ℂ} {f : ℂ → ℂ}
    (hf : Continuous f) (hper1 : Function.Periodic f w1) (hper2 : Function.Periodic f w2) :
    curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z))
      (parallelogramLoop c w1 w2) = 0 := by
  have hCIeq : curveIntegral (fun z ↦ ContinuousLinearMap.toSpanSingleton ℂ (f z))
      (parallelogramLoop c w1 w2) =
      ∫ t in (0:ℝ)..1, f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t := by
    rw [curveIntegral_eq_intervalIntegral_deriv, parallelogramLoop_extend]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    exact intervalIntegral.integral_congr (fun t _ ↦ mul_comm _ _)
  rw [hCIeq]
  have hcontg : Continuous (fun t ↦ f (parallelogramFun c w1 w2 t) *
      deriv (parallelogramFun c w1 w2) t) :=
    (hf.comp (continuous_parallelogramFun c w1 w2)).mul
      ((contDiff_parallelogramFun c w1 w2).iterate_deriv 1).continuous
  have hInt : ∀ a b : ℝ, IntervalIntegrable
      (fun t ↦ f (parallelogramFun c w1 w2 t) * deriv (parallelogramFun c w1 w2) t)
      MeasureTheory.volume a b := fun a b ↦ hcontg.intervalIntegrable a b
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
