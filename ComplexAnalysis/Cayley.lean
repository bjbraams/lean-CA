/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.DiscAutomorphism
public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# The Cayley transform and automorphisms of the half-plane

The Cayley transform `z ↦ (z - I) / (z + I)` maps the upper half-plane `{z | 0 < z.im}`
holomorphically and bijectively onto the unit disc, with inverse `w ↦ I * (1 + w) / (1 - w)`.
Conjugating by it, every holomorphic automorphism of the upper half-plane is of the form
`cayleyInv ∘ (c * φ_a) ∘ cayley` with `‖c‖ = 1` and `‖a‖ < 1`, and hence a real Möbius map
`z ↦ (a * z + b) / (c * z + d)` with `a * d - b * c > 0`.

The upper half-plane is Mathlib's `UpperHalfPlane.upperHalfPlaneSet`. The mapping properties of
the Cayley transform are imported from the Tau Ceti contributors'
`TauCeti.Analysis.Complex.UpperHalfPlane.Cayley`.

## Main definitions

* `Complex.cayley`, `Complex.cayleyInv`.

## Main results

* `Complex.norm_cayley_lt_one`, `Complex.im_cayleyInv_pos`, `Complex.cayleyInv_cayley`,
  `Complex.cayley_cayleyInv`, `Complex.cayley_image_upperHalfPlane`.
* `Complex.exists_eqOn_cayleyInv_mul_discMobius_cayley`: automorphisms of the half-plane, in
  Cayley-conjugated form.
* `Complex.exists_eqOn_real_mobius_of_leftInverse`: automorphisms of the half-plane are real
  Möbius maps.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Section III.3.
* T. W. Gamelin, *Complex Analysis*, Section IX.2.
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open UpperHalfPlane (upperHalfPlaneSet isOpen_upperHalfPlaneSet)
open scoped Topology ComplexConjugate

namespace Complex

/-- The Cayley transform `z ↦ (z - I) / (z + I)`. -/
def cayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse Cayley transform `w ↦ I * (1 + w) / (1 - w)`. -/
def cayleyInv (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

variable {z w : ℂ}

/-- The denominator `z + I` of the Cayley transform does not vanish in the upper half-plane. -/
theorem add_I_ne_zero (hz : 0 < z.im) : z + I ≠ 0 :=
  TauCeti.add_I_ne_zero_of_im_nonneg hz.le

/-- The Cayley transform maps the upper half-plane into the unit disc. -/
theorem norm_cayley_lt_one (hz : 0 < z.im) : ‖cayley z‖ < 1 :=
  (TauCeti.norm_sub_I_div_add_I_lt_one_iff (add_I_ne_zero hz)).mpr hz

/-- The Cayley transform never takes the value one on the upper half-plane. -/
theorem cayley_ne_one (hz : 0 < z.im) : cayley z ≠ 1 := fun h ↦ by
  have := norm_cayley_lt_one hz
  rw [h, norm_one] at this
  exact lt_irrefl _ this

/-- The imaginary part of the inverse Cayley transform is the disc defect `1 - normSq w` divided by
`normSq (1 - w)`. -/
theorem im_cayleyInv (w : ℂ) : (cayleyInv w).im = (1 - normSq w) / normSq (1 - w) := by
  rw [cayleyInv, mul_div_assoc, I_mul_im, div_re, normSq_apply w]
  simp only [add_re, sub_re, add_im, sub_im, one_re, one_im]
  ring

/-- The inverse Cayley transform maps the unit disc into the upper half-plane. -/
theorem im_cayleyInv_pos (hw : ‖w‖ < 1) : 0 < (cayleyInv w).im := by
  rw [im_cayleyInv]
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw
    exact lt_irrefl _ hw
  refine div_pos ?_ (normSq_pos.mpr hw1)
  rw [normSq_eq_norm_sq]
  nlinarith [norm_nonneg w]

/-- The inverse Cayley transform recovers each point of the upper half-plane. -/
theorem cayleyInv_cayley (hz : 0 < z.im) : cayleyInv (cayley z) = z := by
  have hd := add_I_ne_zero hz
  have h1 : 1 - cayley z ≠ 0 := sub_ne_zero.mpr (cayley_ne_one hz).symm
  rw [cayleyInv, div_eq_iff h1, cayley]
  field_simp
  ring

/-- The Cayley transform recovers the input of its inverse whenever that input is not one. -/
theorem cayley_cayleyInv (hw : w ≠ 1) : cayley (cayleyInv w) = w := by
  have hw1 : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
  have h1 : cayleyInv w + I ≠ 0 := by
    rw [cayleyInv, div_add' _ _ _ hw1, div_ne_zero_iff]
    refine ⟨?_, hw1⟩
    intro h
    have : I * 2 = 0 := by linear_combination h
    simp at this
  rw [cayley, div_eq_iff h1, cayleyInv]
  field_simp
  ring

/-- Away from its pole, the Cayley transform has derivative `2 * I / (z + I) ^ 2`. -/
theorem hasDerivAt_cayley (hz : z + I ≠ 0) : HasDerivAt cayley (2 * I / (z + I) ^ 2) z := by
  have h1 : HasDerivAt (fun z ↦ z - I) 1 z := (hasDerivAt_id z).sub_const I
  have h2 : HasDerivAt (fun z ↦ z + I) 1 z := (hasDerivAt_id z).add_const I
  have := h1.div h2 hz
  convert this using 1
  · rfl
  · ring

/-- The Cayley transform is holomorphic on the upper half-plane. -/
theorem differentiableOn_cayley : DifferentiableOn ℂ cayley upperHalfPlaneSet :=
  TauCeti.differentiableOn_sub_I_div_add_I.mono fun _ hz ↦ add_I_ne_zero hz

/-- Away from its pole, the inverse Cayley transform has derivative `2 * I / (1 - w) ^ 2`. -/
theorem hasDerivAt_cayleyInv (hw : 1 - w ≠ 0) : HasDerivAt cayleyInv (2 * I / (1 - w) ^ 2) w := by
  have h1 : HasDerivAt (fun w ↦ I * (1 + w)) (I * 1) w :=
    ((hasDerivAt_id w).const_add 1).const_mul I
  have h2 : HasDerivAt (fun w ↦ 1 - w) (-1) w := (hasDerivAt_id w).const_sub 1
  have := h1.div h2 hw
  convert this using 1
  · rfl
  · ring

/-- The inverse Cayley transform is holomorphic on the open unit disc. -/
theorem differentiableOn_cayleyInv : DifferentiableOn ℂ cayleyInv (ball 0 1) := fun w hw ↦ by
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [mem_ball_zero_iff, this, norm_one] at hw
    exact lt_irrefl _ hw
  exact (hasDerivAt_cayleyInv hw1).differentiableAt.differentiableWithinAt

/-- The Cayley transform maps the upper half-plane into the open unit disc. -/
theorem mapsTo_cayley : MapsTo cayley upperHalfPlaneSet (ball 0 1) := fun _ hz ↦
  mem_ball_zero_iff.mpr (norm_cayley_lt_one hz)

/-- The inverse Cayley transform maps the open unit disc into the upper half-plane. -/
theorem mapsTo_cayleyInv : MapsTo cayleyInv (ball 0 1) upperHalfPlaneSet := fun _ hw ↦
  im_cayleyInv_pos (mem_ball_zero_iff.mp hw)

/-- The Cayley transform is injective on the upper half-plane. -/
theorem cayley_injOn : InjOn cayley upperHalfPlaneSet :=
  TauCeti.bijOn_sub_I_div_add_I_upperHalfPlaneSet.injOn

/-- The Cayley transform maps the upper half-plane onto the unit disc. -/
theorem cayley_image_upperHalfPlane : cayley '' upperHalfPlaneSet = ball 0 1 :=
  TauCeti.bijOn_sub_I_div_add_I_upperHalfPlaneSet.image_eq

/-- **Automorphisms of the upper half-plane.** A holomorphic bijection of the upper half-plane
with holomorphic inverse is the conjugate by the Cayley transform of a disc automorphism
`z ↦ c * φ_a z`. -/
theorem exists_eqOn_cayleyInv_mul_discMobius_cayley {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfm : MapsTo f upperHalfPlaneSet upperHalfPlaneSet)
    (hg : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgm : MapsTo g upperHalfPlaneSet upperHalfPlaneSet)
    (hgf : ∀ z ∈ upperHalfPlaneSet, g (f z) = z) (hfg : ∀ z ∈ upperHalfPlaneSet, f (g z) = z) :
    ∃ c a : ℂ, ‖c‖ = 1 ∧ ‖a‖ < 1 ∧
      EqOn f (fun z ↦ cayleyInv (c * discMobius a (cayley z))) upperHalfPlaneSet := by
  set F : ℂ → ℂ := fun w ↦ cayley (f (cayleyInv w))
  set G : ℂ → ℂ := fun w ↦ cayley (g (cayleyInv w))
  have hFd : DifferentiableOn ℂ F (ball 0 1) :=
    differentiableOn_cayley.comp (hf.comp differentiableOn_cayleyInv mapsTo_cayleyInv)
      (hfm.comp mapsTo_cayleyInv)
  have hGd : DifferentiableOn ℂ G (ball 0 1) :=
    differentiableOn_cayley.comp (hg.comp differentiableOn_cayleyInv mapsTo_cayleyInv)
      (hgm.comp mapsTo_cayleyInv)
  have hFm : MapsTo F (ball 0 1) (ball 0 1) := fun w hw ↦
    mapsTo_cayley (hfm (mapsTo_cayleyInv hw))
  have hGm : MapsTo G (ball 0 1) (ball 0 1) := fun w hw ↦
    mapsTo_cayley (hgm (mapsTo_cayleyInv hw))
  have hGF : ∀ w ∈ ball 0 1, G (F w) = w := by
    intro w hw
    have hw1 : w ≠ 1 := fun h ↦ by
      rw [mem_ball_zero_iff, h, norm_one] at hw
      exact lt_irrefl _ hw
    change cayley (g (cayleyInv (cayley (f (cayleyInv w))))) = w
    rw [cayleyInv_cayley (hfm (mapsTo_cayleyInv hw)), hgf _ (mapsTo_cayleyInv hw),
      cayley_cayleyInv hw1]
  have hFG : ∀ w ∈ ball 0 1, F (G w) = w := by
    intro w hw
    have hw1 : w ≠ 1 := fun h ↦ by
      rw [mem_ball_zero_iff, h, norm_one] at hw
      exact lt_irrefl _ hw
    change cayley (f (cayleyInv (cayley (g (cayleyInv w))))) = w
    rw [cayleyInv_cayley (hgm (mapsTo_cayleyInv hw)), hfg _ (mapsTo_cayleyInv hw),
      cayley_cayleyInv hw1]
  obtain ⟨c, a, hc, ha, hFeq⟩ := exists_eqOn_mul_discMobius_of_leftInverse hFd hFm hGd hGm hGF hFG
  refine ⟨c, a, hc, ha, fun z hz ↦ ?_⟩
  have h1 : f z = cayleyInv (F (cayley z)) := by
    change f z = cayleyInv (cayley (f (cayleyInv (cayley z))))
    rw [cayleyInv_cayley hz, cayleyInv_cayley (hfm hz)]
  rw [h1, hFeq (mapsTo_cayley hz)]

/-- **Automorphisms of the upper half-plane are real Möbius maps.** A holomorphic bijection of
the upper half-plane with holomorphic inverse is `z ↦ (a * z + b) / (c * z + d)` with real
coefficients and `a * d - b * c > 0`.

The coefficients come from the disc automorphism `u * φ_α` of
`Complex.exists_eqOn_cayleyInv_mul_discMobius_cayley`: with `s ^ 2 = u`, `‖s‖ = 1`, `p = s` and
`q = -s α`, they are `a = re p + re q`, `b = im p - im q`, `c = -(im p + im q)`, `d = re p - re q`,
and `a * d - b * c = 1 - ‖α‖ ^ 2`. -/
theorem exists_eqOn_real_mobius_of_leftInverse {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfm : MapsTo f upperHalfPlaneSet upperHalfPlaneSet)
    (hg : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgm : MapsTo g upperHalfPlaneSet upperHalfPlaneSet)
    (hgf : ∀ z ∈ upperHalfPlaneSet, g (f z) = z) (hfg : ∀ z ∈ upperHalfPlaneSet, f (g z) = z) :
    ∃ a b c d : ℝ, 0 < a * d - b * c ∧
      EqOn f (fun z ↦ (a * z + b) / (c * z + d)) upperHalfPlaneSet := by
  obtain ⟨u, α, hu, hα, hfeq⟩ :=
    exists_eqOn_cayleyInv_mul_discMobius_cayley hf hfm hg hgm hgf hfg
  -- a square root `s` of `u` on the unit circle, with `conj s = t`
  set s : ℂ := exp ((arg u / 2 : ℝ) * I)
  set t : ℂ := conj s
  have hs1 : ‖s‖ = 1 := norm_exp_ofReal_mul_I _
  have hst : s * t = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, hs1]; simp
  have hsu : s ^ 2 = u := by
    rw [← exp_nat_mul, ← mul_assoc]
    push_cast
    rw [show (2 : ℂ) * ((arg u : ℂ) / 2) = arg u by ring]
    simpa [hu] using norm_mul_exp_arg_mul_I u
  set q : ℂ := -(s * α)
  have hdet : 0 < (s.re + q.re) * (s.re - q.re) - (s.im - q.im) * -(s.im + q.im) := by
    have hq : normSq q = normSq α := by simp [q, normSq_eq_norm_sq, hs1]
    have hs' : normSq s = 1 := by rw [normSq_eq_norm_sq, hs1]; norm_num
    have hdet : (s.re + q.re) * (s.re - q.re) - (s.im - q.im) * -(s.im + q.im) =
        normSq s - normSq q := by simp only [normSq_apply]; ring
    rw [hdet, hs', hq, normSq_eq_norm_sq]
    nlinarith [norm_nonneg α]
  refine ⟨s.re + q.re, s.im - q.im, -(s.im + q.im), s.re - q.re, hdet, fun z hz ↦ ?_⟩
  · have hzI : z + I ≠ 0 := add_I_ne_zero hz
    set w := cayley z with hw
    have hw1 : ‖w‖ < 1 := norm_cayley_lt_one hz
    have hE' : 1 - conj α * w ≠ 0 := one_sub_conj_mul_ne_zero hα hw1.le
    set E := (z + I) - conj α * (z - I)
    set W := (z - I) - α * (z + I)
    have hE : E ≠ 0 := by
      have : E = (z + I) * (1 - conj α * w) := by
        simp only [E, w, cayley]; field_simp
      rw [this]; exact mul_ne_zero hzI hE'
    set v := u * discMobius α w
    have hv : v = s ^ 2 * W / E := by
      simp only [v, w, cayley, discMobius, hsu, E, W]
      field_simp
    have hv1 : 1 - v ≠ 0 := by
      have : ‖v‖ < 1 := by
        rw [norm_mul, hu, one_mul]; exact norm_discMobius_lt_one hα hw1
      intro h
      rw [show v = 1 by linear_combination -h, norm_one] at this
      exact lt_irrefl _ this
    have key : (-((s - t) + (q - conj q)) * z + I * (s + t - q - conj q)) *
        (I * (E + s ^ 2 * W)) = (I * (s + t + q + conj q) * z + ((s - t) - (q - conj q))) *
          (E - s ^ 2 * W) := by
      simp only [q, map_neg, map_mul, E, W]
      linear_combination
        s * (α * I + α * z + I - z) * (-(conj α) * I ^ 2 + 2 * conj α * I * z + conj α - I ^ 2 -
          2 * I * z + 1) * hst +
        (-α ^ 2 * I * s ^ 3 - α ^ 2 * s ^ 3 * z + 2 * α * conj α * s * z - 2 * α * I * s ^ 3 +
          conj α ^ 2 * I * t - conj α ^ 2 * t * z + 2 * conj α * I * t - I * s ^ 3 + I * t +
          s ^ 3 * z - 2 * s * z + t * z) * I_sq
    have hEW : E - s ^ 2 * W ≠ 0 := by
      intro h
      apply hv1
      rw [hv, ← sub_eq_zero.mp h, div_self hE, sub_self]
    have hD : (((-(s.im + q.im) : ℝ) : ℂ) * z + ((s.re - q.re : ℝ) : ℂ)) ≠ 0 := by
      intro h
      have him := congrArg im h
      have hre := congrArg re h
      simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_im, add_re,
        mul_re, sub_zero, zero_re] at him hre
      have hc : -(s.im + q.im) = 0 := by
        rcases mul_eq_zero.mp him with h' | h'
        · exact h'
        · exact absurd h' (ne_of_gt hz)
      rw [hc, zero_mul, zero_add] at hre
      rw [hc, hre] at hdet
      simp at hdet
    rw [hfeq hz]
    change cayleyInv v = _
    have ha : ((s.re + q.re : ℝ) : ℂ) = (s + t + q + conj q) / 2 := by
      push_cast; rw [re_eq_add_conj, re_eq_add_conj]; ring
    have hb : ((s.im - q.im : ℝ) : ℂ) = ((s - t) - (q - conj q)) / (2 * I) := by
      push_cast; rw [im_eq_sub_conj, im_eq_sub_conj]; ring
    have hc : ((-(s.im + q.im) : ℝ) : ℂ) = -((s - t) + (q - conj q)) / (2 * I) := by
      push_cast; rw [im_eq_sub_conj, im_eq_sub_conj]; ring
    have hd : ((s.re - q.re : ℝ) : ℂ) = (s + t - q - conj q) / 2 := by
      push_cast; rw [re_eq_add_conj, re_eq_add_conj]; ring
    rw [eq_div_iff hD, ha, hb, hc, hd, cayleyInv, hv]
    field_simp
    linear_combination key

end Complex

end
