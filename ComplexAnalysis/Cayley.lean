/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.DiscAutomorphism

/-!
# The Cayley transform and automorphisms of the half-plane

The Cayley transform `z ↦ (z - I) / (z + I)` maps the upper half-plane `{z | 0 < z.im}`
holomorphically and bijectively onto the unit disc, with inverse `w ↦ I * (1 + w) / (1 - w)`.
Conjugating by it, every holomorphic automorphism of the upper half-plane is of the form
`cayleyInv ∘ (c * φ_a) ∘ cayley` with `‖c‖ = 1` and `‖a‖ < 1`.

## Main definitions

* `Complex.cayley`, `Complex.cayleyInv`.

## Main results

* `Complex.norm_cayley_lt_one`, `Complex.im_cayleyInv_pos`, `Complex.cayleyInv_cayley`,
  `Complex.cayley_cayleyInv`, `Complex.cayley_image_upperHalfPlane`.
* `Complex.exists_eqOn_cayleyInv_mul_discMobius_cayley`: automorphisms of the half-plane.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Section III.3.
* T. W. Gamelin, *Complex Analysis*, Section IX.2.
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open scoped Topology ComplexConjugate

namespace Complex

/-- The Cayley transform `z ↦ (z - I) / (z + I)`. -/
def cayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse Cayley transform `w ↦ I * (1 + w) / (1 - w)`. -/
def cayleyInv (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

/-- The upper half-plane as a subset of `ℂ`. -/
def upperHalfPlaneSet : Set ℂ := {z | 0 < z.im}

variable {z w : ℂ}

/-- The upper half-plane is open. -/
theorem isOpen_upperHalfPlaneSet : IsOpen upperHalfPlaneSet :=
  isOpen_lt continuous_const continuous_im

/-- The denominator `z + I` of the Cayley transform does not vanish in the upper half-plane. -/
theorem add_I_ne_zero (hz : 0 < z.im) : z + I ≠ 0 := by
  intro h
  have := congrArg im h
  simp at this
  linarith

/-- The squared norms of `z + I` and `z - I` differ by four times the imaginary part of `z`. -/
theorem normSq_add_I_sub_normSq_sub_I (z : ℂ) : normSq (z + I) - normSq (z - I) = 4 * z.im := by
  simp only [normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
  ring

/-- The Cayley transform maps the upper half-plane into the unit disc. -/
theorem norm_cayley_lt_one (hz : 0 < z.im) : ‖cayley z‖ < 1 := by
  have hd := add_I_ne_zero hz
  rw [cayley, norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have h := normSq_add_I_sub_normSq_sub_I z
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h
  have : ‖z - I‖ ^ 2 < ‖z + I‖ ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

/-- The Cayley transform never takes the value one on the upper half-plane. -/
theorem cayley_ne_one (hz : 0 < z.im) : cayley z ≠ 1 := fun h => by
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
  have h1 : HasDerivAt (fun z => z - I) 1 z := (hasDerivAt_id z).sub_const I
  have h2 : HasDerivAt (fun z => z + I) 1 z := (hasDerivAt_id z).add_const I
  have := h1.div h2 hz
  convert this using 1
  · rfl
  · ring

/-- The Cayley transform is holomorphic on the upper half-plane. -/
theorem differentiableOn_cayley : DifferentiableOn ℂ cayley upperHalfPlaneSet := fun _ hz =>
  (hasDerivAt_cayley (add_I_ne_zero hz)).differentiableAt.differentiableWithinAt

/-- Away from its pole, the inverse Cayley transform has derivative `2 * I / (1 - w) ^ 2`. -/
theorem hasDerivAt_cayleyInv (hw : 1 - w ≠ 0) : HasDerivAt cayleyInv (2 * I / (1 - w) ^ 2) w := by
  have h1 : HasDerivAt (fun w => I * (1 + w)) (I * 1) w :=
    ((hasDerivAt_id w).const_add 1).const_mul I
  have h2 : HasDerivAt (fun w => 1 - w) (-1) w := (hasDerivAt_id w).const_sub 1
  have := h1.div h2 hw
  convert this using 1
  · rfl
  · ring

/-- The inverse Cayley transform is holomorphic on the open unit disc. -/
theorem differentiableOn_cayleyInv : DifferentiableOn ℂ cayleyInv (ball 0 1) := fun w hw => by
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [mem_ball_zero_iff, this, norm_one] at hw
    exact lt_irrefl _ hw
  exact (hasDerivAt_cayleyInv hw1).differentiableAt.differentiableWithinAt

/-- The Cayley transform maps the upper half-plane into the open unit disc. -/
theorem mapsTo_cayley : MapsTo cayley upperHalfPlaneSet (ball 0 1) := fun _ hz =>
  mem_ball_zero_iff.mpr (norm_cayley_lt_one hz)

/-- The inverse Cayley transform maps the open unit disc into the upper half-plane. -/
theorem mapsTo_cayleyInv : MapsTo cayleyInv (ball 0 1) upperHalfPlaneSet := fun _ hw =>
  im_cayleyInv_pos (mem_ball_zero_iff.mp hw)

/-- The Cayley transform is injective on the upper half-plane. -/
theorem cayley_injOn : InjOn cayley upperHalfPlaneSet := fun z hz w hw h => by
  rw [← cayleyInv_cayley hz, h, cayleyInv_cayley hw]

/-- The Cayley transform maps the upper half-plane onto the unit disc. -/
theorem cayley_image_upperHalfPlane : cayley '' upperHalfPlaneSet = ball 0 1 := by
  refine Subset.antisymm mapsTo_cayley.image_subset fun w hw => ?_
  have hw1 : w ≠ 1 := fun h => by
    rw [mem_ball_zero_iff, h, norm_one] at hw
    exact lt_irrefl _ hw
  exact ⟨cayleyInv w, mapsTo_cayleyInv hw, cayley_cayleyInv hw1⟩

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
      EqOn f (fun z => cayleyInv (c * discMobius a (cayley z))) upperHalfPlaneSet := by
  set F : ℂ → ℂ := fun w => cayley (f (cayleyInv w)) with hF_def
  set G : ℂ → ℂ := fun w => cayley (g (cayleyInv w)) with hG_def
  have hFd : DifferentiableOn ℂ F (ball 0 1) :=
    differentiableOn_cayley.comp (hf.comp differentiableOn_cayleyInv mapsTo_cayleyInv)
      (hfm.comp mapsTo_cayleyInv)
  have hGd : DifferentiableOn ℂ G (ball 0 1) :=
    differentiableOn_cayley.comp (hg.comp differentiableOn_cayleyInv mapsTo_cayleyInv)
      (hgm.comp mapsTo_cayleyInv)
  have hFm : MapsTo F (ball 0 1) (ball 0 1) := fun w hw =>
    mapsTo_cayley (hfm (mapsTo_cayleyInv hw))
  have hGm : MapsTo G (ball 0 1) (ball 0 1) := fun w hw =>
    mapsTo_cayley (hgm (mapsTo_cayleyInv hw))
  have hGF : ∀ w ∈ ball 0 1, G (F w) = w := by
    intro w hw
    have hw1 : w ≠ 1 := fun h => by
      rw [mem_ball_zero_iff, h, norm_one] at hw
      exact lt_irrefl _ hw
    change cayley (g (cayleyInv (cayley (f (cayleyInv w))))) = w
    rw [cayleyInv_cayley (hfm (mapsTo_cayleyInv hw)), hgf _ (mapsTo_cayleyInv hw),
      cayley_cayleyInv hw1]
  have hFG : ∀ w ∈ ball 0 1, F (G w) = w := by
    intro w hw
    have hw1 : w ≠ 1 := fun h => by
      rw [mem_ball_zero_iff, h, norm_one] at hw
      exact lt_irrefl _ hw
    change cayley (f (cayleyInv (cayley (g (cayleyInv w))))) = w
    rw [cayleyInv_cayley (hgm (mapsTo_cayleyInv hw)), hfg _ (mapsTo_cayleyInv hw),
      cayley_cayleyInv hw1]
  obtain ⟨c, a, hc, ha, hFeq⟩ := exists_eqOn_mul_discMobius_of_leftInverse hFd hFm hGd hGm hGF hFG
  refine ⟨c, a, hc, ha, fun z hz => ?_⟩
  have h1 : f z = cayleyInv (F (cayley z)) := by
    change f z = cayleyInv (cayley (f (cayleyInv (cayley z))))
    rw [cayleyInv_cayley hz, cayleyInv_cayley (hfm hz)]
  rw [h1, hFeq (mapsTo_cayley hz)]

end Complex

end
