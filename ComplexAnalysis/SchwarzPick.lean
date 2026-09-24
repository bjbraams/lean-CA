/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.DiscMobius
public import Mathlib.Analysis.Complex.Schwarz

/-!
# The Schwarz–Pick lemma and the hyperbolic metric of the disc

For a holomorphic self-map `f` of the unit disc, the Schwarz–Pick lemma states that `f`
contracts the pseudo-hyperbolic distance `‖discMobius a z‖`, and contracts the corresponding
infinitesimal (derivative) form `‖f' a‖ / (1 - ‖f a‖ ^ 2) ≤ 1 / (1 - ‖a‖ ^ 2)`.

The proof composes `f` on either side with disc Möbius transformations to reduce to the
classical Schwarz lemma at the origin (Mathlib's `Complex.norm_le_norm_of_mapsTo_ball` and
`Complex.norm_deriv_le_one_of_mapsTo_ball`): for `a` in the disc, `h z := discMobius (f a)
(f (discMobius (-a) z))` sends the disc into the disc with `h 0 = 0`.

## Main results

* `Complex.norm_discMobius_apply_apply_le`: **the Schwarz–Pick lemma**, distance form.
* `Complex.norm_deriv_div_one_sub_normSq_le`: **the Schwarz–Pick lemma**, derivative form.

## References

* B. Simon, *Basic Complex Analysis*, Section 7.4.
* T. Gamelin, *Complex Analysis*, Chapter IX, Section 3.
-/

public noncomputable section

open Set Metric Filter ComplexConjugate

namespace Complex

variable {f : ℂ → ℂ}

/-- `discMobius (-a) 0 = a`. -/
theorem discMobius_neg_apply_zero (a : ℂ) : discMobius (-a) 0 = a := by
  rw [discMobius_zero_right, neg_neg]

/-- The auxiliary self-map of the disc used in the proof of the Schwarz–Pick lemma. -/
def schwarzPickAux (f : ℂ → ℂ) (a z : ℂ) : ℂ := discMobius (f a) (f (discMobius (-a) z))

/-- The Schwarz–Pick auxiliary map fixes the origin. -/
theorem schwarzPickAux_zero {a : ℂ} :
    schwarzPickAux f a 0 = 0 := by
  simp only [schwarzPickAux, discMobius_neg_apply_zero]
  exact discMobius_self (f a)

/-- Conjugating a self-map of the unit disc by the disc Möbius maps gives another self-map of the
disc. -/
theorem mapsTo_schwarzPickAux (hmaps : MapsTo f (ball 0 1) (ball 0 1)) {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (schwarzPickAux f a) (ball 0 1) (ball 0 1) := by
  have hna : ‖-a‖ < 1 := by simpa using ha
  have hfa : f a ∈ ball (0:ℂ) 1 := hmaps (mem_ball_zero_iff.mpr ha)
  intro z hz
  exact mapsTo_discMobius_ball (mem_ball_zero_iff.mp hfa) (hmaps (mapsTo_discMobius_ball hna hz))

/-- The Schwarz–Pick auxiliary map of a holomorphic self-map of the unit disc is holomorphic there. -/
theorem differentiableOn_schwarzPickAux (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1)) {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (schwarzPickAux f a) (ball 0 1) := by
  have hna : ‖-a‖ < 1 := by simpa using ha
  have hfa : f a ∈ ball (0:ℂ) 1 := hmaps (mem_ball_zero_iff.mpr ha)
  have h1 : DifferentiableOn ℂ (discMobius (-a)) (ball 0 1) :=
    differentiableOn_discMobius_ball hna
  have h2 : DifferentiableOn ℂ (fun z => f (discMobius (-a) z)) (ball 0 1) :=
    hf.comp h1 (mapsTo_discMobius_ball hna)
  have h3 : DifferentiableOn ℂ (discMobius (f a)) (ball 0 1) :=
    differentiableOn_discMobius_ball (mem_ball_zero_iff.mp hfa)
  exact h3.comp h2 (fun z hz => mapsTo_discMobius_ball hna hz |> fun hz' => hmaps hz')

/-- **The Schwarz–Pick lemma**, distance form. A holomorphic self-map of the disc contracts the
pseudo-hyperbolic distance `‖discMobius a z‖`. -/
theorem norm_discMobius_apply_apply_le (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1)) {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖discMobius (f a) (f w)‖ ≤ ‖discMobius a w‖ := by
  set z : ℂ := discMobius a w with hz_def
  have hz : ‖z‖ < 1 := norm_discMobius_lt_one ha hw
  have hφz : discMobius (-a) z = w := discMobius_neg_discMobius ha hw.le
  have hhz : schwarzPickAux f a z = discMobius (f a) (f w) := by
    simp only [schwarzPickAux, hφz]
  rw [← hhz]
  exact norm_le_norm_of_mapsTo_ball (differentiableOn_schwarzPickAux hf hmaps ha)
    ((mapsTo_schwarzPickAux hmaps ha).mono_right ball_subset_closedBall) schwarzPickAux_zero hz

/-- **The Schwarz–Pick lemma**, derivative form. A holomorphic self-map of the disc contracts
the hyperbolic metric infinitesimally. -/
theorem norm_deriv_div_one_sub_normSq_le (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : MapsTo f (ball 0 1) (ball 0 1)) {a : ℂ} (ha : ‖a‖ < 1) :
    ‖deriv f a‖ / (1 - normSq (f a)) ≤ 1 / (1 - normSq a) := by
  have hna : ‖-a‖ < 1 := by simpa using ha
  have hfa : ‖f a‖ < 1 := mem_ball_zero_iff.mp (hmaps (mem_ball_zero_iff.mpr ha))
  -- the three derivatives being composed
  have hd1 : HasDerivAt (discMobius (-a)) (1 - normSq a) 0 := by
    have h := hasDerivAt_discMobius (a := -a) (z := (0:ℂ))
      (one_sub_conj_mul_ne_zero hna (by norm_num))
    have hval : ((1:ℂ) - normSq (-a)) / (1 - conj (-a) * 0) ^ 2 = 1 - normSq a := by simp
    rwa [hval] at h
  have hfan : DifferentiableAt ℂ f a :=
    hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ha))
  have hd3 : HasDerivAt f (deriv f a) a := hfan.hasDerivAt
  have hd23 : HasDerivAt (fun z => f (discMobius (-a) z)) (deriv f a * (1 - normSq a)) 0 :=
    hd3.comp_of_eq 0 hd1 (discMobius_neg_apply_zero a).symm
  have hd2 : HasDerivAt (discMobius (f a)) ((1 - (normSq (f a) : ℂ))⁻¹) (f a) := by
    have hne : (1:ℂ) - conj (f a) * (f a) ≠ 0 := one_sub_conj_mul_ne_zero hfa hfa.le
    have h := hasDerivAt_discMobius (a := f a) (z := f a) hne
    have hval : ((1:ℂ) - normSq (f a)) / (1 - conj (f a) * (f a)) ^ 2
        = (1 - (normSq (f a) : ℂ))⁻¹ := by
      have hc : (1:ℂ) - conj (f a) * f a = 1 - normSq (f a) := by
        rw [conj_mul', normSq_eq_norm_sq]; push_cast; ring
      have hne' : (1:ℂ) - normSq (f a) ≠ 0 := by rw [← hc]; exact hne
      rw [hc, sq]
      field_simp
    rwa [hval] at h
  have hcomp' : HasDerivAt (discMobius (f a) ∘ fun z => f (discMobius (-a) z))
      ((1 - (normSq (f a) : ℂ))⁻¹ * (deriv f a * (1 - normSq a))) 0 :=
    hd2.comp_of_eq 0 hd23 (congrArg f (discMobius_neg_apply_zero a).symm)
  have hcomp : HasDerivAt (schwarzPickAux f a)
      ((1 - (normSq (f a) : ℂ))⁻¹ * (deriv f a * (1 - normSq a))) 0 := by
    have heqfun : schwarzPickAux f a = discMobius (f a) ∘ fun z => f (discMobius (-a) z) := rfl
    rw [heqfun]; exact hcomp'
  have hmaps' : MapsTo (schwarzPickAux f a) (ball 0 1) (closedBall (schwarzPickAux f a 0) 1) := by
    rw [schwarzPickAux_zero]
    exact (mapsTo_schwarzPickAux hmaps ha).mono_right ball_subset_closedBall
  have hb : ‖deriv (schwarzPickAux f a) 0‖ ≤ 1 :=
    norm_deriv_le_one_of_mapsTo_ball (differentiableOn_schwarzPickAux hf hmaps ha) hmaps' one_pos
  have hnormSqa : normSq a < 1 := by
    rw [normSq_eq_norm_sq]; exact pow_lt_one₀ (norm_nonneg a) ha two_ne_zero
  have hnormSqfa : normSq (f a) < 1 := by
    rw [normSq_eq_norm_sq]; exact pow_lt_one₀ (norm_nonneg (f a)) hfa two_ne_zero
  have hval : ‖(1 - (normSq (f a) : ℂ))⁻¹ * (deriv f a * (1 - normSq a))‖
      = ‖deriv f a‖ * (1 - normSq a) / (1 - normSq (f a)) := by
    rw [norm_mul, norm_inv, norm_mul]
    have h1 : ‖(1 - (normSq (f a) : ℂ))‖ = 1 - normSq (f a) := by
      rw [show (1 - (normSq (f a) : ℂ)) = ((1 - normSq (f a) : ℝ) : ℂ) by push_cast; ring]
      exact Complex.norm_of_nonneg (by linarith)
    have h2 : ‖(1 - (normSq a : ℂ))‖ = 1 - normSq a := by
      rw [show (1 - (normSq a : ℂ)) = ((1 - normSq a : ℝ) : ℂ) by push_cast; ring]
      exact Complex.norm_of_nonneg (by linarith)
    rw [h1, h2]
    ring
  rw [hcomp.deriv, hval] at hb
  rw [div_le_one (by linarith)] at hb
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hb]

end Complex

end
