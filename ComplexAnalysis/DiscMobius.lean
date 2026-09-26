/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Möbius transformations of the unit disc

The map `φ a z = (z - a) / (1 - conj a * z)` with `‖a‖ < 1` is a holomorphic bijection of the
unit disc onto itself, sending `a` to `0`, with inverse `φ (-a)`. It preserves the unit circle,
and its derivative is `(1 - ‖a‖²) / (1 - conj a * z)²`, so `φ a` has derivative `1 - ‖a‖²` at `0`
and `1 / (1 - ‖a‖²)` at `a`.

## Main definitions

* `Complex.discMobius a z`.

## Main results

* `Complex.norm_discMobius_lt_one`, `Complex.norm_discMobius_eq_one`: the disc and the circle
  are preserved.
* `Complex.discMobius_neg_discMobius`: `φ (-a)` inverts `φ a` on the closed disc.
* `Complex.hasDerivAt_discMobius`, `Complex.deriv_discMobius_zero`,
  `Complex.deriv_discMobius_self`: the derivative.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Section VI.2.
* T. W. Gamelin, *Complex Analysis*, Section IX.2.
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open scoped Topology ComplexConjugate

namespace Complex

/-- The disc Möbius transformation `φ a z = (z - a) / (1 - conj a * z)`.

The corresponding disk shift is formalized in Yury Kudryashov's Mathlib PR #33368, with the
parameter's sign reversed. See `CREDITS.md`. -/
def discMobius (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

variable {a z : ℂ}

/-- The denominator does not vanish for `‖a‖ < 1` and `‖z‖ ≤ 1`. -/
theorem one_sub_conj_mul_ne_zero (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) : 1 - conj a * z ≠ 0 := by
  intro h
  have h1 : conj a * z = 1 := by linear_combination -h
  have h2 : ‖a‖ * ‖z‖ = 1 := by rw [← norm_conj a, ← norm_mul, h1, norm_one]
  nlinarith [norm_nonneg a, norm_nonneg z]

/-- The basic identity `‖1 - conj a z‖² - ‖z - a‖² = (1 - ‖a‖²) (1 - ‖z‖²)`. -/
theorem normSq_one_sub_conj_mul_sub_normSq_sub (a z : ℂ) :
    normSq (1 - conj a * z) - normSq (z - a) = (1 - normSq a) * (1 - normSq z) := by
  have h : (1 - conj a * z) * conj (1 - conj a * z) - (z - a) * conj (z - a) =
      (1 - a * conj a) * (1 - z * conj z) := by
    simp only [map_sub, map_mul, map_one, conj_conj]
    ring
  rw [mul_conj, mul_conj, mul_conj, mul_conj] at h
  exact_mod_cast h

/-- The difference of the squared denominator and numerator norms of the disc Möbius map is the
product of the two disc defects. -/
theorem norm_one_sub_conj_mul_sq_sub_norm_sub_sq (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 - ‖z - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  have := normSq_one_sub_conj_mul_sub_normSq_sub a z
  simpa only [normSq_eq_norm_sq] using this

/-- The disc Möbius map sends its parameter to zero. -/
theorem discMobius_self (a : ℂ) : discMobius a a = 0 := by
  simp [discMobius]

/-- The disc Möbius map sends zero to the negative of its parameter. -/
@[simp] theorem discMobius_zero_right (a : ℂ) : discMobius a 0 = -a := by
  simp [discMobius]

/-- The disc Möbius map with parameter zero is the identity. -/
@[simp] theorem discMobius_zero_left (z : ℂ) : discMobius 0 z = z := by
  simp [discMobius]

/-- The norm of the disc Möbius map is the quotient of the numerator and denominator norms. -/
theorem norm_discMobius (a z : ℂ) : ‖discMobius a z‖ = ‖z - a‖ / ‖1 - conj a * z‖ := by
  rw [discMobius, norm_div]

/-- The disc Möbius transformation maps the open disc into itself. -/
theorem norm_discMobius_lt_one (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖discMobius a z‖ < 1 := by
  have hd := one_sub_conj_mul_ne_zero ha hz.le
  rw [norm_discMobius, div_lt_one (norm_pos_iff.mpr hd)]
  have hid := norm_one_sub_conj_mul_sq_sub_norm_sub_sq a z
  have hpos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    apply mul_pos <;> nlinarith [norm_nonneg a, norm_nonneg z]
  have : ‖z - a‖ ^ 2 < ‖1 - conj a * z‖ ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

/-- The disc Möbius transformation maps the unit circle into itself. -/
theorem norm_discMobius_eq_one (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) : ‖discMobius a z‖ = 1 := by
  have hd := one_sub_conj_mul_ne_zero ha hz.le
  rw [norm_discMobius, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hd)]
  have hid := norm_one_sub_conj_mul_sq_sub_norm_sub_sq a z
  rw [hz, one_pow, sub_self, mul_zero, sub_eq_zero] at hid
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hid).symm

/-- The disc Möbius transformation maps the closed disc into itself. -/
theorem norm_discMobius_le_one (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) : ‖discMobius a z‖ ≤ 1 := by
  rcases hz.lt_or_eq with hz | hz
  · exact (norm_discMobius_lt_one ha hz).le
  · exact (norm_discMobius_eq_one ha hz).le

/-- A disc Möbius map with parameter in the open unit disc maps that disc into itself. -/
theorem mapsTo_discMobius_ball (ha : ‖a‖ < 1) :
    MapsTo (discMobius a) (ball 0 1) (ball 0 1) := fun z hz ↦ by
  rw [mem_ball_zero_iff] at hz ⊢
  exact norm_discMobius_lt_one ha hz

/-- `φ (-a)` inverts `φ a` on the closed disc. -/
theorem discMobius_neg_discMobius (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    discMobius (-a) (discMobius a z) = z := by
  have hd := one_sub_conj_mul_ne_zero ha hz
  have hd' : 1 - conj (-a) * discMobius a z ≠ 0 :=
    one_sub_conj_mul_ne_zero (by simpa using ha) (norm_discMobius_le_one ha hz)
  have hna : 1 - a * conj a ≠ 0 := by
    rw [mul_conj, sub_ne_zero]
    intro h
    have h' : normSq a = 1 := by exact_mod_cast h.symm
    rw [normSq_eq_norm_sq] at h'
    nlinarith [norm_nonneg a]
  have hd2 : 1 - z * conj a ≠ 0 := by rwa [mul_comm]
  rw [discMobius, div_eq_iff hd', discMobius, map_neg]
  field_simp [hd, hd2]
  ring

/-- Where its denominator is nonzero, the disc Möbius map vanishes exactly at its parameter. -/
theorem discMobius_eq_zero_iff (h : 1 - conj a * z ≠ 0) : discMobius a z = 0 ↔ z = a := by
  rw [discMobius, div_eq_zero_iff, or_iff_left h, sub_eq_zero]

/-- The disc Möbius transformation is injective on the closed disc. -/
theorem discMobius_injOn (ha : ‖a‖ < 1) : InjOn (discMobius a) (closedBall 0 1) := by
  intro z hz w hw hzw
  rw [mem_closedBall_zero_iff] at hz hw
  rw [← discMobius_neg_discMobius ha hz, hzw, discMobius_neg_discMobius ha hw]

/-- The disc Möbius transformation maps the open disc onto itself. -/
theorem discMobius_image_ball (ha : ‖a‖ < 1) : discMobius a '' ball 0 1 = ball 0 1 := by
  refine Subset.antisymm (mapsTo_discMobius_ball ha).image_subset fun w hw ↦ ?_
  have hna : ‖-a‖ < 1 := by simpa using ha
  refine ⟨discMobius (-a) w, mapsTo_discMobius_ball hna hw, ?_⟩
  have := discMobius_neg_discMobius hna (mem_ball_zero_iff.mp hw).le
  rwa [neg_neg] at this

/-- The derivative of the disc Möbius transformation. -/
theorem hasDerivAt_discMobius (h : 1 - conj a * z ≠ 0) :
    HasDerivAt (discMobius a) ((1 - normSq a) / (1 - conj a * z) ^ 2) z := by
  have h1 : HasDerivAt (fun z ↦ z - a) 1 z := (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun z ↦ 1 - conj a * z) (-(conj a * 1)) z :=
    ((hasDerivAt_id z).const_mul (conj a)).const_sub 1
  have := h1.div h2 h
  convert this using 1
  · rfl
  · rw [← mul_conj]
    ring

/-- The disc Möbius map is complex differentiable wherever its denominator is nonzero. -/
theorem differentiableAt_discMobius (h : 1 - conj a * z ≠ 0) :
    DifferentiableAt ℂ (discMobius a) z :=
  (hasDerivAt_discMobius h).differentiableAt

/-- A disc Möbius map with parameter in the open unit disc is differentiable on the closed unit
disc. -/
theorem differentiableOn_discMobius_closedBall (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (discMobius a) (closedBall 0 1) := fun _ hz ↦
  (differentiableAt_discMobius (one_sub_conj_mul_ne_zero ha (mem_closedBall_zero_iff.mp hz)))
    |>.differentiableWithinAt

/-- A disc Möbius map with parameter in the open unit disc is holomorphic on that disc. -/
theorem differentiableOn_discMobius_ball (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (discMobius a) (ball 0 1) :=
  (differentiableOn_discMobius_closedBall ha).mono ball_subset_closedBall

/-- Where the denominator is nonzero, the derivative of the disc Möbius map is its parameter's disc
defect divided by the squared denominator. -/
theorem deriv_discMobius (h : 1 - conj a * z ≠ 0) :
    deriv (discMobius a) z = (1 - normSq a) / (1 - conj a * z) ^ 2 :=
  (hasDerivAt_discMobius h).deriv

/-- The derivative of the disc Möbius map at zero is `1 - normSq a`. -/
theorem deriv_discMobius_zero (a : ℂ) : deriv (discMobius a) 0 = 1 - normSq a := by
  rw [deriv_discMobius (by simp)]
  simp

/-- At a parameter inside the unit disc, the derivative of the disc Möbius map is the reciprocal of
`1 - normSq a`. -/
theorem deriv_discMobius_self (ha : ‖a‖ < 1) :
    deriv (discMobius a) a = (1 - (normSq a : ℂ))⁻¹ := by
  have hna : (1 : ℂ) - normSq a ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h' : normSq a = 1 := by exact_mod_cast h.symm
    rw [normSq_eq_norm_sq] at h'
    nlinarith [norm_nonneg a]
  have hc : (1 : ℂ) - conj a * a = 1 - normSq a := by
    rw [conj_mul', normSq_eq_norm_sq]
    push_cast
    ring
  rw [deriv_discMobius (one_sub_conj_mul_ne_zero ha ha.le), hc, sq, div_mul_eq_div_div,
    div_self hna, one_div]

end Complex

end
