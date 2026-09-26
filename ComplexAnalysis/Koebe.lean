/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.AreaTheorem
public import ComplexAnalysis.BranchLog
public import ToMathlib.Topology.SimplyConnected

/-!
# Bieberbach's coefficient bound and the Koebe one-quarter theorem

Let `f` be holomorphic and injective on the unit disc with `f 0 = 0` and `f' 0 = 1` (the class
`S`), and write `f z = z + a₂ z² + ⋯`. **Bieberbach's theorem** states `‖a₂‖ ≤ 2`: the square-root
transform `F z = z √(f (z²) / z²)` is odd, injective and normalized, so `1 / F` belongs to the
class `Σ` of the area theorem with first coefficient `-a₂ / 2`, and the area theorem gives
`‖a₂ / 2‖ ≤ 1`. **The Koebe one-quarter theorem** follows: if `w` is omitted by `f`, the
function `f / (1 - f / w)` is again in the class `S` with second coefficient `a₂ + 1 / w`, so
`‖1 / w‖ ≤ 4`. Hence the image of the unit disc contains the disc of radius `1 / 4`.

## Main results

* `Complex.norm_taylorCoeff_two_le`: **Bieberbach's theorem** `‖a₂‖ ≤ 2`.
* `Complex.norm_iteratedDeriv_two_le`: the same bound as `‖f'' 0‖ ≤ 4`.
* `Complex.ball_subset_image_of_injOn`: **the Koebe one-quarter theorem**.

## References

* J. B. Conway, *Functions of One Complex Variable II*, Chapter 14, §7.
* P. L. Duren, *Univalent Functions*, Chapter 2, §2–3.
-/

public noncomputable section

open Set Metric Filter Real
open scoped Topology

namespace Complex

variable {f : ℂ → ℂ}

/-- The divided difference `f z / z` of a normalized injective map is holomorphic and
nonvanishing on the disc. -/
theorem dslope_ne_zero_of_injOn_zero
    (hinj : InjOn f (ball 0 1)) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) : dslope f 0 z ≠ 0 := by
  by_cases hz0 : z = 0
  · subst hz0
    rw [dslope_same, hf1]
    exact one_ne_zero
  · rw [dslope_of_ne _ hz0, slope_def_field, sub_zero, hf0, sub_zero]
    refine div_ne_zero (fun h ↦ hz0 ?_) hz0
    exact hinj hz (mem_ball_self one_pos) (h.trans hf0.symm)

/-- **The square-root transform.** For `f` holomorphic and injective on the unit disc with
`f 0 = 0` and `f' 0 = 1` there is a holomorphic nonvanishing `q` with `q 0 = 1`,
`q (z ^ 2) ^ 2 = f (z ^ 2) / z ^ 2` and `q' 0 = a₂ / 2`, such that the odd function
`F z = z * q (z ^ 2)` is injective on the disc. -/
theorem exists_sqrt_transform (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (ball 0 1) ∧ q 0 = 1 ∧ (∀ z ∈ ball (0 : ℂ) 1, q z ≠ 0) ∧
      deriv q 0 = taylorCoeff f 2 / 2 ∧ InjOn (fun z ↦ z * q (z ^ 2)) (ball 0 1) := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hU : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0
  -- a holomorphic square root of the divided difference `p = dslope f 0`
  have hp0 : ∀ z ∈ ball (0 : ℂ) 1, dslope f 0 z ≠ 0 := fun z hz ↦
    dslope_ne_zero_of_injOn_zero hinj hf0 hf1 hz
  have hp00 : dslope f 0 0 = 1 := by rw [dslope_same, hf1]
  obtain ⟨q₀, hq₀, hq₀sq⟩ := exists_analyticOnNhd_root isOpen_ball
    ((convex_ball 0 1).isSimplyConnected (nonempty_ball.mpr one_pos))
    ((differentiableOn_dslope hU).mpr hf) hp0 two_ne_zero
  -- normalize the root so that `q 0 = 1`
  have hq₀0 : q₀ 0 ^ 2 = 1 := by rw [hq₀sq 0 h0, hp00]
  set q : ℂ → ℂ := fun z ↦ q₀ 0 * q₀ z
  have hqd : DifferentiableOn ℂ q (ball 0 1) :=
    (differentiableOn_const _).mul hq₀.differentiableOn
  have hqsq : ∀ z ∈ ball (0 : ℂ) 1, q z ^ 2 = dslope f 0 z := fun z hz ↦ by
    simp only [q, mul_pow, hq₀0, one_mul, hq₀sq z hz]
  have hq0 : q 0 = 1 := by simp only [q, ← sq, hq₀0]
  have hqne : ∀ z ∈ ball (0 : ℂ) 1, q z ≠ 0 := fun z hz h ↦ by
    have := hqsq z hz
    rw [h, zero_pow two_ne_zero] at this
    exact hp0 z hz this.symm
  have hq' : deriv q 0 = taylorCoeff f 2 / 2 := by
    have hqa : HasDerivAt q (deriv q 0) 0 := ((hqd 0 h0).differentiableAt hU).hasDerivAt
    have h1 : deriv (fun z ↦ q z ^ 2) 0 = 2 * deriv q 0 := by
      rw [show (fun z ↦ q z ^ 2) = q ^ 2 from rfl, (hqa.pow 2).deriv, hq0]
      norm_num
    have h2 : deriv (fun z ↦ q z ^ 2) 0 = taylorCoeff f 2 := by
      rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem hU hqsq), ← taylorCoeff_one,
        taylorCoeff_dslope_zero hf one_pos 1]
    rw [← h2, h1]
    ring
  refine ⟨q, hqd, hq0, hqne, hq', ?_⟩
  -- `F z = z q (z²)` is odd with `F² = f (z²)`, hence injective
  have hsq : ∀ z ∈ ball (0 : ℂ) 1, z ^ 2 ∈ ball (0 : ℂ) 1 := fun z hz ↦ by
    rw [mem_ball_zero_iff, norm_pow]
    have := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  have hFsq : ∀ z ∈ ball (0 : ℂ) 1, (z * q (z ^ 2)) ^ 2 = f (z ^ 2) := fun z hz ↦ by
    rw [mul_pow, hqsq _ (hsq z hz)]
    by_cases hz0 : z = 0
    · simp [hz0, hf0]
    · rw [dslope_of_ne _ (pow_ne_zero 2 hz0), slope_def_field, sub_zero, hf0, sub_zero,
        mul_div_cancel₀ _ (pow_ne_zero 2 hz0)]
  intro z₁ hz₁ z₂ hz₂ he
  have h2 : z₁ ^ 2 = z₂ ^ 2 := hinj (hsq z₁ hz₁) (hsq z₂ hz₂)
    (by rw [← hFsq z₁ hz₁, ← hFsq z₂ hz₂]; exact congrArg (· ^ 2) he)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
  · exact h
  · -- `F` is odd, so `F z₂ = -F z₂ = 0`, forcing `z₂ = 0`
    simp only [h, neg_sq, neg_mul] at he
    have hF : z₂ * q (z₂ ^ 2) = 0 := by linear_combination -he / 2
    rcases mul_eq_zero.mp hF with hz | hz
    · rw [h, hz, neg_zero]
    · exact absurd hz (hqne _ (hsq z₂ hz₂))

/-- **The reciprocal of the square-root transform is of class `Σ`.** If `q` is holomorphic and
nonvanishing on the disc with `q 0 = 1` and `F z = z * q (z ^ 2)` is injective, then
`1 / F z = z⁻¹ + h z` for a holomorphic `h` whose first Taylor coefficient is `-q' 0`. -/
theorem exists_sigma_of_sqrt_transform {q : ℂ → ℂ} (hqd : DifferentiableOn ℂ q (ball 0 1))
    (hq0 : q 0 = 1) (hqne : ∀ z ∈ ball (0 : ℂ) 1, q z ≠ 0)
    (hFinj : InjOn (fun z ↦ z * q (z ^ 2)) (ball 0 1)) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball 0 1) ∧
      InjOn (fun z ↦ z⁻¹ + h z) (ball 0 1 \ {0}) ∧ taylorCoeff h 1 = -deriv q 0 := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hU : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0
  have hsq : ∀ z ∈ ball (0 : ℂ) 1, z ^ 2 ∈ ball (0 : ℂ) 1 := fun z hz ↦ by
    rw [mem_ball_zero_iff, norm_pow]
    have := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  set u : ℂ → ℂ := fun w ↦ (q w)⁻¹ - 1
  have hu0 : u 0 = 0 := by simp [u, hq0]
  set D : ℂ → ℂ := dslope u 0
  have hDd : DifferentiableOn ℂ D (ball 0 1) :=
    (differentiableOn_dslope hU).mpr ((hqd.inv hqne).sub (differentiableOn_const _))
  refine ⟨fun z ↦ z * D (z ^ 2), differentiableOn_id.mul (hDd.comp (differentiableOn_pow 2) hsq),
    ?_, ?_⟩
  · have hg : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, z⁻¹ + z * D (z ^ 2) = (z * q (z ^ 2))⁻¹ := by
      rintro z ⟨hz, hz0⟩
      have hq' := hqne _ (hsq z hz)
      have hz0' : z ≠ 0 := hz0
      simp only [D, u, dslope_of_ne _ (pow_ne_zero 2 hz0'), slope_def_field, sub_zero, hu0]
      field_simp
      ring
    intro z₁ hz₁ z₂ hz₂ he
    simp only [hg z₁ hz₁, hg z₂ hz₂, inv_inj] at he
    exact hFinj hz₁.1 hz₂.1 he
  · have hDa : HasDerivAt D (deriv D 0) 0 := ((hDd 0 h0).differentiableAt hU).hasDerivAt
    have hmul : HasDerivAt (fun z : ℂ ↦ z * D (z ^ 2))
        (1 * D (0 ^ 2) + 0 * (deriv D 0 * ((2 : ℕ) * (0 : ℂ) ^ (2 - 1)))) 0 :=
      (hasDerivAt_id' 0).mul (hDa.comp_of_eq 0 (hasDerivAt_pow 2 0) (by simp))
    rw [taylorCoeff_one, hmul.deriv]
    have hqa : HasDerivAt q (deriv q 0) 0 := ((hqd 0 h0).differentiableAt hU).hasDerivAt
    have hinv : HasDerivAt (fun w ↦ (q w)⁻¹ - 1) (-(deriv q 0) / q 0 ^ 2) 0 :=
      (hqa.inv (hqne 0 h0)).sub_const 1
    simp [D, u, dslope_same, hinv.deriv, hq0]

/-- **Bieberbach's theorem**: for `f` holomorphic and injective on the unit disc with `f 0 = 0`
and `f' 0 = 1`, the second Taylor coefficient satisfies `‖a₂‖ ≤ 2`. -/
theorem norm_taylorCoeff_two_le (hf : DifferentiableOn ℂ f (ball 0 1)) (hinj : InjOn f (ball 0 1))
    (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1) : ‖taylorCoeff f 2‖ ≤ 2 := by
  obtain ⟨q, hqd, hq0, hqne, hq', hFinj⟩ := exists_sqrt_transform hf hinj hf0 hf1
  obtain ⟨h, hhd, hinj', hh1⟩ := exists_sigma_of_sqrt_transform hqd hq0 hqne hFinj
  have := norm_taylorCoeff_one_le hhd hinj'
  rw [hh1, hq', norm_neg, norm_div, norm_ofNat] at this
  linarith

/-- **Bieberbach's theorem** in terms of the second derivative: `‖f'' 0‖ ≤ 4`. -/
theorem norm_iteratedDeriv_two_le (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1) :
    ‖iteratedDeriv 2 f 0‖ ≤ 4 := by
  have := norm_taylorCoeff_two_le hf hinj hf0 hf1
  rw [taylorCoeff, norm_mul, norm_inv, norm_natCast, Nat.factorial_two, Nat.cast_ofNat] at this
  linarith

/-- **The Koebe one-quarter theorem**: the image of the unit disc under a holomorphic injective
map `f` with `f 0 = 0` and `f' 0 = 1` contains the disc of radius `1 / 4`. -/
theorem ball_subset_image_of_injOn (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1) :
    ball (0 : ℂ) (1 / 4) ⊆ f '' ball 0 1 := by
  intro w hw
  by_contra hwf
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hU : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds h0
  have hw0 : w ≠ 0 := fun h ↦ hwf ⟨0, h0, by rw [hf0, h]⟩
  have hfw : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ w := fun z hz h ↦ hwf ⟨z, hz, h⟩
  -- the transformed map `F = f / (1 - f / w) = f + f² v / w`
  set v : ℂ → ℂ := fun z ↦ (1 - f z / w)⁻¹ with hv_def
  have hvne : ∀ z ∈ ball (0 : ℂ) 1, 1 - f z / w ≠ 0 := fun z hz h ↦ by
    apply hfw z hz
    have : f z / w = 1 := by linear_combination -h
    rwa [div_eq_one_iff_eq hw0] at this
  have hvd : DifferentiableOn ℂ v (ball 0 1) :=
    ((differentiableOn_const _).sub (hf.div_const w)).inv hvne
  have hv0 : v 0 = 1 := by
    rw [hv_def]
    simp [hf0]
  set G : ℂ → ℂ := fun z ↦ f z ^ 2 * v z / w with hG_def
  set F : ℂ → ℂ := fun z ↦ f z + G z with hF_def
  have hGd : DifferentiableOn ℂ G (ball 0 1) := ((hf.pow 2).mul hvd).div_const w
  have hFd : DifferentiableOn ℂ F (ball 0 1) := hf.add hGd
  have hFmul : ∀ z ∈ ball (0 : ℂ) 1, F z = f z * v z := by
    intro z hz
    have hv1 : (1 - f z / w)⁻¹ * (1 - f z / w) = 1 := inv_mul_cancel₀ (hvne z hz)
    simp only [hF_def, hG_def, hv_def]
    linear_combination (-(f z)) * hv1
  have hF0 : F 0 = 0 := by rw [hFmul 0 h0, hf0, zero_mul]
  have hF1 : deriv F 0 = 1 := by
    have hev : F =ᶠ[𝓝 0] fun z ↦ f z * v z := by
      filter_upwards [hU] with z hz
      exact hFmul z hz
    rw [hev.deriv_eq]
    have hfa : HasDerivAt f (deriv f 0) 0 := ((hf 0 h0).differentiableAt hU).hasDerivAt
    have hva : HasDerivAt v (deriv v 0) 0 := ((hvd 0 h0).differentiableAt hU).hasDerivAt
    have hmul : HasDerivAt (fun z ↦ f z * v z) (deriv f 0 * v 0 + f 0 * deriv v 0) 0 :=
      hfa.mul hva
    rw [hmul.deriv, hf0, hv0, hf1]
    ring
  have hFinj : InjOn F (ball 0 1) := by
    intro z₁ hz₁ z₂ hz₂ he
    rw [hFmul z₁ hz₁, hFmul z₂ hz₂] at he
    have h1 := hvne z₁ hz₁
    have h2 := hvne z₂ hz₂
    have key : f z₁ * (1 - f z₂ / w) = f z₂ * (1 - f z₁ / w) := by
      calc f z₁ * (1 - f z₂ / w)
          = f z₁ * (1 - f z₁ / w)⁻¹ * ((1 - f z₁ / w) * (1 - f z₂ / w)) := by
            rw [mul_assoc, ← mul_assoc (1 - f z₁ / w)⁻¹, inv_mul_cancel₀ h1, one_mul]
        _ = f z₂ * (1 - f z₂ / w)⁻¹ * ((1 - f z₁ / w) * (1 - f z₂ / w)) := by rw [he]
        _ = f z₂ * (1 - f z₁ / w) := by
            rw [mul_assoc, mul_comm (1 - f z₁ / w), ← mul_assoc (1 - f z₂ / w)⁻¹,
              inv_mul_cancel₀ h2, one_mul]
    exact hinj hz₁ hz₂ (by linear_combination key)
  -- the second coefficient of `F` is `a₂ + 1 / w`
  have hG2 : taylorCoeff G 2 = 1 / w := by
    set K : ℂ → ℂ := fun z ↦ dslope f 0 z ^ 2 * v z / w with hK_def
    have hKd : DifferentiableOn ℂ K (ball 0 1) :=
      ((((differentiableOn_dslope hU).mpr hf).pow 2).mul hvd).div_const w
    have hGK : G = fun z ↦ z ^ 2 * K z := by
      funext z
      have hz : f z = z * dslope f 0 z := by
        have := sub_smul_dslope f 0 z
        rw [sub_zero, hf0, sub_zero, smul_eq_mul] at this
        exact this.symm
      simp only [hG_def, hK_def]
      rw [hz]
      ring
    have := taylorCoeff_pow_mul hKd one_pos 2 0
    rw [zero_add, taylorCoeff_zero] at this
    rw [hGK, this, hK_def]
    dsimp only
    rw [dslope_same, hf1, hv0]
    ring
  have hF2 : taylorCoeff F 2 = taylorCoeff f 2 + 1 / w := by
    rw [hF_def, taylorCoeff_add hf hGd one_pos 2, hG2]
  -- Bieberbach's bound for `F` and for `f`
  have hB := norm_taylorCoeff_two_le hFd hFinj hF0 hF1
  have hA := norm_taylorCoeff_two_le hf hinj hf0 hf1
  rw [hF2] at hB
  have h4 : ‖1 / w‖ ≤ 4 := by
    have := norm_sub_le (taylorCoeff f 2 + 1 / w) (taylorCoeff f 2)
    rw [add_sub_cancel_left] at this
    linarith
  rw [norm_div, norm_one, one_div] at h4
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hw' : ‖w‖ < 1 / 4 := mem_ball_zero_iff.mp hw
  have h5 : (1 : ℝ) ≤ ‖w‖ * 4 := by
    calc (1 : ℝ) = ‖w‖ * ‖w‖⁻¹ := (mul_inv_cancel₀ hwpos.ne').symm
      _ ≤ ‖w‖ * 4 := by gcongr
  linarith

end Complex

end
