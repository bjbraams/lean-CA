/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Koebe
public import ComplexAnalysis.DiscMobius

/-!
# The pre-Schwarzian bound for univalent functions

For `f` holomorphic and injective on the unit disc with `f 0 = 0` and `f' 0 = 1` (the class
`S`), the **pre-Schwarzian bound**
`‖(1 - ‖z‖ ^ 2) * f'' z / f' z - 2 * conj z‖ ≤ 4`
holds at every `z` in the disc. This is the key estimate behind the Koebe distortion and
growth theorems of `KoebeGrowth`, which integrate it along rays.

The proof composes `f` with the disc Möbius transformation `ψ = discMobius (-z₀)` (sending `0`
to `z₀`) to get a new function of class `S`, and applies Bieberbach's bound `‖a₂‖ ≤ 2`
(`Koebe.norm_taylorCoeff_two_le`) to it; the second Taylor coefficient of the composite unwinds
by the chain rule to `[(1 - ‖z₀‖ ^ 2) f'' z₀ / f' z₀ - 2 conj z₀] / 2`.

## Main results

* `Complex.deriv_deriv_discMobius_zero`: the second derivative of `discMobius a` at `0`.
* `Complex.norm_deriv_deriv_div_deriv_le_four`: Bieberbach's bound `‖φ'' 0 / φ' 0‖ ≤ 4` for
  any injective holomorphic `φ` on the disc.
* `Complex.norm_one_sub_normSq_mul_deriv_deriv_div_deriv_sub_two_conj_le`: **the pre-Schwarzian
  bound**.

## References

* P. L. Duren, *Univalent Functions*, Chapter 2, Theorem 2.6.
* J. B. Conway, *Functions of One Complex Variable II*, Chapter 14, §7.
-/

public noncomputable section

open Set Metric Filter Real
open scoped ComplexConjugate Topology

namespace Complex

variable {f : ℂ → ℂ}

/-- **The second derivative of a disc Möbius transformation at `0`**, as a `HasDerivAt`
statement for `deriv (discMobius a)` itself. -/
theorem hasDerivAt_deriv_discMobius_zero (a : ℂ) :
    HasDerivAt (deriv (discMobius a)) (2 * conj a * (1 - (normSq a : ℂ))) 0 := by
  have hopen : IsOpen {w : ℂ | 1 - conj a * w ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have h0 : (0 : ℂ) ∈ {w : ℂ | 1 - conj a * w ≠ 0} := by simp
  have hev : deriv (discMobius a) =ᶠ[𝓝 (0 : ℂ)]
      fun w ↦ (1 - (normSq a : ℂ)) / (1 - conj a * w) ^ 2 := by
    filter_upwards [hopen.mem_nhds h0] with w hw
    exact deriv_discMobius hw
  -- differentiate the explicit rational formula at `0`
  have hp : HasDerivAt (fun w : ℂ ↦ 1 - conj a * w) (-conj a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (conj a)).const_sub 1
  have hq : HasDerivAt (fun w : ℂ ↦ (1 - conj a * w) ^ 2) (2 * (-conj a)) 0 := by
    simpa using hp.fun_pow 2
  refine (((hasDerivAt_const (0 : ℂ) (1 - (normSq a : ℂ))).div hq (by simp)).congr_deriv ?_)
    |>.congr_of_eventuallyEq hev
  simp
  ring

/-- **The second derivative of a disc Möbius transformation at `0`.** -/
theorem deriv_deriv_discMobius_zero (a : ℂ) :
    deriv (deriv (discMobius a)) 0 = 2 * conj a * (1 - (normSq a : ℂ)) :=
  (hasDerivAt_deriv_discMobius_zero a).deriv

/-- **Bieberbach's bound without normalization.** For `φ` holomorphic and injective on the unit
disc, `‖φ'' 0 / φ' 0‖ ≤ 4`: apply Bieberbach's theorem to `(φ - φ 0) / φ' 0`. -/
theorem norm_deriv_deriv_div_deriv_le_four {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ (ball 0 1))
    (hinj : InjOn φ (ball 0 1)) : ‖deriv (deriv φ) 0 / deriv φ 0‖ ≤ 4 := by
  have hd0 : deriv φ 0 ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hφ hinj (mem_ball_self one_pos)
  set F : ℂ → ℂ := fun z ↦ (φ z - φ 0) / deriv φ 0
  have hderivF : deriv F = fun z ↦ deriv φ z / deriv φ 0 := by
    funext z
    simp only [F, deriv_div_const, deriv_sub_const]
  have hFinj : InjOn F (ball 0 1) := fun z₁ h₁ z₂ h₂ he ↦
    hinj h₁ h₂ (sub_left_inj.mp ((div_left_inj' hd0).mp he))
  have hB := norm_taylorCoeff_two_le ((hφ.sub_const _).div_const _) hFinj (by simp)
    (by rw [hderivF]; exact div_self hd0)
  rw [taylorCoeff, iteratedDeriv_succ, iteratedDeriv_one, hderivF, deriv_div_const, norm_mul,
    norm_inv, Nat.factorial_two, Nat.cast_ofNat, norm_ofNat] at hB
  linarith

/-- **The pre-Schwarzian bound.** For `f` holomorphic and injective on the unit disc,
`‖(1 - ‖z‖ ^ 2) * f'' z / f' z - 2 * conj z‖ ≤ 4`. No normalization of `f` at `0` is needed:
the bound is Bieberbach's bound `norm_deriv_deriv_div_deriv_le_four` for the composite of `f`
with the disc automorphism `ψ = discMobius (-z)` sending `0` to `z`. -/
theorem norm_one_sub_normSq_mul_deriv_deriv_div_deriv_sub_two_conj_le
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hinj : InjOn f (ball 0 1))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) :
    ‖(1 - (normSq z₀ : ℂ)) * deriv (deriv f) z₀ / deriv f z₀ - 2 * conj z₀‖ ≤ 4 := by
  have hU : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd hU
  have hnz₀ : ‖-z₀‖ < 1 := by simpa using hz₀
  set ψ : ℂ → ℂ := discMobius (-z₀)
  have hψd : DifferentiableOn ℂ ψ (ball 0 1) := differentiableOn_discMobius_ball hnz₀
  have hψmaps : MapsTo ψ (ball 0 1) (ball 0 1) := mapsTo_discMobius_ball hnz₀
  have hψ0 : ψ 0 = z₀ := by simp [ψ, discMobius_zero_right]
  have hψinj : InjOn ψ (ball 0 1) := (discMobius_injOn hnz₀).mono ball_subset_closedBall
  have hψ' : deriv ψ 0 = 1 - normSq z₀ := by simp [ψ, deriv_discMobius_zero]
  have hψ'' : HasDerivAt (deriv ψ) (-2 * conj z₀ * (1 - normSq z₀)) 0 := by
    convert hasDerivAt_deriv_discMobius_zero (-z₀) using 1
    simp
  have hnorm : (1 - (normSq z₀ : ℂ)) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub, ofReal_ne_zero, sub_ne_zero, normSq_eq_norm_sq]
    exact (pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hz₀) two_ne_zero).ne'
  -- the chain rule for `φ = f ∘ ψ` and its derivative
  have hderivφ : ∀ z ∈ ball (0 : ℂ) 1,
      deriv (fun z ↦ f (ψ z)) z = deriv f (ψ z) * deriv ψ z := fun z hz ↦
    ((hfan _ (hψmaps hz)).differentiableAt.hasDerivAt.comp z
      (hψd.differentiableAt (hU.mem_nhds hz)).hasDerivAt).deriv
  have hφ' : deriv (fun z ↦ f (ψ z)) 0 = deriv f z₀ * (1 - normSq z₀) := by
    rw [hderivφ 0 h0, hψ0, hψ']
  have hφ'' : deriv (deriv fun z ↦ f (ψ z)) 0 = deriv (deriv f) z₀ * (1 - normSq z₀) ^ 2 +
      deriv f z₀ * (-2 * conj z₀ * (1 - normSq z₀)) := by
    have hcomp : HasDerivAt (fun z ↦ deriv f (ψ z)) (deriv (deriv f) z₀ * deriv ψ 0) 0 :=
      (hfan.deriv z₀ hz₀).differentiableAt.hasDerivAt.comp_of_eq 0
        (hψd.differentiableAt (hU.mem_nhds h0)).hasDerivAt hψ0.symm
    rw [((hcomp.mul hψ'').congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds h0) hderivφ)).deriv, hψ0, hψ']
    ring
  have hB := norm_deriv_deriv_div_deriv_le_four (φ := fun z ↦ f (ψ z)) (hf.comp hψd hψmaps)
    fun z₁ h₁ z₂ h₂ he ↦ hψinj h₁ h₂ (hinj (hψmaps h₁) (hψmaps h₂) he)
  rw [hφ', hφ''] at hB
  have hfz₀ := deriv_ne_zero_of_injOn hU hf hinj hz₀
  convert hB using 2
  field_simp
  ring

end Complex

end
