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
growth theorems (not derived here, since they require integrating this pointwise bound along a
ray, an additional argument not included).

The proof composes `f` with the disc Möbius transformation `ψ = discMobius (-z₀)` (sending `0`
to `z₀`) to get a new function of class `S`, and applies Bieberbach's bound `‖a₂‖ ≤ 2`
(`Koebe.norm_taylorCoeff_two_le`) to it; the second Taylor coefficient of the composite unwinds
by the chain rule to `[(1 - ‖z₀‖ ^ 2) f'' z₀ / f' z₀ - 2 conj z₀] / 2`.

## Main results

* `Complex.deriv_deriv_discMobius_zero`: the second derivative of `discMobius a` at `0`.
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
      fun w => (1 - (normSq a : ℂ)) / (1 - conj a * w) ^ 2 := by
    filter_upwards [hopen.mem_nhds h0] with w hw
    exact deriv_discMobius hw
  -- differentiate the explicit rational formula at `0`
  have hp : HasDerivAt (fun w : ℂ => 1 - conj a * w) (-conj a) 0 := by
    have h1 : HasDerivAt (fun w : ℂ => conj a * w) (conj a) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (conj a)
    simpa using h1.const_sub 1
  have hp2 : HasDerivAt (fun w : ℂ => (1 - conj a * w) * (1 - conj a * w))
      ((-conj a) * (1 - conj a * (0:ℂ)) + (1 - conj a * (0:ℂ)) * (-conj a)) 0 :=
    hp.mul hp
  have hp0 : (1 - conj a * (0 : ℂ)) ≠ 0 := by simp
  have hp20 : (1 - conj a * (0 : ℂ)) * (1 - conj a * (0 : ℂ)) ≠ 0 := mul_ne_zero hp0 hp0
  have hinv : HasDerivAt (fun w : ℂ => ((1 - conj a * w) * (1 - conj a * w))⁻¹)
      (-((-conj a) * (1 - conj a * (0:ℂ)) + (1 - conj a * (0:ℂ)) * (-conj a)) /
        ((1 - conj a * (0:ℂ)) * (1 - conj a * (0:ℂ))) ^ 2) 0 :=
    hp2.inv hp20
  have hmul : HasDerivAt (fun w : ℂ => (1 - (normSq a : ℂ)) *
      ((1 - conj a * w) * (1 - conj a * w))⁻¹)
      ((1 - (normSq a : ℂ)) *
        (-((-conj a) * (1 - conj a * (0:ℂ)) + (1 - conj a * (0:ℂ)) * (-conj a)) /
          ((1 - conj a * (0:ℂ)) * (1 - conj a * (0:ℂ))) ^ 2)) 0 :=
    hinv.const_mul _
  have heq : (fun w : ℂ => (1 - (normSq a : ℂ)) * ((1 - conj a * w) * (1 - conj a * w))⁻¹)
      = fun w => (1 - (normSq a : ℂ)) / (1 - conj a * w) ^ 2 := by
    funext w; rw [div_eq_mul_inv, sq]
  rw [heq] at hmul
  have hval : (1 - (normSq a : ℂ)) *
      (-((-conj a) * (1 - conj a * (0:ℂ)) + (1 - conj a * (0:ℂ)) * (-conj a)) /
        ((1 - conj a * (0:ℂ)) * (1 - conj a * (0:ℂ))) ^ 2)
      = 2 * conj a * (1 - (normSq a : ℂ)) := by
    simp only [mul_zero, sub_zero]
    ring
  rw [hval] at hmul
  exact hmul.congr_of_eventuallyEq hev

/-- **The second derivative of a disc Möbius transformation at `0`.** -/
theorem deriv_deriv_discMobius_zero (a : ℂ) :
    deriv (deriv (discMobius a)) 0 = 2 * conj a * (1 - (normSq a : ℂ)) :=
  (hasDerivAt_deriv_discMobius_zero a).deriv

/-- **The pre-Schwarzian bound.** For `f` holomorphic and injective on the unit disc,
`‖(1 - ‖z‖ ^ 2) * f'' z / f' z - 2 * conj z‖ ≤ 4`. No normalization of `f` at `0` is needed:
the bound is invariant under post-composition of `f` with an affine map, so it follows from
Bieberbach's theorem applied to the normalized Koebe transform of `f` at `z`, not to `f`
itself. -/
theorem norm_one_sub_normSq_mul_deriv_deriv_div_deriv_sub_two_conj_le
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hinj : InjOn f (ball 0 1))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) :
    ‖(1 - (normSq z₀ : ℂ)) * deriv (deriv f) z₀ / deriv f z₀ - 2 * conj z₀‖ ≤ 4 := by
  have hU : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd hU
  have hfz₀ne : deriv f z₀ ≠ 0 := deriv_ne_zero_of_injOn hU hf hinj hz₀
  have hnz₀ : ‖-z₀‖ < 1 := by simpa using hz₀
  set ψ : ℂ → ℂ := discMobius (-z₀) with hψ_def
  have hψd : DifferentiableOn ℂ ψ (ball 0 1) := differentiableOn_discMobius_ball hnz₀
  have hψmaps : MapsTo ψ (ball 0 1) (ball 0 1) := mapsTo_discMobius_ball hnz₀
  have hψ0 : ψ 0 = z₀ := by rw [hψ_def]; simp [discMobius_zero_right]
  have hψinj : InjOn ψ (ball 0 1) := discMobius_injOn hnz₀ |>.mono ball_subset_closedBall
  have hψderiv0 : deriv ψ 0 = 1 - normSq z₀ := by
    rw [hψ_def, deriv_discMobius_zero]; simp
  have hψderiv0' : (1 : ℂ) - normSq (-z₀) = 1 - normSq z₀ := by simp
  -- the composite `φ = f ∘ ψ`
  set φ : ℂ → ℂ := fun z => f (ψ z) with hφ_def
  have hφd : DifferentiableOn ℂ φ (ball 0 1) := hf.comp hψd hψmaps
  have hφinj : InjOn φ (ball 0 1) := fun z₁ hz₁ z₂ hz₂ he =>
    hψinj hz₁ hz₂ (hinj (hψmaps hz₁) (hψmaps hz₂) he)
  have hψan : AnalyticAt ℂ ψ 0 := hψd.analyticOnNhd hU 0 (mem_ball_self one_pos)
  have hfan' : AnalyticAt ℂ f z₀ := hfan z₀ hz₀
  have hψhd0 : HasDerivAt ψ (deriv ψ 0) 0 := hψan.differentiableAt.hasDerivAt
  have hfhd0 : HasDerivAt f (deriv f z₀) z₀ := hfan'.differentiableAt.hasDerivAt
  have hφderiv0 : deriv φ 0 = deriv f z₀ * deriv ψ 0 := by
    have h := (hfhd0.comp_of_eq 0 hψhd0 hψ0.symm).deriv
    rw [show (f ∘ ψ) = φ from rfl] at h
    exact h
  have hψderiv0ne : deriv ψ 0 ≠ 0 := by
    rw [hψderiv0]
    have hnormlt : normSq z₀ < 1 := by
      rw [normSq_eq_norm_sq]
      exact pow_lt_one₀ (norm_nonneg z₀) (mem_ball_zero_iff.mp hz₀) two_ne_zero
    intro h
    rw [sub_eq_zero] at h
    have : normSq z₀ = 1 := by exact_mod_cast h.symm
    linarith
  have hφderiv0ne : deriv φ 0 ≠ 0 := by
    rw [hφderiv0]; exact mul_ne_zero hfz₀ne hψderiv0ne
  -- the second derivative of `φ` at `0` by the chain and product rules
  have hderivφ_eq : ∀ z ∈ ball (0 : ℂ) 1, deriv φ z = deriv f (ψ z) * deriv ψ z := by
    intro z hz
    have h1 : HasDerivAt f (deriv f (ψ z)) (ψ z) :=
      (hfan (ψ z) (hψmaps hz)).differentiableAt.hasDerivAt
    have h2 : HasDerivAt ψ (deriv ψ z) z := (hψd.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have h := h1.comp z h2
    rw [show (f ∘ ψ) = φ from rfl] at h
    exact h.deriv
  have hderivφ_ev : deriv φ =ᶠ[𝓝 (0 : ℂ)] fun z => deriv f (ψ z) * deriv ψ z := by
    filter_upwards [hU.mem_nhds (mem_ball_self one_pos)] with z hz using hderivφ_eq z hz
  have hderivfan : AnalyticOnNhd ℂ (deriv f) (ball 0 1) := hfan.deriv
  have hderivf_hd : HasDerivAt (deriv f) (deriv (deriv f) z₀) z₀ :=
    (hderivfan z₀ hz₀).differentiableAt.hasDerivAt
  have hcomp1 : HasDerivAt (fun z => deriv f (ψ z)) (deriv (deriv f) z₀ * deriv ψ 0) 0 :=
    hderivf_hd.comp_of_eq 0 hψhd0 hψ0.symm
  have hψ2hd0 : HasDerivAt (deriv ψ) (-2 * conj z₀ * (1 - normSq z₀)) 0 := by
    have h := hasDerivAt_deriv_discMobius_zero (-z₀)
    have hval : 2 * conj (-z₀) * (1 - (normSq (-z₀) : ℂ)) = -2 * conj z₀ * (1 - normSq z₀) := by
      simp only [map_neg]; rw [hψderiv0']; ring
    rw [hψ_def]
    rwa [hval] at h
  have hprod : HasDerivAt (fun z => deriv f (ψ z) * deriv ψ z)
      (deriv (deriv f) z₀ * deriv ψ 0 * deriv ψ 0 +
        deriv f (ψ 0) * (-2 * conj z₀ * (1 - normSq z₀))) 0 :=
    hcomp1.mul hψ2hd0
  have hφ2hd0 : HasDerivAt (deriv φ)
      (deriv (deriv f) z₀ * deriv ψ 0 * deriv ψ 0 +
        deriv f (ψ 0) * (-2 * conj z₀ * (1 - normSq z₀))) 0 :=
    hprod.congr_of_eventuallyEq hderivφ_ev
  have hφ2eq : deriv (deriv φ) 0 =
      deriv (deriv f) z₀ * deriv ψ 0 * deriv ψ 0 +
        deriv f (ψ 0) * (-2 * conj z₀ * (1 - normSq z₀)) :=
    hφ2hd0.deriv
  rw [hψ0] at hφ2eq
  -- assemble the normalized function `F` and apply Bieberbach's bound
  set F : ℂ → ℂ := fun z => (φ z - φ 0) / deriv φ 0 with hF_def
  have hFd : DifferentiableOn ℂ F (ball 0 1) :=
    ((hφd.sub_const _)).div_const _
  have hFinj : InjOn F (ball 0 1) := by
    intro z₁ hz₁ z₂ hz₂ he
    apply hφinj hz₁ hz₂
    have he' : (φ z₁ - φ 0) / deriv φ 0 = (φ z₂ - φ 0) / deriv φ 0 := by
      simpa [hF_def] using he
    field_simp [hφderiv0ne] at he'
    linear_combination he'
  have hF0 : F 0 = 0 := by rw [hF_def]; simp
  have hF1 : deriv F 0 = 1 := by
    have hev : F =ᶠ[𝓝 (0:ℂ)] fun z => (deriv φ 0)⁻¹ • (φ z - φ 0) := by
      filter_upwards with z; rw [hF_def]; simp [div_eq_inv_mul, smul_eq_mul]
    have hφhd0 : HasDerivAt φ (deriv φ 0) 0 := by
      have h1 : DifferentiableAt ℂ f (ψ 0) :=
        (hfan (ψ 0) (hψmaps (mem_ball_self one_pos))).differentiableAt
      have h2 : DifferentiableAt ℂ ψ 0 :=
        hψd.differentiableAt (hU.mem_nhds (mem_ball_self one_pos))
      have hcomp := h1.hasDerivAt.comp 0 h2.hasDerivAt
      have hcast : deriv f (ψ 0) * deriv ψ 0 = deriv φ 0 :=
        (hderivφ_eq 0 (mem_ball_self one_pos)).symm
      rw [hcast, show (f ∘ ψ) = φ from rfl] at hcomp
      exact hcomp
    have hFhd0 : HasDerivAt F ((deriv φ 0)⁻¹ * deriv φ 0) 0 := by
      have hsm := (hφhd0.sub_const (φ 0)).const_smul (deriv φ 0)⁻¹
      simp only [smul_eq_mul] at hsm
      exact hsm.congr_of_eventuallyEq hev
    have := hFhd0.deriv
    rw [inv_mul_cancel₀ hφderiv0ne] at this
    exact this
  have hbieber := norm_taylorCoeff_two_le hFd hFinj hF0 hF1
  have hFtaylor2 : taylorCoeff F 2 = deriv (deriv φ) 0 / (2 * deriv φ 0) := by
    rw [taylorCoeff]
    have hiter : iteratedDeriv 2 F 0 = deriv (deriv φ) 0 / deriv φ 0 := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, hF_def]
      have hevd : deriv (fun z => (φ z - φ 0) / deriv φ 0) =ᶠ[𝓝 (0:ℂ)]
          fun z => deriv φ z / deriv φ 0 := by
        filter_upwards with z
        rw [deriv_div_const, deriv_sub_const]
      rw [Filter.EventuallyEq.deriv_eq hevd, deriv_div_const]
    rw [hiter]
    have h2fac : ((Nat.factorial 2 : ℕ) : ℂ) = 2 := by norm_num [Nat.factorial]
    rw [h2fac]
    field_simp
  rw [hFtaylor2, hφ2eq, hφderiv0, hψderiv0] at hbieber
  have hnormne : (1 - (normSq z₀ : ℂ)) ≠ 0 := by
    intro h
    apply hψderiv0ne
    rw [hψderiv0]; exact h
  have hCne : deriv f z₀ * (1 - (normSq z₀ : ℂ)) ≠ 0 := mul_ne_zero hfz₀ne hnormne
  have hsimplify :
      (deriv (deriv f) z₀ * (1 - (normSq z₀ : ℂ)) * (1 - (normSq z₀ : ℂ)) +
          deriv f z₀ * (-2 * conj z₀ * (1 - (normSq z₀ : ℂ)))) /
        (2 * (deriv f z₀ * (1 - (normSq z₀ : ℂ)))) =
        ((1 - (normSq z₀ : ℂ)) * deriv (deriv f) z₀ / deriv f z₀ - 2 * conj z₀) / 2 := by
    field_simp [hnormne]
    ring
  rw [hsimplify, norm_div] at hbieber
  have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2norm, div_le_iff₀ (by norm_num : (0:ℝ) < 2)] at hbieber
  linarith [hbieber]

end Complex

end
