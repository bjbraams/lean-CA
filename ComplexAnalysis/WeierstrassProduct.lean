/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.InfiniteProduct
public import ComplexAnalysis.WeierstrassFactor
public import ComplexAnalysis.RemovableSingularity
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Weierstrass product theorem and factorization for entire functions

For a sequence `a n` of nonzero complex numbers with `‖a n‖ → ∞`, the Weierstrass product
`∏' n, E n (z / a n)` of elementary factors is an entire function whose zeros are exactly the
`a n`, with the order at `w` equal to the number of `n` with `a n = w`. Every entire function
`f` with `f 0 ≠ 0` and with exactly these zeros and orders is `exp g` times the product for some
entire `g` (Weierstrass factorization).

## Main definitions

* `Complex.weierstrassProduct a z = ∏' n, elementaryFactor n (z / a n)`.

## Main results

* `Complex.differentiable_weierstrassProduct`, `Complex.weierstrassProduct_eq_zero_iff`,
  `Complex.analyticOrderAt_weierstrassProduct`.
* `Complex.exists_exp_mul_weierstrassProduct`: the factorization theorem.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorems VII.5.12 and VII.5.14.
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open scoped Topology

namespace Complex

/-- The Weierstrass product with zeros `a n`, using the elementary factor of index `n` for the
`n`-th zero. -/
def weierstrassProduct (a : ℕ → ℂ) (z : ℂ) : ℂ := ∏' n, elementaryFactor n (z / a n)

variable {a : ℕ → ℂ}

/-- The set of indices of a given zero is finite. -/
theorem finite_setOf_eq_of_tendsto (hlim : Tendsto (fun n => ‖a n‖) atTop atTop) (w : ℂ) :
    {n | a n = w}.Finite := by
  have h := hlim.eventually (eventually_gt_atTop ‖w‖)
  rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at h
  refine h.subset fun n hn => ?_
  have hn' : a n = w := hn
  simp [hn']

/-- The terms `E n (z / a n) - 1` have summable uniform bounds on every compact set. -/
theorem hasSummableBoundOn_weierstrass (ha : ∀ n, a n ≠ 0)
    (hlim : Tendsto (fun n => ‖a n‖) atTop atTop) :
    HasSummableBoundOn (fun n z => elementaryFactor n (z / a n) - 1) univ := by
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨fun n => 4 * (1 / 2 : ℝ) ^ (n + 1), ?_, ?_⟩
  · exact (summable_geometric_two.comp_injective (add_left_injective 1)).mul_left 4
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [hlim.eventually (eventually_ge_atTop (2 * max R 0 + 1))] with n hn z hz
    have hzR : ‖z‖ ≤ max R 0 := by
      have := hR hz
      rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    have hw : ‖z / a n‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (ha n))]
      linarith [le_max_right R 0]
    calc ‖elementaryFactor n (z / a n) - 1‖ = ‖1 - elementaryFactor n (z / a n)‖ :=
          norm_sub_rev _ _
      _ ≤ 4 * ‖z / a n‖ ^ (n + 1) := norm_one_sub_elementaryFactor_le hw
      _ ≤ 4 * (1 / 2 : ℝ) ^ (n + 1) := by gcongr

/-- The Weierstrass product can be written as a product of factors of the form `1 + f n z`. -/
theorem weierstrassProduct_eq_tprod_one_add (z : ℂ) :
    weierstrassProduct a z = ∏' n, (1 + (elementaryFactor n (z / a n) - 1)) := by
  simp [weierstrassProduct]

/-- The Weierstrass product is entire. -/
theorem differentiable_weierstrassProduct (ha : ∀ n, a n ≠ 0)
    (hlim : Tendsto (fun n => ‖a n‖) atTop atTop) :
    Differentiable ℂ (weierstrassProduct a) := by
  rw [← differentiableOn_univ]
  have : weierstrassProduct a = fun z => ∏' n, (1 + (elementaryFactor n (z / a n) - 1)) :=
    funext weierstrassProduct_eq_tprod_one_add
  rw [this]
  refine differentiableOn_tprod_one_add isOpen_univ (fun n => ?_)
    (hasSummableBoundOn_weierstrass ha hlim)
  exact ((differentiable_elementaryFactor n).comp (differentiable_id.div_const _)).sub
    (differentiable_const 1) |>.differentiableOn

/-- The zeros of the Weierstrass product are exactly the `a n`. -/
theorem weierstrassProduct_eq_zero_iff (ha : ∀ n, a n ≠ 0)
    (hlim : Tendsto (fun n => ‖a n‖) atTop atTop) (z : ℂ) :
    weierstrassProduct a z = 0 ↔ ∃ n, z = a n := by
  rw [weierstrassProduct_eq_tprod_one_add,
    tprod_one_add_eq_zero_iff (hasSummableBoundOn_weierstrass ha hlim) (mem_univ z)]
  simp only [add_sub_cancel, elementaryFactor_eq_zero_iff]
  refine exists_congr fun n => ?_
  rw [div_eq_one_iff_eq (ha n)]

/-- The Weierstrass product has value one at the origin. -/
@[simp] theorem weierstrassProduct_zero (a : ℕ → ℂ) : weierstrassProduct a 0 = 1 := by
  simp [weierstrassProduct]

/-- The elementary factor rescaled to vanish at `c` has order one there. -/
theorem analyticOrderAt_elementaryFactor_div {c : ℂ} (hc : c ≠ 0) (p : ℕ) :
    analyticOrderAt (fun z => elementaryFactor p (z / c)) c = 1 := by
  have hfun : (fun z => elementaryFactor p (z / c)) =
      (fun z => (-c⁻¹ : ℂ) * (z - c)) * fun z => exp (elementaryExponent p (z / c)) := by
    ext z
    simp only [elementaryFactor_eq, Pi.mul_apply]
    congr 1
    field_simp
    ring
  have hexp : AnalyticAt ℂ (fun z => exp (elementaryExponent p (z / c))) c :=
    (((differentiable_elementaryExponent p).comp (differentiable_id.div_const c)).analyticAt
      c).cexp
  rw [hfun, analyticOrderAt_mul (by fun_prop) hexp,
    (hexp.analyticOrderAt_eq_zero).mpr (exp_ne_zero _), add_zero]
  change analyticOrderAt ((fun _ => (-c⁻¹ : ℂ)) * fun z => z - c) c = 1
  rw [analyticOrderAt_mul analyticAt_const (by fun_prop),
    (analyticAt_const.analyticOrderAt_eq_zero).mpr (by simpa using hc), zero_add]
  exact analyticOrderAt_id_sub_const_self

/-- **Orders of the Weierstrass product.** The order at `w` is the number of `n` with
`a n = w`. -/
theorem analyticOrderAt_weierstrassProduct (ha : ∀ n, a n ≠ 0)
    (hlim : Tendsto (fun n => ‖a n‖) atTop atTop) (w : ℂ) :
    analyticOrderAt (weierstrassProduct a) w =
      ((finite_setOf_eq_of_tendsto hlim w).toFinset.card : ℕ∞) := by
  classical
  have hb := hasSummableBoundOn_weierstrass ha hlim
  have hf : ∀ n, DifferentiableOn ℂ (fun z => elementaryFactor n (z / a n) - 1) univ := fun n =>
    (((differentiable_elementaryFactor n).comp (differentiable_id.div_const _)).sub
      (differentiable_const 1)).differentiableOn
  have hfun : weierstrassProduct a = fun z => ∏' n, (1 + (elementaryFactor n (z / a n) - 1)) :=
    funext weierstrassProduct_eq_tprod_one_add
  rw [hfun, analyticOrderAt_tprod_one_add isOpen_univ hf hb (mem_univ w)]
  have hset : (finite_setOf_one_add_eq_zero hb (mem_univ w)).toFinset =
      (finite_setOf_eq_of_tendsto hlim w).toFinset := by
    ext n
    simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, add_sub_cancel,
      elementaryFactor_eq_zero_iff, div_eq_one_iff_eq (ha n)]
    exact eq_comm
  rw [hset, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Set.Finite.mem_toFinset, mem_ofPred_eq] at hn
  simp only [add_sub_cancel, Nat.cast_one]
  rw [← hn]
  exact analyticOrderAt_elementaryFactor_div (ha n) n

/-- An entire function without zeros is the exponential of an entire function. -/
theorem exists_exp_eq_of_differentiable {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hne : ∀ z, H z ≠ 0) : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, H z = exp (g z) := by
  have hq : Differentiable ℂ fun z => deriv H z / H z := (hH.deriv).div hH hne
  obtain ⟨g₀, hg₀⟩ := hq.isExactOn_univ
  have hg₀' : ∀ z, HasDerivAt g₀ (deriv H z / H z) z := fun z => hg₀ z (mem_univ z)
  have hdiff : Differentiable ℂ g₀ := fun z => (hg₀' z).differentiableAt
  -- `H * exp (-g₀)` is constant
  have hconst : ∀ z, H z * exp (-g₀ z) = H 0 * exp (-g₀ 0) := by
    intro z
    have hd : ∀ z, HasDerivAt (fun z => H z * exp (-g₀ z)) 0 z := by
      intro z
      have h1 := (hH z).hasDerivAt
      have h2 : HasDerivAt (fun z => exp (-g₀ z)) (exp (-g₀ z) * (-(deriv H z / H z))) z :=
        (hg₀' z).neg.cexp
      have h := h1.mul h2
      convert h using 1
      field_simp [hne z]
      ring
    exact is_const_of_deriv_eq_zero (fun z => (hd z).differentiableAt) (fun z => (hd z).deriv) z 0
  set c : ℂ := H 0 * exp (-g₀ 0) with hc_def
  have hc : c ≠ 0 := mul_ne_zero (hne 0) (exp_ne_zero _)
  refine ⟨fun z => g₀ z + log c, hdiff.add_const _, fun z => ?_⟩
  rw [exp_add, exp_log hc]
  have := hconst z
  calc H z = H z * exp (-g₀ z) * exp (g₀ z) := by
        rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    _ = exp (g₀ z) * c := by rw [this, mul_comm]

/-- If `f` and `P` are entire, `P` is not identically zero, and `f` and `P` have the same order
of vanishing at every point, then `f = H * P` with `H` entire and nowhere zero. -/
theorem exists_differentiable_ne_zero_mul_of_analyticOrderAt_eq {f P : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hP : Differentiable ℂ P) (hPne : ∃ z, P z ≠ 0)
    (hPord : ∀ w, analyticOrderAt P w = analyticOrderAt f w) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ z, H z ≠ 0) ∧ ∀ z, f z = H z * P z := by
  -- local factorization at every point
  have hloc : ∀ w, ∃ (m : ℕ) (f₁ P₁ : ℂ → ℂ), AnalyticAt ℂ f₁ w ∧ f₁ w ≠ 0 ∧
      AnalyticAt ℂ P₁ w ∧ P₁ w ≠ 0 ∧ (∀ᶠ z in 𝓝 w, f z = (z - w) ^ m * f₁ z) ∧
      ∀ᶠ z in 𝓝 w, P z = (z - w) ^ m * P₁ z := by
    intro w
    have hPtop : analyticOrderAt P w ≠ ⊤ := by
      obtain ⟨z₀, hz₀⟩ := hPne
      refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (fun z _ => hP.analyticAt z)
        isPreconnected_univ (mem_univ z₀) (mem_univ w) ?_
      rw [Ne, analyticOrderAt_eq_top]
      exact fun h => hz₀ h.self_of_nhds
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hPtop
    obtain ⟨f₁, hf₁, hf₁w, hfeq⟩ := ((hf.analyticAt w).analyticOrderAt_eq_natCast (n := m)).mp
      (by rw [← hPord w, ← hm]; rfl)
    obtain ⟨P₁, hP₁, hP₁w, hPeq⟩ :=
      ((Differentiable.analyticAt hP w).analyticOrderAt_eq_natCast).mp hm.symm
    exact ⟨m, f₁, P₁, hf₁, hf₁w, hP₁, hP₁w, by simpa [smul_eq_mul] using hfeq,
      by simpa [smul_eq_mul] using hPeq⟩
  -- the quotient `f / P` extends to an entire nonvanishing function
  have hPne' : ∃ z ∈ (univ : Set ℂ), P z ≠ 0 := by
    obtain ⟨z, hz⟩ := hPne
    exact ⟨z, mem_univ _, hz⟩
  have hquot : AnalyticOnNhd ℂ (fun z => f z / P z) (univ \ P ⁻¹' {0}) := fun z hz =>
    (hf.analyticAt z).div (Differentiable.analyticAt hP z) (by simpa using hz.2)
  obtain ⟨H, hH, hHeq⟩ := exists_analyticOnNhd_extension_zeroSet_oneVariable isOpen_univ
    isPreconnected_univ (fun z _ => Differentiable.analyticAt hP z) hPne' hquot (by
      intro w _ _
      obtain ⟨m, f₁, P₁, hf₁, hf₁w, hP₁, hP₁w, hfeq, hPeq⟩ := hloc w
      have hcont : ContinuousAt (fun z => f₁ z / P₁ z) w :=
        hf₁.continuousAt.div hP₁.continuousAt hP₁w
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
        ((hfeq.and hPeq).and (hcont.eventually (Metric.ball_mem_nhds _ one_pos)))
      refine ⟨r, hr, ‖f₁ w / P₁ w‖ + 1, fun z hz => ?_⟩
      obtain ⟨⟨hfz, hPz⟩, hclose⟩ := hball hz.1
      have hPz0 : P z ≠ 0 := by simpa using hz.2.2
      have hzw' : (z - w) ^ m ≠ 0 := fun h => hPz0 (by rw [hPz, h, zero_mul])
      have : f z / P z = f₁ z / P₁ z := by
        rw [hfz, hPz, mul_div_mul_left _ _ hzw']
      rw [this]
      have : ‖f₁ z / P₁ z - f₁ w / P₁ w‖ < 1 := by
        have := hclose
        rwa [dist_eq_norm] at this
      calc ‖f₁ z / P₁ z‖ = ‖(f₁ z / P₁ z - f₁ w / P₁ w) + f₁ w / P₁ w‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖f₁ z / P₁ z - f₁ w / P₁ w‖ + ‖f₁ w / P₁ w‖ := norm_add_le _ _
        _ ≤ 1 + ‖f₁ w / P₁ w‖ := by linarith
        _ = ‖f₁ w / P₁ w‖ + 1 := by ring)
  have hHdiff : Differentiable ℂ H := fun z => (hH z (mem_univ z)).differentiableAt
  -- `H` does not vanish
  have hHne : ∀ w, H w ≠ 0 := by
    intro w
    obtain ⟨m, f₁, P₁, hf₁, hf₁w, hP₁, hP₁w, hfeq, hPeq⟩ := hloc w
    have hev : ∀ᶠ z in 𝓝[≠] w, H z = f₁ z / P₁ z := by
      filter_upwards [nhdsWithin_le_nhds hfeq, nhdsWithin_le_nhds hPeq,
        nhdsWithin_le_nhds (hP₁.continuousAt.eventually_ne hP₁w), self_mem_nhdsWithin]
        with z hfz hPz hP₁z hzw
      have hzw' : z ≠ w := hzw
      have hPz0 : P z ≠ 0 := by
        rw [hPz]
        exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzw')) hP₁z
      rw [hHeq ⟨mem_univ _, by simpa using hPz0⟩]
      change f z / P z = f₁ z / P₁ z
      rw [hfz, hPz, mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr hzw'))]
    have hlim1 : Tendsto H (𝓝[≠] w) (𝓝 (H w)) :=
      ((hH w (mem_univ w)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto H (𝓝[≠] w) (𝓝 (f₁ w / P₁ w)) := by
      have := ((hf₁.continuousAt.div hP₁.continuousAt hP₁w).tendsto).mono_left
        (nhdsWithin_le_nhds (s := {w}ᶜ))
      exact this.congr' (hev.mono fun z hz => hz.symm)
    have hHw : H w = f₁ w / P₁ w := tendsto_nhds_unique hlim1 hlim2
    rw [hHw]
    exact div_ne_zero hf₁w hP₁w
  refine ⟨H, hHdiff, hHne, fun z => ?_⟩
  by_cases hPz : P z = 0
  · -- both sides vanish: `f z = 0` since the order of `f` at `z` is positive
    rw [hPz, mul_zero]
    have hord : analyticOrderAt f z ≠ 0 := by
      rw [← hPord z]
      intro h
      exact ((Differentiable.analyticAt hP z).analyticOrderAt_eq_zero).mp h hPz
    by_contra hfz
    exact hord (((hf.analyticAt z).analyticOrderAt_eq_zero).mpr hfz)
  · rw [hHeq ⟨mem_univ _, by simpa using hPz⟩]
    change f z = f z / P z * P z
    rw [div_mul_cancel₀ _ hPz]

/-- **Weierstrass factorization.** An entire function `f` with `f 0 ≠ 0` whose zeros, counted
with multiplicity, are exactly the terms of a sequence `a n → ∞` is `exp g` times the
Weierstrass product of the sequence, for some entire `g`. -/
theorem exists_exp_mul_weierstrassProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (ha : ∀ n, a n ≠ 0) (hlim : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hzero : ∀ w, analyticOrderAt f w = ((finite_setOf_eq_of_tendsto hlim w).toFinset.card : ℕ∞)) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = exp (g z) * weierstrassProduct a z := by
  set P := weierstrassProduct a with hP_def
  have hP : Differentiable ℂ P := differentiable_weierstrassProduct ha hlim
  have hPord : ∀ w, analyticOrderAt P w = analyticOrderAt f w := fun w => by
    rw [analyticOrderAt_weierstrassProduct ha hlim, hzero]
  obtain ⟨H, hHdiff, hHne, hfH⟩ :=
    exists_differentiable_ne_zero_mul_of_analyticOrderAt_eq hf hP ⟨0, by simp [P]⟩ hPord
  obtain ⟨g, hg, hHg⟩ := exists_exp_eq_of_differentiable hHdiff hHne
  exact ⟨g, hg, fun z => by rw [hfH z, hHg z]⟩

end Complex

end
