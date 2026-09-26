/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.InfiniteProduct
public import ComplexAnalysis.WeierstrassFactor
public import ComplexAnalysis.AnalyticOrder
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
theorem finite_setOf_eq_of_tendsto (hlim : Tendsto (fun n ↦ ‖a n‖) atTop atTop) (w : ℂ) :
    {n | a n = w}.Finite := by
  have h := hlim.eventually (eventually_gt_atTop ‖w‖)
  rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at h
  refine h.subset fun n hn ↦ ?_
  have hn' : a n = w := hn
  simp [hn']

/-- The terms `E n (z / a n) - 1` have summable uniform bounds on every compact set. -/
theorem hasSummableBoundOn_weierstrass (ha : ∀ n, a n ≠ 0)
    (hlim : Tendsto (fun n ↦ ‖a n‖) atTop atTop) :
    HasSummableBoundOn (fun n z ↦ elementaryFactor n (z / a n) - 1) univ := by
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨fun n ↦ 4 * (1 / 2 : ℝ) ^ (n + 1), ?_, ?_⟩
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
    (hlim : Tendsto (fun n ↦ ‖a n‖) atTop atTop) :
    Differentiable ℂ (weierstrassProduct a) := by
  rw [← differentiableOn_univ]
  have : weierstrassProduct a = fun z ↦ ∏' n, (1 + (elementaryFactor n (z / a n) - 1)) :=
    funext weierstrassProduct_eq_tprod_one_add
  rw [this]
  refine differentiableOn_tprod_one_add isOpen_univ (fun n ↦ ?_)
    (hasSummableBoundOn_weierstrass ha hlim)
  exact ((differentiable_elementaryFactor n).comp (differentiable_id.div_const _)).sub
    (differentiable_const 1) |>.differentiableOn

/-- The zeros of the Weierstrass product are exactly the `a n`. -/
theorem weierstrassProduct_eq_zero_iff (ha : ∀ n, a n ≠ 0)
    (hlim : Tendsto (fun n ↦ ‖a n‖) atTop atTop) (z : ℂ) :
    weierstrassProduct a z = 0 ↔ ∃ n, z = a n := by
  rw [weierstrassProduct_eq_tprod_one_add,
    tprod_one_add_eq_zero_iff (hasSummableBoundOn_weierstrass ha hlim) (mem_univ z)]
  simp only [add_sub_cancel, elementaryFactor_eq_zero_iff]
  refine exists_congr fun n ↦ ?_
  rw [div_eq_one_iff_eq (ha n)]

/-- The Weierstrass product has value one at the origin. -/
@[simp] theorem weierstrassProduct_zero (a : ℕ → ℂ) : weierstrassProduct a 0 = 1 := by
  simp [weierstrassProduct]

/-- The elementary factor rescaled to vanish at `c` has order one there. -/
theorem analyticOrderAt_elementaryFactor_div {c : ℂ} (hc : c ≠ 0) (p : ℕ) :
    analyticOrderAt (fun z ↦ elementaryFactor p (z / c)) c = 1 := by
  have hfun : (fun z ↦ elementaryFactor p (z / c)) =
      (fun z ↦ (-c⁻¹ : ℂ) * (z - c)) * fun z ↦ exp (elementaryExponent p (z / c)) := by
    ext z
    simp only [elementaryFactor_eq, Pi.mul_apply]
    congr 1
    field_simp
    ring
  have hexp : AnalyticAt ℂ (fun z ↦ exp (elementaryExponent p (z / c))) c :=
    (((differentiable_elementaryExponent p).comp (differentiable_id.div_const c)).analyticAt
      c).cexp
  rw [hfun, analyticOrderAt_mul (by fun_prop) hexp,
    (hexp.analyticOrderAt_eq_zero).mpr (exp_ne_zero _), add_zero]
  change analyticOrderAt ((fun _ ↦ (-c⁻¹ : ℂ)) * fun z ↦ z - c) c = 1
  rw [analyticOrderAt_mul analyticAt_const (by fun_prop),
    (analyticAt_const.analyticOrderAt_eq_zero).mpr (by simpa using hc), zero_add]
  exact analyticOrderAt_id_sub_const_self

/-- **Orders of the Weierstrass product.** The order at `w` is the number of `n` with
`a n = w`. -/
theorem analyticOrderAt_weierstrassProduct (ha : ∀ n, a n ≠ 0)
    (hlim : Tendsto (fun n ↦ ‖a n‖) atTop atTop) (w : ℂ) :
    analyticOrderAt (weierstrassProduct a) w =
      ((finite_setOf_eq_of_tendsto hlim w).toFinset.card : ℕ∞) := by
  classical
  have hb := hasSummableBoundOn_weierstrass ha hlim
  have hf : ∀ n, DifferentiableOn ℂ (fun z ↦ elementaryFactor n (z / a n) - 1) univ := fun n ↦
    (((differentiable_elementaryFactor n).comp (differentiable_id.div_const _)).sub
      (differentiable_const 1)).differentiableOn
  have hfun : weierstrassProduct a = fun z ↦ ∏' n, (1 + (elementaryFactor n (z / a n) - 1)) :=
    funext weierstrassProduct_eq_tprod_one_add
  rw [hfun, analyticOrderAt_tprod_one_add isOpen_univ hf hb (mem_univ w)]
  have hset : (finite_setOf_one_add_eq_zero hb (mem_univ w)).toFinset =
      (finite_setOf_eq_of_tendsto hlim w).toFinset := by
    ext n
    simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, add_sub_cancel,
      elementaryFactor_eq_zero_iff, div_eq_one_iff_eq (ha n)]
    exact eq_comm
  rw [hset, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [Set.Finite.mem_toFinset, mem_ofPred_eq] at hn
  simp only [add_sub_cancel, Nat.cast_one]
  rw [← hn]
  exact analyticOrderAt_elementaryFactor_div (ha n) n

/-- An entire function without zeros is the exponential of an entire function. -/
theorem exists_exp_eq_of_differentiable {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hne : ∀ z, H z ≠ 0) : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, H z = exp (g z) := by
  have hq : Differentiable ℂ fun z ↦ deriv H z / H z := (hH.deriv).div hH hne
  obtain ⟨g₀, hg₀⟩ := hq.isExactOn_univ
  have hg₀' : ∀ z, HasDerivAt g₀ (deriv H z / H z) z := fun z ↦ hg₀ z (mem_univ z)
  have hdiff : Differentiable ℂ g₀ := fun z ↦ (hg₀' z).differentiableAt
  -- `H * exp (-g₀)` is constant
  have hconst : ∀ z, H z * exp (-g₀ z) = H 0 * exp (-g₀ 0) := by
    intro z
    have hd : ∀ z, HasDerivAt (fun z ↦ H z * exp (-g₀ z)) 0 z := by
      intro z
      have h1 := (hH z).hasDerivAt
      have h2 : HasDerivAt (fun z ↦ exp (-g₀ z)) (exp (-g₀ z) * (-(deriv H z / H z))) z :=
        (hg₀' z).neg.cexp
      have h := h1.mul h2
      convert h using 1
      field_simp [hne z]
      ring
    exact is_const_of_deriv_eq_zero (fun z ↦ (hd z).differentiableAt) (fun z ↦ (hd z).deriv) z 0
  set c : ℂ := H 0 * exp (-g₀ 0)
  have hc : c ≠ 0 := mul_ne_zero (hne 0) (exp_ne_zero _)
  refine ⟨fun z ↦ g₀ z + log c, hdiff.add_const _, fun z ↦ ?_⟩
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
  obtain ⟨z₀, hz₀⟩ := hPne
  obtain ⟨H, hH, hHne, hfH⟩ := AnalyticOnNhd.exists_ne_zero_mul_of_analyticOrderAt_eq
    (U := univ) (fun z _ ↦ hf.analyticAt z) (fun z _ ↦ hP.analyticAt z) isOpen_univ
    isPreconnected_univ ⟨z₀, mem_univ _, hz₀⟩ fun w _ ↦ hPord w
  exact ⟨H, fun z ↦ (hH z (mem_univ z)).differentiableAt, fun z ↦ hHne z (mem_univ z),
    fun z ↦ hfH z (mem_univ z)⟩

/-- **Weierstrass factorization.** An entire function `f` with `f 0 ≠ 0` whose zeros, counted
with multiplicity, are exactly the terms of a sequence `a n → ∞` is `exp g` times the
Weierstrass product of the sequence, for some entire `g`. -/
theorem exists_exp_mul_weierstrassProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (ha : ∀ n, a n ≠ 0) (hlim : Tendsto (fun n ↦ ‖a n‖) atTop atTop)
    (hzero : ∀ w, analyticOrderAt f w = ((finite_setOf_eq_of_tendsto hlim w).toFinset.card : ℕ∞)) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = exp (g z) * weierstrassProduct a z := by
  set P := weierstrassProduct a
  have hP : Differentiable ℂ P := differentiable_weierstrassProduct ha hlim
  have hPord : ∀ w, analyticOrderAt P w = analyticOrderAt f w := fun w ↦ by
    rw [analyticOrderAt_weierstrassProduct ha hlim, hzero]
  obtain ⟨H, hHdiff, hHne, hfH⟩ :=
    exists_differentiable_ne_zero_mul_of_analyticOrderAt_eq hf hP ⟨0, by simp [P]⟩ hPord
  obtain ⟨g, hg, hHg⟩ := exists_exp_eq_of_differentiable hHdiff hHne
  exact ⟨g, hg, fun z ↦ by rw [hfH z, hHg z]⟩

end Complex

end
