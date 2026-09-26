/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.WeierstrassProduct

/-!
# Canonical products of finite genus

For a family `a i` of nonzero complex numbers, indexed by an arbitrary type, with
`∑ ‖a i‖⁻¹ ^ (k + 1) < ∞`, the canonical product of genus `k` is `∏' i, E_k (z / a i)`. It is
entire, its zeros are exactly the `a i`, and its order of vanishing at `w` is the number of `i`
with `a i = w`. This is the product that appears in Hadamard's factorization theorem; unlike the
Weierstrass product, the genus is fixed.

## Main definitions

* `Complex.canonicalProduct k a z`.

## Main results

* `Complex.differentiable_canonicalProduct`, `Complex.canonicalProduct_eq_zero_iff`,
  `Complex.analyticOrderAt_canonicalProduct`.

## References

* E. M. Stein and R. Shakarchi, *Complex Analysis*, Chapter 5, Section 4.
* J. B. Conway, *Functions of One Complex Variable I*, Section XI.3.
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open scoped Topology

namespace Complex

variable {ι : Type*} {a : ι → ℂ} {k : ℕ}

/-- The canonical product of genus `k` with zeros `a i`.

A corresponding canonical-product construction appears in Matteo Cipollina's Hadamard
development. See `CREDITS.md`. -/
def canonicalProduct (k : ℕ) (a : ι → ℂ) (z : ℂ) : ℂ := ∏' i, elementaryFactor k (z / a i)

/-- For a family tending to infinity, only finitely many members lie in a bounded set. -/
theorem finite_setOf_norm_le_of_tendsto (hlim : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (R : ℝ) : {i | ‖a i‖ ≤ R}.Finite := by
  have h := hlim.eventually (eventually_gt_atTop R)
  rw [Filter.eventually_cofinite] at h
  exact h.subset fun i hi ↦ not_lt.mpr hi

/-- For a family tending to infinity, every value is taken finitely often. -/
theorem finite_setOf_eq_of_tendsto_cofinite (hlim : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    (w : ℂ) : {i | a i = w}.Finite :=
  (finite_setOf_norm_le_of_tendsto hlim ‖w‖).subset fun i hi ↦ by
    have : a i = w := hi
    simp [this]

/-- Summability of the inverse powers forces the family to tend to infinity. -/
theorem tendsto_norm_cofinite_of_summable (ha : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ ‖a i‖⁻¹ ^ (k + 1)) :
    Tendsto (fun i ↦ ‖a i‖) cofinite atTop := by
  have h := hs.tendsto_cofinite_zero
  rw [Filter.tendsto_atTop]
  intro b
  have hpos : 0 < (max b 1)⁻¹ ^ (k + 1) := by positivity
  filter_upwards [h.eventually (gt_mem_nhds hpos)] with i hi
  have h1 : ‖a i‖⁻¹ < (max b 1)⁻¹ := lt_of_pow_lt_pow_left₀ _ (by positivity) hi
  have h2 : max b 1 < ‖a i‖ := by
    rwa [inv_lt_inv₀ (norm_pos_iff.mpr (ha i)) (by positivity)] at h1
  exact (le_max_left b 1).trans h2.le

/-- The terms `E_k (z / a i) - 1` have summable uniform bounds on every compact set. -/
theorem hasSummableBoundOn_canonical (ha : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ ‖a i‖⁻¹ ^ (k + 1)) :
    HasSummableBoundOn (fun i z ↦ elementaryFactor k (z / a i) - 1) univ := by
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨fun i ↦ 4 * (max R 0) ^ (k + 1) * ‖a i‖⁻¹ ^ (k + 1),
    hs.mul_left (4 * (max R 0) ^ (k + 1)), ?_⟩
  have hlim := tendsto_norm_cofinite_of_summable ha hs
  filter_upwards [hlim.eventually (eventually_ge_atTop (2 * max R 0 + 1))] with i hi z hz
  have hzR : ‖z‖ ≤ max R 0 := (mem_closedBall_zero_iff.mp (hR hz)).trans (le_max_left _ _)
  have hw : ‖z / a i‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (ha i))]
    linarith [le_max_right R 0]
  calc ‖elementaryFactor k (z / a i) - 1‖ = ‖1 - elementaryFactor k (z / a i)‖ :=
        norm_sub_rev _ _
    _ ≤ 4 * ‖z / a i‖ ^ (k + 1) := norm_one_sub_elementaryFactor_le hw
    _ = 4 * (‖z‖ * ‖a i‖⁻¹) ^ (k + 1) := by rw [norm_div, div_eq_mul_inv]
    _ ≤ 4 * (max R 0 * ‖a i‖⁻¹) ^ (k + 1) := by gcongr
    _ = 4 * (max R 0) ^ (k + 1) * ‖a i‖⁻¹ ^ (k + 1) := by rw [mul_pow, mul_assoc]

/-- A canonical product can be written as a product of factors of the form `1 + f i z`. -/
theorem canonicalProduct_eq_tprod_one_add (z : ℂ) :
    canonicalProduct k a z = ∏' i, (1 + (elementaryFactor k (z / a i) - 1)) := by
  simp [canonicalProduct]

/-- An elementary factor composed with division by a fixed parameter, and then shifted by minus one,
is entire. -/
theorem differentiableOn_elementaryFactor_div (i : ι) (k : ℕ) :
    DifferentiableOn ℂ (fun z ↦ elementaryFactor k (z / a i) - 1) univ :=
  (((differentiable_elementaryFactor k).comp (differentiable_id.div_const _)).sub
    (differentiable_const 1)).differentiableOn

/-- The canonical product is entire.

A corresponding canonical-product construction appears in Matteo Cipollina's Hadamard
development. See `CREDITS.md`. -/
theorem differentiable_canonicalProduct (ha : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ ‖a i‖⁻¹ ^ (k + 1)) :
    Differentiable ℂ (canonicalProduct k a) := by
  rw [← differentiableOn_univ]
  have : canonicalProduct k a = fun z ↦ ∏' i, (1 + (elementaryFactor k (z / a i) - 1)) :=
    funext canonicalProduct_eq_tprod_one_add
  rw [this]
  exact differentiableOn_tprod_one_add isOpen_univ (fun i ↦ differentiableOn_elementaryFactor_div
    i k) (hasSummableBoundOn_canonical ha hs)

/-- The zeros of the canonical product are exactly the `a i`. -/
theorem canonicalProduct_eq_zero_iff (ha : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ ‖a i‖⁻¹ ^ (k + 1)) (z : ℂ) :
    canonicalProduct k a z = 0 ↔ ∃ i, z = a i := by
  rw [canonicalProduct_eq_tprod_one_add,
    tprod_one_add_eq_zero_iff (hasSummableBoundOn_canonical ha hs) (mem_univ z)]
  simp only [add_sub_cancel, elementaryFactor_eq_zero_iff]
  refine exists_congr fun i ↦ ?_
  rw [div_eq_one_iff_eq (ha i)]

/-- The canonical product has value one at the origin. -/
@[simp] theorem canonicalProduct_zero (k : ℕ) (a : ι → ℂ) : canonicalProduct k a 0 = 1 := by
  simp [canonicalProduct]

/-- **Orders of the canonical product.** The order at `w` is the number of `i` with `a i = w`. -/
theorem analyticOrderAt_canonicalProduct (ha : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ ‖a i‖⁻¹ ^ (k + 1)) (w : ℂ) :
    analyticOrderAt (canonicalProduct k a) w =
      ((finite_setOf_eq_of_tendsto_cofinite (tendsto_norm_cofinite_of_summable ha hs)
        w).toFinset.card : ℕ∞) := by
  classical
  have hb := hasSummableBoundOn_canonical ha hs
  have hfun : canonicalProduct k a = fun z ↦ ∏' i, (1 + (elementaryFactor k (z / a i) - 1)) :=
    funext canonicalProduct_eq_tprod_one_add
  rw [hfun, analyticOrderAt_tprod_one_add isOpen_univ
    (fun i ↦ differentiableOn_elementaryFactor_div i k) hb (mem_univ w)]
  have hset : (finite_setOf_one_add_eq_zero hb (mem_univ w)).toFinset =
      (finite_setOf_eq_of_tendsto_cofinite (tendsto_norm_cofinite_of_summable ha hs)
        w).toFinset := by
    ext i
    simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, add_sub_cancel,
      elementaryFactor_eq_zero_iff, div_eq_one_iff_eq (ha i)]
    exact eq_comm
  rw [hset, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Set.Finite.mem_toFinset, mem_ofPred_eq] at hi
  simp only [add_sub_cancel, Nat.cast_one]
  rw [← hi]
  exact analyticOrderAt_elementaryFactor_div (ha i) k

end Complex

end
