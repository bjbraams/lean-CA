/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Weierstrass elementary factors

The elementary factor `E p z = (1 - z) exp (z + z²/2 + ⋯ + zᵖ/p)` is entire, vanishes exactly
at `z = 1`, to first order, and satisfies `‖1 - E p z‖ ≤ 4 ‖z‖ ^ (p + 1)` for `‖z‖ ≤ 1 / 2`,
uniformly in `p`. The estimate comes from `E p z = exp (-∑_{k > p} zᵏ / k)` and the bounds
`‖exp w - 1‖ ≤ 2 ‖w‖` for `‖w‖ ≤ 1`.

## Main definitions

* `Complex.elementaryFactor p z`.

## Main results

* `Complex.norm_one_sub_elementaryFactor_le`: the uniform estimate.
* `Complex.elementaryFactor_eq_zero_iff`, `Complex.analyticOrderAt_elementaryFactor_one`.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Lemma VII.5.11 (with the constant `1`
  for `‖z‖ ≤ 1`, which is not needed here).
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open scoped Topology

namespace Complex

/-- The Weierstrass elementary factor `E p z = (1 - z) exp (∑_{k < p} z ^ (k + 1) / (k + 1))`.

The same factor is formalized in Matteo Cipollina's Hadamard development. See `CREDITS.md`. -/
def elementaryFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))

/-- The exponent polynomial of the elementary factor. -/
def elementaryExponent (p : ℕ) (z : ℂ) : ℂ := ∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)

/-- A Weierstrass elementary factor is `1 - z` multiplied by the exponential of its correcting
polynomial. -/
theorem elementaryFactor_eq (p : ℕ) (z : ℂ) :
    elementaryFactor p z = (1 - z) * exp (elementaryExponent p z) := rfl

/-- The polynomial exponent of a Weierstrass elementary factor is entire. -/
theorem differentiable_elementaryExponent (p : ℕ) : Differentiable ℂ (elementaryExponent p) := by
  unfold elementaryExponent
  fun_prop

/-- Every Weierstrass elementary factor is entire. -/
theorem differentiable_elementaryFactor (p : ℕ) : Differentiable ℂ (elementaryFactor p) := by
  unfold elementaryFactor
  fun_prop

/-- Every Weierstrass elementary factor is analytic at every complex point. -/
theorem analyticAt_elementaryFactor (p : ℕ) (z : ℂ) : AnalyticAt ℂ (elementaryFactor p) z :=
  (differentiable_elementaryFactor p).analyticAt z

/-- A Weierstrass elementary factor vanishes exactly at one. -/
theorem elementaryFactor_eq_zero_iff (p : ℕ) (z : ℂ) : elementaryFactor p z = 0 ↔ z = 1 := by
  rw [elementaryFactor, mul_eq_zero, or_iff_left (exp_ne_zero _), sub_eq_zero, eq_comm]

/-- A Weierstrass elementary factor takes the value one at zero. -/
@[simp] theorem elementaryFactor_zero_apply (p : ℕ) : elementaryFactor p 0 = 1 := by
  simp [elementaryFactor]

/-- The elementary factor vanishes to first order at `1`. -/
theorem analyticOrderAt_elementaryFactor_one (p : ℕ) :
    analyticOrderAt (elementaryFactor p) 1 = 1 := by
  have h1 : (fun z : ℂ ↦ 1 - z) = fun z ↦ (-1 : ℂ) * (z - 1) := by
    ext z
    ring
  have hexp : AnalyticAt ℂ (fun z ↦ exp (elementaryExponent p z)) 1 :=
    ((differentiable_elementaryExponent p).analyticAt 1).cexp
  have hfun : elementaryFactor p = (fun z ↦ 1 - z) * fun z ↦ exp (elementaryExponent p z) :=
    funext fun z ↦ elementaryFactor_eq p z
  rw [hfun]
  rw [analyticOrderAt_mul (by fun_prop) hexp, (hexp.analyticOrderAt_eq_zero).mpr (exp_ne_zero _),
    add_zero, h1]
  change analyticOrderAt ((fun _ ↦ (-1 : ℂ)) * fun z ↦ z - 1) 1 = 1
  rw [analyticOrderAt_mul analyticAt_const (by fun_prop),
    (analyticAt_const.analyticOrderAt_eq_zero).mpr (by norm_num), zero_add]
  exact analyticOrderAt_id_sub_const_self

/-- The power series of `-log (1 - z)`. -/
theorem hasSum_pow_div_neg_log_one_sub {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ z ^ n / n) (-log (1 - z)) := by
  have h := hasSum_taylorSeries_log (z := -z) (by simpa using hz)
  rw [show (1 : ℂ) + -z = 1 - z by ring] at h
  have h' := h.neg
  refine h'.congr_fun fun n ↦ ?_
  rw [neg_pow z n, ← mul_assoc, ← pow_add, show n + 1 + n = 2 * n + 1 by ring, pow_succ,
    pow_mul, neg_one_sq, one_pow, one_mul]
  ring

/-- The elementary factor as an exponential of the tail of the logarithmic series. -/
theorem elementaryFactor_eq_exp_neg_tsum {p : ℕ} {z : ℂ} (hz : ‖z‖ < 1) :
    elementaryFactor p z = exp (-∑' n : ℕ, z ^ (n + (p + 1)) / (n + (p + 1) : ℕ)) := by
  have hz1 : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz
    exact lt_irrefl _ hz
  have hsum := hasSum_pow_div_neg_log_one_sub hz
  have hsplit := hsum.summable.sum_add_tsum_nat_add (p + 1)
  rw [hsum.tsum_eq] at hsplit
  have hhead : ∑ i ∈ Finset.range (p + 1), z ^ i / (i : ℂ) = elementaryExponent p z := by
    rw [Finset.sum_range_succ', elementaryExponent]
    simp only [pow_zero, Nat.cast_zero, div_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    push_cast
    ring
  rw [hhead] at hsplit
  rw [elementaryFactor_eq]
  have hlog : (1 : ℂ) - z = exp (log (1 - z)) := (exp_log hz1).symm
  rw [hlog, ← exp_add]
  congr 1
  have : ∑' i : ℕ, z ^ (i + (p + 1)) / ((i + (p + 1) : ℕ) : ℂ) = -log (1 - z) -
      elementaryExponent p z := by linear_combination hsplit
  rw [this]
  ring

/-- The tail of the logarithmic series is small: for `‖z‖ ≤ 1 / 2`,
`‖∑' n, z ^ (n + (p + 1)) / (n + (p + 1))‖ ≤ 2 ‖z‖ ^ (p + 1)`. -/
theorem norm_tsum_pow_div_tail_le {p : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖∑' n : ℕ, z ^ (n + (p + 1)) / ((n + (p + 1) : ℕ) : ℂ)‖ ≤ 2 * ‖z‖ ^ (p + 1) := by
  have hz1 : ‖z‖ < 1 := by linarith
  set T : ℂ := ∑' n : ℕ, z ^ (n + (p + 1)) / ((n + (p + 1) : ℕ) : ℂ)
  have hterm : ∀ n : ℕ, ‖z ^ (n + (p + 1)) / ((n + (p + 1) : ℕ) : ℂ)‖ ≤ ‖z‖ ^ (n + (p + 1)) := by
    intro n
    rw [norm_div, norm_pow, Complex.norm_natCast]
    have hn : (1 : ℝ) ≤ (n + (p + 1) : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    exact div_le_self (by positivity) hn
  have hgeom : Summable fun n : ℕ ↦ ‖z‖ ^ (n + (p + 1)) :=
    (summable_geometric_of_lt_one (norm_nonneg _) hz1).comp_injective
      (add_left_injective (p + 1))
  have hsumnorm : Summable fun n : ℕ ↦ ‖z ^ (n + (p + 1)) / ((n + (p + 1) : ℕ) : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hterm hgeom
  have hTbound : ‖T‖ ≤ 2 * ‖z‖ ^ (p + 1) := by
    calc ‖T‖ ≤ ∑' n : ℕ, ‖z ^ (n + (p + 1)) / ((n + (p + 1) : ℕ) : ℂ)‖ :=
          norm_tsum_le_tsum_norm hsumnorm
      _ ≤ ∑' n : ℕ, ‖z‖ ^ (n + (p + 1)) := hsumnorm.tsum_le_tsum hterm hgeom
      _ = ‖z‖ ^ (p + 1) * ∑' n : ℕ, ‖z‖ ^ n := by
          rw [← tsum_mul_left]
          congr 1
          ext n
          rw [pow_add, mul_comm]
      _ = ‖z‖ ^ (p + 1) * (1 - ‖z‖)⁻¹ := by
          rw [tsum_geometric_of_lt_one (norm_nonneg _) hz1]
      _ ≤ ‖z‖ ^ (p + 1) * 2 := by
          gcongr
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
      _ = 2 * ‖z‖ ^ (p + 1) := by ring
  exact hTbound

/-- **The uniform estimate for elementary factors.** For `‖z‖ ≤ 1 / 2`,
`‖1 - E p z‖ ≤ 4 ‖z‖ ^ (p + 1)`.

The same estimate, with constant 4, appears in Matteo Cipollina's Hadamard development. See
`CREDITS.md`. -/
theorem norm_one_sub_elementaryFactor_le {p : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖1 - elementaryFactor p z‖ ≤ 4 * ‖z‖ ^ (p + 1) := by
  have hz1 : ‖z‖ < 1 := by linarith
  rw [elementaryFactor_eq_exp_neg_tsum hz1]
  set T : ℂ := ∑' n : ℕ, z ^ (n + (p + 1)) / ((n + (p + 1) : ℕ) : ℂ)
  have hTbound : ‖T‖ ≤ 2 * ‖z‖ ^ (p + 1) := norm_tsum_pow_div_tail_le hz
  have hzp : ‖z‖ ^ (p + 1) ≤ 1 / 2 := by
    calc ‖z‖ ^ (p + 1) ≤ (1 / 2 : ℝ) ^ (p + 1) := pow_le_pow_left₀ (norm_nonneg _) hz _
      _ ≤ 1 / 2 := by
          calc (1 / 2 : ℝ) ^ (p + 1) ≤ (1 / 2) ^ 1 :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ = 1 / 2 := pow_one _
  have hT1 : ‖-T‖ ≤ 1 := by
    rw [norm_neg]
    linarith
  calc ‖1 - exp (-T)‖ = ‖exp (-T) - 1‖ := norm_sub_rev _ _
    _ ≤ 2 * ‖-T‖ := norm_exp_sub_one_le hT1
    _ = 2 * ‖T‖ := by rw [norm_neg]
    _ ≤ 2 * (2 * ‖z‖ ^ (p + 1)) := by gcongr
    _ = 4 * ‖z‖ ^ (p + 1) := by ring

/-- **Lower bound near the origin.** For `‖z‖ ≤ 1 / 2`, `exp (-(2 ‖z‖ ^ (p + 1))) ≤ ‖E p z‖`. -/
theorem exp_neg_le_norm_elementaryFactor {p : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    Real.exp (-(2 * ‖z‖ ^ (p + 1))) ≤ ‖elementaryFactor p z‖ := by
  have hz1 : ‖z‖ < 1 := by linarith
  rw [elementaryFactor_eq_exp_neg_tsum hz1, norm_exp, neg_re]
  apply Real.exp_le_exp.mpr
  have h1 := norm_tsum_pow_div_tail_le (p := p) hz
  have h2 := re_le_norm (∑' n : ℕ, z ^ (n + (p + 1)) / ((n + (p + 1) : ℕ) : ℂ))
  linarith

/-- **Lower bound away from the origin.** For `1 / 2 ≤ ‖z‖`,
`‖1 - z‖ exp (-(2 ^ p p ‖z‖ ^ p)) ≤ ‖E p z‖`. -/
theorem norm_one_sub_mul_exp_neg_le_norm_elementaryFactor {p : ℕ} {z : ℂ} (hz : 1 / 2 ≤ ‖z‖) :
    ‖1 - z‖ * Real.exp (-(2 ^ p * p * ‖z‖ ^ p)) ≤ ‖elementaryFactor p z‖ := by
  rw [elementaryFactor_eq, norm_mul, norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hterm : ∀ k ∈ Finset.range p, ‖z ^ (k + 1) / (k + 1 : ℂ)‖ ≤ 2 ^ p * ‖z‖ ^ p := by
    intro k hk
    have hkp : k + 1 ≤ p := Finset.mem_range.mp hk
    rw [norm_div, norm_pow]
    have h1 : (1 : ℝ) ≤ ‖(k + 1 : ℂ)‖ := by
      rw [show (k + 1 : ℂ) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, norm_natCast]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have h2 : ‖z‖ ^ (k + 1) ≤ 2 ^ p * ‖z‖ ^ p := by
      have h3 : (1 / 2 : ℝ) ^ (p - (k + 1)) ≤ ‖z‖ ^ (p - (k + 1)) :=
        pow_le_pow_left₀ (by norm_num) hz _
      have h4 : (1 / 2 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ (p - (k + 1)) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.sub_le p (k + 1))
      have h5 : ‖z‖ ^ (k + 1) * ‖z‖ ^ (p - (k + 1)) = ‖z‖ ^ p := by
        rw [← pow_add, Nat.add_sub_cancel' hkp]
      have h6 : (1 / 2 : ℝ) ^ p * ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ p := by
        calc (1 / 2 : ℝ) ^ p * ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ (p - (k + 1)) * ‖z‖ ^ (k + 1) :=
              mul_le_mul_of_nonneg_right (h4.trans h3) (by positivity)
          _ = ‖z‖ ^ p := by rw [mul_comm, h5]
      have h7 : (2 : ℝ) ^ p * (1 / 2 : ℝ) ^ p = 1 := by
        rw [← mul_pow]
        norm_num
      calc ‖z‖ ^ (k + 1) = 2 ^ p * ((1 / 2 : ℝ) ^ p * ‖z‖ ^ (k + 1)) := by
            rw [← mul_assoc, h7, one_mul]
        _ ≤ 2 ^ p * ‖z‖ ^ p := mul_le_mul_of_nonneg_left h6 (by positivity)
    calc ‖z‖ ^ (k + 1) / ‖(k + 1 : ℂ)‖ ≤ ‖z‖ ^ (k + 1) := div_le_self (by positivity) h1
      _ ≤ 2 ^ p * ‖z‖ ^ p := h2
  have hnorm : ‖elementaryExponent p z‖ ≤ 2 ^ p * p * ‖z‖ ^ p := by
    unfold elementaryExponent
    calc ‖∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1 : ℂ)‖
        ≤ ∑ k ∈ Finset.range p, ‖z ^ (k + 1) / (k + 1 : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range p, 2 ^ p * ‖z‖ ^ p := Finset.sum_le_sum hterm
      _ = 2 ^ p * p * ‖z‖ ^ p := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have := abs_re_le_norm (elementaryExponent p z)
  linarith [neg_abs_le (elementaryExponent p z).re]

end Complex

end
