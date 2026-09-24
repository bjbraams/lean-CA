/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CanonicalProduct
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Entire functions of finite order

An entire function `f` has order at most `ρ` if `‖f z‖ ≤ A exp (B ‖z‖ ^ ρ)` for some constants
`A, B ≥ 0`. Jensen's inequality (Mathlib) bounds the number of zeros of `f` in the disc of radius
`r` by a constant times `r ^ ρ`, and a dyadic shell argument turns this counting bound into the
summability of `‖a i‖ ^ (-s)` over the zeros `a i` for every `s > ρ`. These are the ingredients
of Hadamard's factorization theorem.

## Main definitions

* `Complex.HasOrderLE f ρ`.

## Main results

* `Complex.sum_divisor_le_of_hasOrderLE`: Jensen's zero-counting bound.
* `Complex.ncard_setOf_norm_le_eq_sum_divisor`: the counting function of a family enumerating
  the zeros with multiplicity is the divisor degree.
* `Complex.summable_norm_rpow_neg_of_ncard_le`: summability of `‖a i‖ ^ (-s)` for `s > ρ`.
* `Complex.summable_norm_rpow_neg_of_hasOrderLE`: the same for the zeros of a function of order
  at most `ρ`.

## References

* E. M. Stein and R. Shakarchi, *Complex Analysis*, Chapter 5, Sections 1–2.
* S. Lang, *Complex Analysis*, Chapter XIII, Section 3.
-/

@[expose] public noncomputable section

open Set Metric Filter Function MeromorphicOn
open scoped Topology

namespace Complex

/-- `f` has order at most `ρ`: `‖f z‖ ≤ A * exp (B * ‖z‖ ^ ρ)` for all `z`, for some constants
`A, B ≥ 0`. -/
def HasOrderLE (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)

variable {f : ℂ → ℂ} {ρ : ℝ}

/-- The order bound is monotone in the exponent. -/
theorem HasOrderLE.mono (h : HasOrderLE f ρ) {ρ' : ℝ} (hρ : 0 ≤ ρ) (hρρ' : ρ ≤ ρ') :
    HasOrderLE f ρ' := by
  obtain ⟨A, B, hA, hB, h⟩ := h
  refine ⟨A * Real.exp B, B, by positivity, hB, fun z => ?_⟩
  have h1 : ‖z‖ ^ ρ ≤ 1 + ‖z‖ ^ ρ' := by
    rcases le_or_gt ‖z‖ 1 with hz | hz
    · have : ‖z‖ ^ ρ ≤ 1 := Real.rpow_le_one (norm_nonneg _) hz hρ
      linarith [Real.rpow_nonneg (norm_nonneg z) ρ']
    · have := Real.rpow_le_rpow_of_exponent_le hz.le hρρ'
      linarith
  calc ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ) := h z
    _ ≤ A * Real.exp (B * (1 + ‖z‖ ^ ρ')) := by gcongr
    _ = A * Real.exp B * Real.exp (B * ‖z‖ ^ ρ') := by
        rw [mul_add, mul_one, Real.exp_add, mul_assoc]

/-- **Jensen's zero-counting bound.** For an entire function with `f 0 ≠ 0` and
`‖f z‖ ≤ A exp (B ‖z‖ ^ ρ)`, the divisor degree on the disc of radius `r` is at most
`(log (max 1 (A exp (B (2r) ^ ρ))) - log ‖f 0‖) / log 2`.

A counterpart under a related growth hypothesis appears in Matteo Cipollina's Hadamard
development. See `CREDITS.md`. -/
theorem sum_divisor_le_of_hasOrderLE (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {A B : ℝ}
    (hbound : ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)) {r : ℝ} (hr : 0 < r) :
    ((∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u : ℤ) : ℝ) ≤
      (Real.log (max 1 (A * Real.exp (B * (2 * r) ^ ρ))) - Real.log ‖f 0‖) / Real.log 2 := by
  set M : ℝ := max 1 (A * Real.exp (B * (2 * r) ^ ρ)) with hM_def
  have hM : 1 ≤ M := le_max_left _ _
  have h2r : 0 < 2 * r := by linarith
  have key := AnalyticOnNhd.sum_divisor_le (c := 0) (r := r) (R := 2 * r) (M := M)
    (by rwa [abs_of_pos hr]) (by rw [abs_of_pos hr, abs_of_pos h2r]; linarith) hM
    (fun z _ => hf.analyticAt z) h0 (fun z hz => ?_)
  · rw [abs_of_pos hr] at key
    rwa [Real.log_div (by positivity) (norm_ne_zero_iff.mpr h0),
      show (2 * r) / r = 2 by field_simp] at key
  · rw [mem_sphere_zero_iff_norm, abs_of_pos h2r] at hz
    calc ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ) := hbound z
      _ = A * Real.exp (B * (2 * r) ^ ρ) := by rw [hz]
      _ ≤ M := le_max_right _ _

variable {ι : Type*} {a : ι → ℂ}

/-- For a family `a` of nonzero points enumerating the zeros of `f` with multiplicity, the
number of `i` with `‖a i‖ ≤ r` is the divisor degree of `f` on the closed disc of radius `r`. -/
theorem ncard_setOf_norm_le_eq_sum_divisor (hf : Differentiable ℂ f)
    (hlim : Tendsto (fun i => ‖a i‖) cofinite atTop)
    (hzero : ∀ w, analyticOrderAt f w =
      ((finite_setOf_eq_of_tendsto_cofinite hlim w).toFinset.card : ℕ∞)) (r : ℝ) :
    (({i | ‖a i‖ ≤ r}.ncard : ℤ)) = ∑ᶠ u, MeromorphicOn.divisor f (closedBall 0 r) u := by
  classical
  set F := (finite_setOf_norm_le_of_tendsto hlim r).toFinset with hF_def
  have hfan : AnalyticOnNhd ℂ f (closedBall 0 r) := fun z _ => hf.analyticAt z
  have hD : ∀ u, MeromorphicOn.divisor f (closedBall 0 r) u =
      ((F.filter (fun i => a i = u)).card : ℤ) := by
    intro u
    by_cases hu : u ∈ closedBall 0 r
    · rw [AnalyticOnNhd.divisor_apply hfan hu, hzero u]
      have : (finite_setOf_eq_of_tendsto_cofinite hlim u).toFinset =
          F.filter (fun i => a i = u) := by
        ext i
        simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, Finset.mem_filter, hF_def]
        constructor
        · intro h
          exact ⟨by rw [h]; exact mem_closedBall_zero_iff.mp hu, h⟩
        · exact fun h => h.2
      rw [this]
      simp
    · rw [Function.notMem_support.mp fun h =>
        hu ((MeromorphicOn.divisor _ _).supportWithinDomain h)]
      have : F.filter (fun i => a i = u) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, hF_def,
          Set.Finite.mem_toFinset, mem_ofPred_eq]
        intro hi hiu
        exact hu (mem_closedBall_zero_iff.mpr (hiu ▸ hi))
      rw [this]
      simp
  have hsupp : support (fun u => MeromorphicOn.divisor f (closedBall 0 r) u) ⊆
      ↑(F.image a) := by
    intro u hu
    rw [mem_support, hD u] at hu
    have : (F.filter (fun i => a i = u)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      apply hu
      rw [h]
      simp
    obtain ⟨i, hi⟩ := this
    rw [Finset.mem_filter] at hi
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hi.1, hi.2⟩)
  rw [finsum_eq_sum_of_support_subset _ hsupp, Set.ncard_eq_toFinset_card _
    (finite_setOf_norm_le_of_tendsto hlim r)]
  change ((F.card : ℕ) : ℤ) = _
  rw [Finset.card_eq_sum_card_fiberwise (f := a) (t := F.image a)
    fun i hi => Finset.mem_image_of_mem a hi]
  push_cast
  exact Finset.sum_congr rfl fun u _ => (hD u).symm

/-- **Summability from a counting bound.** If the number of `i` with `‖a i‖ ≤ r` is at most
`C r ^ ρ` for `r ≥ 1`, then `∑ ‖a i‖ ^ (-s)` converges for every `s > ρ`. -/
theorem summable_norm_rpow_neg_of_ncard_le
    (hlim : Tendsto (fun i => ‖a i‖) cofinite atTop) {ρ C : ℝ} (hρ : 0 ≤ ρ) (hC : 0 ≤ C)
    (hN : ∀ r, 1 ≤ r → ({i | ‖a i‖ ≤ r}.ncard : ℝ) ≤ C * r ^ ρ) {s : ℝ} (hs : ρ < s) :
    Summable fun i => ‖a i‖ ^ (-s) := by
  classical
  set q : ℝ := (2 : ℝ) ^ (ρ - s) with hq_def
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set S₀ := (finite_setOf_norm_le_of_tendsto hlim 1).toFinset with hS₀_def
  set K₀ : ℝ := ∑ i ∈ S₀, ‖a i‖ ^ (-s) with hK₀_def
  have hterm : ∀ i, 0 ≤ ‖a i‖ ^ (-s) := fun i => Real.rpow_nonneg (norm_nonneg _) _
  refine summable_of_sum_le (c := K₀ + C * 2 ^ ρ / (1 - q)) hterm fun F => ?_
  rw [← Finset.sum_filter_add_sum_filter_not F (fun i => ‖a i‖ ≤ 1)]
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hterm i
    intro i hi
    rw [Finset.mem_filter] at hi
    exact (Set.Finite.mem_toFinset _).mpr hi.2
  · set G := F.filter (fun i => ¬ ‖a i‖ ≤ 1) with hG_def
    set sh : ι → ℕ := fun i => ⌊Real.logb 2 ‖a i‖⌋₊ with hsh_def
    have hG1 : ∀ i ∈ G, 1 < ‖a i‖ := fun i hi => by
      rw [hG_def, Finset.mem_filter] at hi
      exact not_le.mp hi.2
    have hsh : ∀ i ∈ G, (2 : ℝ) ^ (sh i : ℝ) ≤ ‖a i‖ ∧ ‖a i‖ < 2 ^ ((sh i : ℝ) + 1) := by
      intro i hi
      have h1 := hG1 i hi
      have hlog : 0 ≤ Real.logb 2 ‖a i‖ := Real.logb_nonneg one_lt_two h1.le
      have heq : (2 : ℝ) ^ Real.logb 2 ‖a i‖ = ‖a i‖ := Real.rpow_logb two_pos (by norm_num)
        (by linarith)
      constructor
      · rw [← heq]
        exact Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.floor_le hlog)
      · rw [← heq]
        exact Real.rpow_lt_rpow_of_exponent_lt one_lt_two (Nat.lt_floor_add_one _)
    have hfiber : ∀ j ∈ G.image sh,
        ∑ i ∈ G.filter (fun i => sh i = j), ‖a i‖ ^ (-s) ≤ C * 2 ^ ρ * q ^ j := by
      intro j _
      have hcard : (((G.filter (fun i => sh i = j)).card : ℕ) : ℝ) ≤
          C * 2 ^ ρ * 2 ^ ((j : ℝ) * ρ) := by
        have hsub : (↑(G.filter (fun i => sh i = j)) : Set ι) ⊆
            {i | ‖a i‖ ≤ 2 ^ ((j : ℝ) + 1)} := by
          intro i hi
          rw [Finset.mem_coe, Finset.mem_filter] at hi
          have := (hsh i hi.1).2
          rw [hi.2] at this
          exact this.le
        have h1 : ((G.filter (fun i => sh i = j)).card : ℝ) ≤
            ({i | ‖a i‖ ≤ 2 ^ ((j : ℝ) + 1)}.ncard : ℝ) := by
          rw [← Set.ncard_coe_finset]
          exact_mod_cast Set.ncard_le_ncard hsub (finite_setOf_norm_le_of_tendsto hlim _)
        have h2 := hN (2 ^ ((j : ℝ) + 1)) (by
          rw [show (1 : ℝ) = 2 ^ (0 : ℝ) by simp]
          exact Real.rpow_le_rpow_of_exponent_le one_le_two (by positivity))
        have h3 : ((2 : ℝ) ^ ((j : ℝ) + 1)) ^ ρ = 2 ^ ρ * 2 ^ ((j : ℝ) * ρ) := by
          rw [← Real.rpow_mul (by norm_num), add_mul, one_mul, Real.rpow_add two_pos, mul_comm]
        rw [h3] at h2
        linarith
      have hval : ∀ i ∈ G.filter (fun i => sh i = j), ‖a i‖ ^ (-s) ≤ 2 ^ (-((j : ℝ) * s)) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        have := (hsh i hi.1).1
        rw [hi.2] at this
        calc ‖a i‖ ^ (-s) ≤ ((2 : ℝ) ^ (j : ℝ)) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) this (by linarith)
          _ = 2 ^ (-((j : ℝ) * s)) := by rw [← Real.rpow_mul (by norm_num), mul_neg]
      calc ∑ i ∈ G.filter (fun i => sh i = j), ‖a i‖ ^ (-s)
          ≤ ∑ _i ∈ G.filter (fun i => sh i = j), (2 : ℝ) ^ (-((j : ℝ) * s)) :=
            Finset.sum_le_sum hval
        _ = ((G.filter (fun i => sh i = j)).card : ℝ) * 2 ^ (-((j : ℝ) * s)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ C * 2 ^ ρ * 2 ^ ((j : ℝ) * ρ) * 2 ^ (-((j : ℝ) * s)) := by
            gcongr
        _ = C * 2 ^ ρ * q ^ j := by
            rw [mul_assoc (C * 2 ^ ρ), ← Real.rpow_add two_pos, hq_def, ← Real.rpow_natCast,
              ← Real.rpow_mul (by norm_num)]
            congr 2
            ring
    calc ∑ i ∈ G, ‖a i‖ ^ (-s)
        = ∑ j ∈ G.image sh, ∑ i ∈ G.filter (fun i => sh i = j), ‖a i‖ ^ (-s) :=
          (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem sh hi) _).symm
      _ ≤ ∑ j ∈ G.image sh, C * 2 ^ ρ * q ^ j := Finset.sum_le_sum hfiber
      _ ≤ ∑' j : ℕ, C * 2 ^ ρ * q ^ j := by
          refine Summable.sum_le_tsum _ (fun j _ => by positivity) ?_
          exact (summable_geometric_of_lt_one hq0.le hq1).mul_left _
      _ = C * 2 ^ ρ / (1 - q) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1, div_eq_mul_inv]

/-- **Summability of the inverse powers of the zeros.** If `f` is entire with `f 0 ≠ 0` and of
order at most `ρ`, and `a` enumerates its zeros with multiplicity, then `∑ ‖a i‖ ^ (-s)`
converges for every `s > ρ`.

A counterpart under a related growth hypothesis appears in Matteo Cipollina's Hadamard
development. See `CREDITS.md`. -/
theorem summable_norm_rpow_neg_of_hasOrderLE (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hρ : 0 ≤ ρ) (hord : HasOrderLE f ρ)
    (hlim : Tendsto (fun i => ‖a i‖) cofinite atTop)
    (hzero : ∀ w, analyticOrderAt f w =
      ((finite_setOf_eq_of_tendsto_cofinite hlim w).toFinset.card : ℕ∞))
    {s : ℝ} (hs : ρ < s) : Summable fun i => ‖a i‖ ^ (-s) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := hord
  set C : ℝ := (Real.log (max 1 A) + |Real.log ‖f 0‖| + B * 2 ^ ρ) / Real.log 2 with hC_def
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hC : 0 ≤ C := by
    apply div_nonneg _ hlog2.le
    have : 0 ≤ Real.log (max 1 A) := Real.log_nonneg (le_max_left _ _)
    positivity
  refine summable_norm_rpow_neg_of_ncard_le hlim hρ hC (fun r hr => ?_) hs
  have hr0 : 0 < r := by linarith
  have h1 := sum_divisor_le_of_hasOrderLE hf h0 hbound hr0
  rw [← ncard_setOf_norm_le_eq_sum_divisor hf hlim hzero r] at h1
  push_cast at h1
  -- estimate the numerator
  have hrρ : 1 ≤ r ^ ρ := by
    rw [show (1 : ℝ) = 1 ^ ρ by simp]
    exact Real.rpow_le_rpow (by norm_num) hr hρ
  have hexp : 1 ≤ Real.exp (B * (2 * r) ^ ρ) := Real.one_le_exp (by positivity)
  have hmax : max 1 (A * Real.exp (B * (2 * r) ^ ρ)) ≤ max 1 A * Real.exp (B * (2 * r) ^ ρ) := by
    rw [max_le_iff]
    constructor
    · calc (1 : ℝ) ≤ max 1 A := le_max_left _ _
        _ = max 1 A * 1 := (mul_one _).symm
        _ ≤ max 1 A * Real.exp (B * (2 * r) ^ ρ) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  have hlogmax : Real.log (max 1 (A * Real.exp (B * (2 * r) ^ ρ))) ≤
      Real.log (max 1 A) + B * (2 * r) ^ ρ := by
    calc Real.log (max 1 (A * Real.exp (B * (2 * r) ^ ρ)))
        ≤ Real.log (max 1 A * Real.exp (B * (2 * r) ^ ρ)) :=
          Real.log_le_log (by positivity) hmax
      _ = Real.log (max 1 A) + B * (2 * r) ^ ρ := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have h2r : (2 * r) ^ ρ = 2 ^ ρ * r ^ ρ := Real.mul_rpow (by norm_num) hr0.le
  have hnum : Real.log (max 1 (A * Real.exp (B * (2 * r) ^ ρ))) - Real.log ‖f 0‖ ≤
      (Real.log (max 1 A) + |Real.log ‖f 0‖| + B * 2 ^ ρ) * r ^ ρ := by
    have hlogA : 0 ≤ Real.log (max 1 A) := Real.log_nonneg (le_max_left _ _)
    have habs : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| := neg_le_abs _
    have e1 : Real.log (max 1 A) ≤ Real.log (max 1 A) * r ^ ρ :=
      le_mul_of_one_le_right hlogA hrρ
    have e2 : |Real.log ‖f 0‖| ≤ |Real.log ‖f 0‖| * r ^ ρ :=
      le_mul_of_one_le_right (abs_nonneg _) hrρ
    have e3 : B * (2 * r) ^ ρ = B * 2 ^ ρ * r ^ ρ := by rw [h2r]; ring
    calc Real.log (max 1 (A * Real.exp (B * (2 * r) ^ ρ))) - Real.log ‖f 0‖
        ≤ Real.log (max 1 A) * r ^ ρ + |Real.log ‖f 0‖| * r ^ ρ + B * 2 ^ ρ * r ^ ρ := by
          linarith
      _ = (Real.log (max 1 A) + |Real.log ‖f 0‖| + B * 2 ^ ρ) * r ^ ρ := by ring
  calc (({i | ‖a i‖ ≤ r}.ncard : ℕ) : ℝ) ≤ _ := h1
    _ ≤ (Real.log (max 1 A) + |Real.log ‖f 0‖| + B * 2 ^ ρ) * r ^ ρ / Real.log 2 :=
        div_le_div_of_nonneg_right hnum hlog2.le
    _ = C * r ^ ρ := by rw [hC_def]; ring

end Complex

end
