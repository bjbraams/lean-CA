/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.CanonicalProduct

/-!
# Lower bounds for canonical products

If `∑ ‖a i‖ ^ (-ρ) < ∞` with `k ≤ s < k + 1` and `ρ < s`, then the canonical product of genus
`k` satisfies `‖P z‖ ≥ exp (-c ‖z‖ ^ s)` for `‖z‖ ≥ 1` outside the discs of radius
`‖a i‖⁻¹ ^ (k + 1)` around the zeros. The total length of the radii met by those discs is
finite, so there are arbitrarily large circles avoiding all of them. These are the estimates
behind Hadamard's factorization theorem.

## Main results

* `Complex.norm_tprod_ge_exp_neg_tsum`: a general lower bound for infinite products.
* `Complex.exists_exp_neg_le_norm_canonicalProduct`: the lower bound off the discs.
* `Complex.frequently_forall_norm_sub_ge`: arbitrarily large good radii.

## References

* E. M. Stein and R. Shakarchi, *Complex Analysis*, Chapter 5, Lemmas 5.3–5.6.
-/

public noncomputable section

open Set Metric Filter Function
open scoped Topology

namespace Complex

variable {ι : Type*} {a : ι → ℂ} {k : ℕ}

/-- `log x ≤ x ^ ε / ε` for `x > 0` and `ε > 0`. -/
theorem log_le_rpow_div_of_pos {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) :
    Real.log x ≤ x ^ ε / ε := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx ε)
  rw [Real.log_rpow hx] at h
  rw [le_div_iff₀ hε]
  linarith

/-- For a nonnegative real base, a natural power of its inverse is the real power with the
corresponding negative exponent. -/
theorem inv_pow_eq_rpow_neg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : x⁻¹ ^ n = x ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg hx, Real.rpow_natCast, inv_pow]

/-- Summability of `‖a i‖ ^ (-ρ)` with `ρ > 0` forces the family to tend to infinity. -/
theorem tendsto_norm_cofinite_of_summable_rpow (ha : ∀ i, a i ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hsum : Summable fun i ↦ ‖a i‖ ^ (-ρ)) : Tendsto (fun i ↦ ‖a i‖) cofinite atTop := by
  have h := hsum.tendsto_cofinite_zero
  rw [Filter.tendsto_atTop]
  intro b
  have hpos : 0 < (max b 1) ^ (-ρ) := by positivity
  filter_upwards [h.eventually (gt_mem_nhds hpos)] with i hi
  by_contra hlt
  push Not at hlt
  have h1 : (max b 1) ^ (-ρ) ≤ ‖a i‖ ^ (-ρ) :=
    Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr (ha i)) (hlt.le.trans (le_max_left b 1))
      (by linarith)
  linarith

/-- Summability of `‖a i‖ ^ (-ρ)` transfers to larger exponents. -/
theorem summable_norm_rpow_neg_mono (hlim : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    {ρ s : ℝ} (hρs : ρ ≤ s) (hsum : Summable fun i ↦ ‖a i‖ ^ (-ρ)) :
    Summable fun i ↦ ‖a i‖ ^ (-s) := by
  refine Summable.of_norm_bounded_eventually hsum ?_
  filter_upwards [hlim.eventually (eventually_ge_atTop 1)] with i hi
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow_of_exponent_le hi (by linarith)

/-- Summability of `‖a i‖ ^ (-ρ)` with `ρ ≤ k + 1` gives summability of `‖a i‖⁻¹ ^ (k + 1)`. -/
theorem summable_inv_pow_of_summable_rpow (hlim : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    {ρ : ℝ} (hρ : ρ ≤ k + 1) (hsum : Summable fun i ↦ ‖a i‖ ^ (-ρ)) :
    Summable fun i ↦ ‖a i‖⁻¹ ^ (k + 1) := by
  refine (summable_norm_rpow_neg_mono hlim hρ hsum).congr fun i ↦ ?_
  rw [inv_pow_eq_rpow_neg (norm_nonneg _)]
  push_cast
  rfl

/-- The counting function is bounded by `r ^ ρ` times the sum of the inverse powers. -/
theorem ncard_setOf_norm_le_le_rpow_mul_tsum (ha : ∀ i, a i ≠ 0)
    (hlim : Tendsto (fun i ↦ ‖a i‖) cofinite atTop) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsum : Summable fun i ↦ ‖a i‖ ^ (-ρ)) {r : ℝ} (hr : 0 < r) :
    ({i | ‖a i‖ ≤ r}.ncard : ℝ) ≤ r ^ ρ * ∑' i, ‖a i‖ ^ (-ρ) := by
  classical
  have hfin := finite_setOf_norm_le_of_tendsto hlim r
  rw [Set.ncard_eq_toFinset_card _ hfin]
  calc ((hfin.toFinset.card : ℕ) : ℝ) = ∑ _i ∈ hfin.toFinset, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ hfin.toFinset, r ^ ρ * ‖a i‖ ^ (-ρ) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hi' : ‖a i‖ ≤ r := hfin.mem_toFinset.mp hi
        have h1 : r ^ (-ρ) ≤ ‖a i‖ ^ (-ρ) :=
          Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr (ha i)) hi' (by linarith)
        calc (1 : ℝ) = r ^ ρ * r ^ (-ρ) := by
              rw [← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero]
          _ ≤ r ^ ρ * ‖a i‖ ^ (-ρ) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = r ^ ρ * ∑ i ∈ hfin.toFinset, ‖a i‖ ^ (-ρ) := by rw [Finset.mul_sum]
    _ ≤ r ^ ρ * ∑' i, ‖a i‖ ^ (-ρ) := by
        gcongr
        exact hsum.sum_le_tsum _ fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _

/-- **A lower bound for infinite products.** If `‖g i‖ ≥ exp (-u i)` with `u ≥ 0` summable,
then `‖∏' i, g i‖ ≥ exp (-∑' i, u i)`. -/
theorem norm_tprod_ge_exp_neg_tsum {g : ι → ℂ} {u : ι → ℝ} (hg : Multipliable g)
    (hu : Summable u) (hu0 : ∀ i, 0 ≤ u i) (h : ∀ i, Real.exp (-u i) ≤ ‖g i‖) :
    Real.exp (-∑' i, u i) ≤ ‖∏' i, g i‖ := by
  have ht : Tendsto (fun F : Finset ι ↦ ‖∏ i ∈ F, g i‖) atTop (𝓝 ‖∏' i, g i‖) :=
    Filter.Tendsto.norm hg.hasProd
  refine ge_of_tendsto ht (Eventually.of_forall fun F ↦ ?_)
  rw [norm_prod]
  calc Real.exp (-∑' i, u i) ≤ Real.exp (-∑ i ∈ F, u i) := by
        apply Real.exp_le_exp.mpr
        have := hu.sum_le_tsum F fun i _ ↦ hu0 i
        linarith
    _ = ∏ i ∈ F, Real.exp (-u i) := by rw [← Real.exp_sum, Finset.sum_neg_distrib]
    _ ≤ ∏ i ∈ F, ‖g i‖ :=
        Finset.prod_le_prod₀ (fun i _ ↦ (Real.exp_pos _).le) fun i _ ↦ h i

/-- The family `E_k (z / a i)` is multipliable. -/
theorem multipliable_elementaryFactor_div (ha : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ ‖a i‖⁻¹ ^ (k + 1)) (z : ℂ) :
    Multipliable fun i ↦ elementaryFactor k (z / a i) := by
  have h1 : Summable fun i ↦ ‖elementaryFactor k (z / a i) - 1‖ :=
    (hasSummableBoundOn_canonical ha hs).summable_norm (mem_univ z)
  have h2 : Multipliable fun i ↦ 1 + (elementaryFactor k (z / a i) - 1) :=
    multipliable_one_add_of_summable (f := fun i ↦ elementaryFactor k (z / a i) - 1) h1
  exact h2.congr fun i ↦ add_sub_cancel _ _

/-- Sub-families of `E_k (z / a i)` are multipliable. -/
theorem multipliable_elementaryFactor_div_subtype (ha : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ ‖a i‖⁻¹ ^ (k + 1)) (z : ℂ) (S : Set ι) :
    Multipliable ((fun i ↦ elementaryFactor k (z / a i)) ∘ (Subtype.val : S → ι)) := by
  have h1 : Summable fun i : S ↦ ‖elementaryFactor k (z / a i) - 1‖ :=
    ((hasSummableBoundOn_canonical ha hs).summable_norm (mem_univ z)).subtype _
  have h2 : Multipliable fun i : S ↦ 1 + (elementaryFactor k (z / a i) - 1) :=
    multipliable_one_add_of_summable (f := fun i : S ↦ elementaryFactor k (z / a i) - 1) h1
  exact h2.congr fun i ↦ add_sub_cancel _ _

/-- Splitting the canonical product at a finite set of indices. -/
theorem canonicalProduct_eq_prod_mul_tprod (ha : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ ‖a i‖⁻¹ ^ (k + 1)) (F : Finset ι) (z : ℂ) :
    canonicalProduct k a z = (∏ i ∈ F, elementaryFactor k (z / a i)) *
      ∏' i : ↥((F : Set ι)ᶜ), elementaryFactor k (z / a i) := by
  set g : ι → ℂ := fun i ↦ elementaryFactor k (z / a i)
  have h1 : Multipliable (g ∘ (Subtype.val : ↥(F : Set ι) → ι)) :=
    multipliable_elementaryFactor_div_subtype ha hs z _
  have h2 : Multipliable (g ∘ (Subtype.val : ↥((F : Set ι)ᶜ) → ι)) :=
    multipliable_elementaryFactor_div_subtype ha hs z _
  have hsplit := Multipliable.tprod_mul_tprod_compl h1 h2
  have h3 : ∏' x : ↥(F : Set ι), g x = ∏ i ∈ F, g i := Finset.tprod_subtype F g
  change ∏' i, g i = (∏ i ∈ F, g i) * ∏' i : ↥((F : Set ι)ᶜ), g i
  rw [← hsplit, h3]

/-- **The far factors.** Over a set of indices with `‖a i‖ > 2 ‖z‖`, the product of the
elementary factors is bounded below by `exp (-c ‖z‖ ^ ρ)`. -/
theorem exp_neg_le_norm_tprod_far (ha : ∀ i, a i ≠ 0) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρk : ρ ≤ k + 1) (hsum : Summable fun i ↦ ‖a i‖ ^ (-ρ)) {z : ℂ} (hz : 1 ≤ ‖z‖)
    {S : Set ι} (hS : ∀ i ∈ S, 2 * ‖z‖ < ‖a i‖) :
    Real.exp (-(2 * 2 ^ (ρ - (k + 1)) * (∑' i, ‖a i‖ ^ (-ρ)) * ‖z‖ ^ ρ)) ≤
      ‖∏' i : ↥S, elementaryFactor k (z / a i)‖ := by
  have hlim := tendsto_norm_cofinite_of_summable_rpow ha hρ0 hsum
  have hs1 := summable_inv_pow_of_summable_rpow hlim hρk hsum
  have hmul := multipliable_elementaryFactor_div_subtype ha hs1 z S
  have hr0 : 0 < ‖z‖ := by linarith
  set r := ‖z‖ with hr_def
  have hu : Summable fun i : ↥S ↦ 2 * r ^ (k + 1) * ‖a i‖⁻¹ ^ (k + 1) :=
    (hs1.subtype _).mul_left _
  refine le_trans ?_ (norm_tprod_ge_exp_neg_tsum hmul hu (fun i ↦ by positivity)
    fun i ↦ ?_)
  · apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    have hterm : ∀ i : ↥S, 2 * r ^ (k + 1) * ‖a i‖⁻¹ ^ (k + 1) ≤
        2 * 2 ^ (ρ - (k + 1)) * r ^ ρ * ‖a i‖ ^ (-ρ) := by
      intro i
      have hi := hS i i.2
      have hai : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
      have h2r : 0 < 2 * r := by positivity
      have e1 : ‖a i‖⁻¹ ^ (k + 1) = ‖a i‖ ^ (-ρ) * ‖a i‖ ^ (ρ - (k + 1)) := by
        rw [inv_pow_eq_rpow_neg (norm_nonneg _), ← Real.rpow_add hai]
        push_cast
        ring_nf
      have e2 : ‖a i‖ ^ (ρ - (k + 1)) ≤ (2 * r) ^ (ρ - (k + 1)) :=
        Real.rpow_le_rpow_of_nonpos h2r hi.le (by linarith)
      have e3 : r ^ (k + 1) * (2 * r) ^ (ρ - (k + 1)) = 2 ^ (ρ - (k + 1)) * r ^ ρ := by
        rw [Real.mul_rpow (by norm_num) hr0.le, ← Real.rpow_natCast r (k + 1)]
        push_cast
        rw [mul_left_comm, ← Real.rpow_add hr0]
        congr 2
        ring
      calc 2 * r ^ (k + 1) * ‖a i‖⁻¹ ^ (k + 1)
          = 2 * r ^ (k + 1) * (‖a i‖ ^ (-ρ) * ‖a i‖ ^ (ρ - (k + 1))) := by rw [e1]
        _ ≤ 2 * r ^ (k + 1) * (‖a i‖ ^ (-ρ) * (2 * r) ^ (ρ - (k + 1))) := by gcongr
        _ = 2 * 2 ^ (ρ - (k + 1)) * r ^ ρ * ‖a i‖ ^ (-ρ) := by
            linear_combination (2 * ‖a i‖ ^ (-ρ)) * e3
    calc ∑' i : ↥S, 2 * r ^ (k + 1) * ‖a i‖⁻¹ ^ (k + 1)
        ≤ ∑' i : ↥S, 2 * 2 ^ (ρ - (k + 1)) * r ^ ρ * ‖a i‖ ^ (-ρ) :=
          hu.tsum_le_tsum hterm ((hsum.subtype _).mul_left _)
      _ = 2 * 2 ^ (ρ - (k + 1)) * r ^ ρ * ∑' i : ↥S, ‖a i‖ ^ (-ρ) := tsum_mul_left
      _ ≤ 2 * 2 ^ (ρ - (k + 1)) * r ^ ρ * ∑' i, ‖a i‖ ^ (-ρ) := by
          gcongr
          exact hsum.tsum_subtype_le _ S fun i ↦ Real.rpow_nonneg (norm_nonneg _) _
      _ = 2 * 2 ^ (ρ - (k + 1)) * (∑' i, ‖a i‖ ^ (-ρ)) * r ^ ρ := by ring
  · have hi := hS i i.2
    have hw : ‖z / a i‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (ha i))]
      linarith
    refine le_trans (le_of_eq ?_) (exp_neg_le_norm_elementaryFactor hw)
    rw [norm_div, div_eq_mul_inv, mul_pow, ← hr_def]
    ring_nf

/-- **The near factors, exponential part.** -/
theorem prod_norm_elementaryFactor_div_ge (F : Finset ι) {z : ℂ}
    (hF : ∀ i ∈ F, 1 / 2 ≤ ‖z / a i‖) :
    (∏ i ∈ F, ‖1 - z / a i‖) * Real.exp (-(2 ^ k * k * ∑ i ∈ F, ‖z / a i‖ ^ k)) ≤
      ∏ i ∈ F, ‖elementaryFactor k (z / a i)‖ := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun i _ ↦ by positivity) fun i hi ↦
    norm_one_sub_mul_exp_neg_le_norm_elementaryFactor (hF i hi)

/-- **The near factors, size of the exponent.** -/
theorem sum_norm_div_pow_le (hlim : Tendsto (fun i ↦ ‖a i‖) cofinite atTop)
    {ρ : ℝ} (hsum : Summable fun i ↦ ‖a i‖ ^ (-ρ)) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ∑ i ∈ (finite_setOf_norm_le_of_tendsto hlim (2 * ‖z‖)).toFinset, ‖z / a i‖ ^ k ≤
      ((∑ i ∈ (finite_setOf_norm_le_of_tendsto hlim 1).toFinset, ‖a i‖⁻¹ ^ k) +
        2 ^ max (ρ - k) 0 * ∑' i, ‖a i‖ ^ (-ρ)) * ‖z‖ ^ ((k : ℝ) + max (ρ - k) 0) := by
  classical
  set r := ‖z‖
  have hr0 : 0 < r := by linarith
  set m : ℝ := max (ρ - k) 0
  have hm0 : 0 ≤ m := le_max_right _ _
  set T : ℝ := ∑' i, ‖a i‖ ^ (-ρ)
  have hT0 : 0 ≤ T := tsum_nonneg fun i ↦ Real.rpow_nonneg (norm_nonneg _) _
  set F := (finite_setOf_norm_le_of_tendsto hlim (2 * r)).toFinset
  set S₀ := (finite_setOf_norm_le_of_tendsto hlim 1).toFinset
  set K₀ : ℝ := ∑ i ∈ S₀, ‖a i‖⁻¹ ^ k
  have hK₀ : 0 ≤ K₀ := Finset.sum_nonneg fun i _ ↦ by positivity
  have hFmem : ∀ i, i ∈ F ↔ ‖a i‖ ≤ 2 * r := fun i ↦ Set.Finite.mem_toFinset _
  have hterm : ∀ i, ‖z / a i‖ ^ k = r ^ k * ‖a i‖⁻¹ ^ k := fun i ↦ by
    rw [norm_div, div_eq_mul_inv, mul_pow]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  -- split the sum at `‖a i‖ ≤ 1`
  have hsplit : ∑ i ∈ F, ‖a i‖⁻¹ ^ k ≤ K₀ + (2 * r) ^ m * T := by
    rw [← Finset.sum_filter_add_sum_filter_not F (fun i ↦ ‖a i‖ ≤ 1)]
    refine add_le_add ?_ ?_
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ ↦ by positivity
      intro i hi
      rw [Finset.mem_filter] at hi
      exact (Set.Finite.mem_toFinset _).mpr hi.2
    · have hbound : ∀ i ∈ F.filter (fun i ↦ ¬ ‖a i‖ ≤ 1),
          ‖a i‖⁻¹ ^ k ≤ (2 * r) ^ m * ‖a i‖ ^ (-ρ) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        have h1 : 1 < ‖a i‖ := not_le.mp hi.2
        have h2 : ‖a i‖ ≤ 2 * r := (hFmem i).mp hi.1
        have hai : 0 < ‖a i‖ := by linarith
        rw [inv_pow_eq_rpow_neg (norm_nonneg _), show -(k : ℝ) = -ρ + (ρ - k) by ring,
          Real.rpow_add hai, mul_comm]
        gcongr
        calc ‖a i‖ ^ (ρ - k) ≤ ‖a i‖ ^ m :=
              Real.rpow_le_rpow_of_exponent_le h1.le (le_max_left _ _)
          _ ≤ (2 * r) ^ m := Real.rpow_le_rpow hai.le h2 hm0
      calc ∑ i ∈ F.filter (fun i ↦ ¬ ‖a i‖ ≤ 1), ‖a i‖⁻¹ ^ k
          ≤ ∑ i ∈ F.filter (fun i ↦ ¬ ‖a i‖ ≤ 1), (2 * r) ^ m * ‖a i‖ ^ (-ρ) :=
            Finset.sum_le_sum hbound
        _ = (2 * r) ^ m * ∑ i ∈ F.filter (fun i ↦ ¬ ‖a i‖ ≤ 1), ‖a i‖ ^ (-ρ) := by
            rw [Finset.mul_sum]
        _ ≤ (2 * r) ^ m * T := by
            gcongr
            exact hsum.sum_le_tsum _ fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hrk : r ^ k = r ^ (k : ℝ) := (Real.rpow_natCast r k).symm
  have hrkm : r ^ (k : ℝ) * r ^ m = r ^ ((k : ℝ) + m) := (Real.rpow_add hr0 _ _).symm
  have hrk_le : r ^ (k : ℝ) ≤ r ^ ((k : ℝ) + m) :=
    Real.rpow_le_rpow_of_exponent_le hz (by linarith)
  have h2rm : (2 * r) ^ m = 2 ^ m * r ^ m := Real.mul_rpow (by norm_num) hr0.le
  calc r ^ k * ∑ i ∈ F, ‖a i‖⁻¹ ^ k ≤ r ^ k * (K₀ + (2 * r) ^ m * T) := by gcongr
    _ = K₀ * r ^ (k : ℝ) + 2 ^ m * T * (r ^ (k : ℝ) * r ^ m) := by rw [hrk, h2rm]; ring
    _ ≤ K₀ * r ^ ((k : ℝ) + m) + 2 ^ m * T * r ^ ((k : ℝ) + m) := by
        rw [hrkm]
        gcongr
    _ = (K₀ + 2 ^ m * T) * r ^ ((k : ℝ) + m) := by ring

/-- **The near factors, linear part.** Off the discs of radius `‖a i‖⁻¹ ^ (k + 1)` the product
of `‖1 - z / a i‖` over the near zeros is bounded below by `exp (-c ‖z‖ ^ s)`. -/
theorem exp_neg_le_prod_norm_one_sub_div (ha : ∀ i, a i ≠ 0)
    (hlim : Tendsto (fun i ↦ ‖a i‖) cofinite atTop) {ρ s : ℝ} (hρ0 : 0 ≤ ρ) (hρs : ρ < s)
    (hsum : Summable fun i ↦ ‖a i‖ ^ (-ρ)) {z : ℂ} (hz : 1 ≤ ‖z‖)
    (hdisc : ∀ i, ‖a i‖⁻¹ ^ (k + 1) ≤ ‖z - a i‖) :
    Real.exp (-((k + 2) * (∑' i, ‖a i‖ ^ (-ρ)) * 2 ^ s / (s - ρ) * ‖z‖ ^ s)) ≤
      ∏ i ∈ (finite_setOf_norm_le_of_tendsto hlim (2 * ‖z‖)).toFinset, ‖1 - z / a i‖ := by
  classical
  set r := ‖z‖
  have hr0 : 0 < r := by linarith
  have h2r : 1 ≤ 2 * r := by linarith
  set T : ℝ := ∑' i, ‖a i‖ ^ (-ρ)
  have hT0 : 0 ≤ T := tsum_nonneg fun i ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hfin := finite_setOf_norm_le_of_tendsto hlim (2 * r)
  set F := hfin.toFinset
  have hFmem : ∀ i, i ∈ F ↔ ‖a i‖ ≤ 2 * r := fun i ↦ Set.Finite.mem_toFinset _
  -- each factor is at least `‖a i‖⁻¹ ^ (k + 2)`
  have hfactor : ∀ i, ‖a i‖⁻¹ ^ (k + 2) ≤ ‖1 - z / a i‖ := by
    intro i
    have hai : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
    have : ‖1 - z / a i‖ = ‖a i - z‖ / ‖a i‖ := by
      rw [← norm_div, sub_div, div_self (ha i)]
    rw [this, norm_sub_rev, le_div_iff₀ hai, pow_succ, mul_assoc, inv_mul_cancel₀ hai.ne',
      mul_one]
    exact hdisc i
  -- the product of these lower bounds
  have hprod : ∏ i ∈ F, ‖a i‖⁻¹ ^ (k + 2) =
      Real.exp (-((k + 2) * ∑ i ∈ F, Real.log ‖a i‖)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hai : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
    rw [← Real.exp_log (by positivity : 0 < ‖a i‖⁻¹ ^ (k + 2)), Real.log_pow, Real.log_inv]
    push_cast
    ring_nf
  -- the sum of the logarithms
  have hlog : ∑ i ∈ F, Real.log ‖a i‖ ≤ T * 2 ^ s / (s - ρ) * r ^ s := by
    have hcard : (F.card : ℝ) ≤ (2 * r) ^ ρ * T := by
      have := ncard_setOf_norm_le_le_rpow_mul_tsum ha hlim hρ0 hsum (by linarith : 0 < 2 * r)
      rwa [Set.ncard_eq_toFinset_card _ hfin] at this
    have hlog2r : 0 ≤ Real.log (2 * r) := Real.log_nonneg h2r
    have hle : Real.log (2 * r) ≤ (2 * r) ^ (s - ρ) / (s - ρ) :=
      log_le_rpow_div_of_pos (by linarith) (by linarith)
    calc ∑ i ∈ F, Real.log ‖a i‖ ≤ ∑ _i ∈ F, Real.log (2 * r) := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          exact Real.log_le_log (norm_pos_iff.mpr (ha i)) ((hFmem i).mp hi)
      _ = F.card * Real.log (2 * r) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * r) ^ ρ * T * ((2 * r) ^ (s - ρ) / (s - ρ)) := by gcongr
      _ = T * 2 ^ s / (s - ρ) * r ^ s := by
          rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, mul_right_comm ((2 * r) ^ ρ),
            ← Real.rpow_add (by linarith : 0 < 2 * r), add_sub_cancel,
            Real.mul_rpow (by norm_num) hr0.le]
          ring
  calc Real.exp (-((k + 2) * T * 2 ^ s / (s - ρ) * r ^ s))
      ≤ Real.exp (-((k + 2) * ∑ i ∈ F, Real.log ‖a i‖)) := by
        apply Real.exp_le_exp.mpr
        have : (k + 2 : ℝ) * ∑ i ∈ F, Real.log ‖a i‖ ≤ (k + 2) * (T * 2 ^ s / (s - ρ) * r ^ s) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        have e : (k + 2 : ℝ) * (T * 2 ^ s / (s - ρ) * r ^ s) =
            (k + 2) * T * 2 ^ s / (s - ρ) * r ^ s := by ring
        linarith
    _ = ∏ i ∈ F, ‖a i‖⁻¹ ^ (k + 2) := hprod.symm
    _ ≤ ∏ i ∈ F, ‖1 - z / a i‖ :=
        Finset.prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ hfactor i

/-- **Lower bound for the canonical product off the exceptional discs.** With
`∑ ‖a i‖ ^ (-ρ) < ∞`, `k ≤ s < k + 1` and `ρ < s`, there is `c` such that
`‖P z‖ ≥ exp (-c ‖z‖ ^ s)` for all `z` with `‖z‖ ≥ 1` at distance at least
`‖a i‖⁻¹ ^ (k + 1)` from every `a i`. -/
theorem exists_exp_neg_le_norm_canonicalProduct (ha : ∀ i, a i ≠ 0) {s ρ : ℝ}
    (hk : (k : ℝ) ≤ s) (hsk : s < k + 1) (hρ0 : 0 < ρ) (hρs : ρ < s)
    (hsum : Summable fun i ↦ ‖a i‖ ^ (-ρ)) :
    ∃ c : ℝ, ∀ z : ℂ, 1 ≤ ‖z‖ → (∀ i, ‖a i‖⁻¹ ^ (k + 1) ≤ ‖z - a i‖) →
      Real.exp (-(c * ‖z‖ ^ s)) ≤ ‖canonicalProduct k a z‖ := by
  classical
  have hlim := tendsto_norm_cofinite_of_summable_rpow ha hρ0 hsum
  have hs1 : Summable fun i ↦ ‖a i‖⁻¹ ^ (k + 1) :=
    summable_inv_pow_of_summable_rpow hlim (by linarith) hsum
  set T : ℝ := ∑' i, ‖a i‖ ^ (-ρ)
  have hT0 : 0 ≤ T := tsum_nonneg fun i ↦ Real.rpow_nonneg (norm_nonneg _) _
  set K₀ : ℝ := ∑ i ∈ (finite_setOf_norm_le_of_tendsto hlim 1).toFinset, ‖a i‖⁻¹ ^ k
  have hK₀ : 0 ≤ K₀ := Finset.sum_nonneg fun i _ ↦ by positivity
  set m : ℝ := max (ρ - k) 0 with hm_def
  have hm0 : 0 ≤ m := le_max_right _ _
  have hkm : (k : ℝ) + m ≤ s := by
    rw [hm_def]
    rcases le_total (ρ - k) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  set c₁ : ℝ := 2 * 2 ^ (ρ - (k + 1)) * T with hc₁_def
  set c₂ : ℝ := 2 ^ k * k * (K₀ + 2 ^ m * T) with hc₂_def
  set c₃ : ℝ := (k + 2) * T * 2 ^ s / (s - ρ)
  have hc₂ : 0 ≤ c₂ := by positivity
  refine ⟨c₁ + c₂ + c₃, fun z hz hdisc ↦ ?_⟩
  set r : ℝ := ‖z‖
  have hr0 : 0 < r := by linarith
  have hfin := finite_setOf_norm_le_of_tendsto hlim (2 * r)
  set F := hfin.toFinset
  have hFmem : ∀ i, i ∈ F ↔ ‖a i‖ ≤ 2 * r := fun i ↦ Set.Finite.mem_toFinset _
  rw [canonicalProduct_eq_prod_mul_tprod ha hs1 F z, norm_mul, norm_prod]
  -- the far factors
  have hfar : Real.exp (-(c₁ * r ^ s)) ≤
      ‖∏' i : ↥((F : Set ι)ᶜ), elementaryFactor k (z / a i)‖ := by
    refine le_trans ?_ (exp_neg_le_norm_tprod_far ha hρ0 (by linarith) hsum hz
      (S := (F : Set ι)ᶜ) fun i hi ↦ ?_)
    · apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, hc₁_def]
      have : r ^ ρ ≤ r ^ s := Real.rpow_le_rpow_of_exponent_le hz hρs.le
      have h0 : 0 ≤ 2 * 2 ^ (ρ - (k + 1)) * T := by positivity
      exact mul_le_mul_of_nonneg_left this h0
    · rw [mem_compl_iff, Finset.mem_coe, hFmem] at hi
      exact not_le.mp hi
  -- the near factors
  have hnear : Real.exp (-((c₂ + c₃) * r ^ s)) ≤ ∏ i ∈ F, ‖elementaryFactor k (z / a i)‖ := by
    have hF : ∀ i ∈ F, 1 / 2 ≤ ‖z / a i‖ := by
      intro i hi
      rw [norm_div, le_div_iff₀ (norm_pos_iff.mpr (ha i))]
      linarith [(hFmem i).mp hi]
    refine le_trans ?_ (prod_norm_elementaryFactor_div_ge F hF)
    have hsum' := sum_norm_div_pow_le (k := k) hlim hsum hz
    have hexp : Real.exp (-(c₂ * r ^ s)) ≤ Real.exp (-(2 ^ k * k * ∑ i ∈ F, ‖z / a i‖ ^ k)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, hc₂_def]
      have h1 : r ^ ((k : ℝ) + m) ≤ r ^ s := Real.rpow_le_rpow_of_exponent_le hz hkm
      calc (2 : ℝ) ^ k * k * ∑ i ∈ F, ‖z / a i‖ ^ k
          ≤ 2 ^ k * k * ((K₀ + 2 ^ m * T) * r ^ ((k : ℝ) + m)) := by gcongr
        _ ≤ 2 ^ k * k * ((K₀ + 2 ^ m * T) * r ^ s) := by gcongr
        _ = 2 ^ k * k * (K₀ + 2 ^ m * T) * r ^ s := by ring
    have hlin := exp_neg_le_prod_norm_one_sub_div (k := k) ha hlim hρ0.le hρs hsum hz hdisc
    calc Real.exp (-((c₂ + c₃) * r ^ s)) = Real.exp (-(c₃ * r ^ s)) * Real.exp (-(c₂ * r ^ s)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ (∏ i ∈ F, ‖1 - z / a i‖) * Real.exp (-(2 ^ k * k * ∑ i ∈ F, ‖z / a i‖ ^ k)) :=
          mul_le_mul hlin hexp (Real.exp_pos _).le (Finset.prod_nonneg fun i _ ↦ norm_nonneg _)
  calc Real.exp (-((c₁ + c₂ + c₃) * r ^ s))
      = Real.exp (-((c₂ + c₃) * r ^ s)) * Real.exp (-(c₁ * r ^ s)) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ (∏ i ∈ F, ‖elementaryFactor k (z / a i)‖) *
        ‖∏' i : ↥((F : Set ι)ᶜ), elementaryFactor k (z / a i)‖ :=
        mul_le_mul hnear hfar (Real.exp_pos _).le (Finset.prod_nonneg fun i _ ↦ norm_nonneg _)

end Complex

end
