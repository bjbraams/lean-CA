/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Blaschke
public import ComplexAnalysis.RemovableSingularity
public import ComplexAnalysis.Hadamard

/-!
# The Riesz factorization theorem

A bounded holomorphic function `f` on the disc, not identically zero, factors as
`f = B * g` where `B` is the Blaschke product formed from the zeros of `f` (each zero
repeated according to its multiplicity) and `g` is holomorphic, nonvanishing, and bounded on
the disc by the same bound as `f`.

The proof enumerates the nonzero zeros with multiplicity over the countable index type
`Σ w : Z, Fin (ord w)` (as for Hadamard's factorization theorem), uses the multiplicity-weighted
Blaschke condition of `Blaschke.lean` for the convergence of the matching Blaschke product `B`,
divides `f` by `z ^ m * B` using `AnalyticOnNhd.exists_ne_zero_mul_of_analyticOrderAt_eq`, and
shows that the cofactor has the same bound `M`, by comparing `f` to the finite partial Blaschke
products on circles of radius `r → 1`.

## Main results

* `Complex.norm_le_of_blaschkeProduct_bounded`: boundedness of the cofactor `g`, by comparing
  `f` to finite Blaschke prefixes on circles of radius `r → 1` (maximum modulus) and passing
  to the limit of the full product.
* `Complex.exists_rieszFactorization`: **the Riesz factorization theorem**.

## References

* J. B. Conway, *Functions of One Complex Variable II*, Chapter 20, Theorem 2.6.
* B. Simon, *Basic Complex Analysis*, Section 9.9.
-/

public noncomputable section

open Set Metric Filter Function MeromorphicOn Real
open scoped Topology ComplexConjugate

namespace Complex

variable {f : ℂ → ℂ}

/-! ### The Riesz factorization theorem -/

variable {a : ι → ℂ}

/-- Restricting the Blaschke summable bound to the complement of a finite index set. -/
theorem hasSummableBoundOn_blaschke_compl (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ 1 - ‖a i‖) (S : Finset ι) :
    HasSummableBoundOn (fun (i : ↑((S : Set ι))ᶜ) (z : ℂ) ↦ blaschkeFactor (a i) z - 1)
      (ball 0 1) :=
  (hasSummableBoundOn_blaschke ha ha0 hs).comp_subtype _

/-- The Blaschke factors past a finite index set are multipliable at any point of the disc. -/
theorem multipliable_blaschke_compl (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ 1 - ‖a i‖) (S : Finset ι) {z : ℂ} (hz : ‖z‖ < 1) :
    Multipliable (fun i : ↑((S : Set ι))ᶜ ↦ blaschkeFactor (a i) z) := by
  have hsum := (hasSummableBoundOn_blaschke_compl ha ha0 hs S).summable_norm
    (mem_ball_zero_iff.mpr hz)
  have h2 := multipliable_one_add_of_summable (f := fun i : ↑((S : Set ι))ᶜ ↦
    blaschkeFactor (a i) z - 1) hsum
  exact h2.congr fun i ↦ add_sub_cancel _ _

/-- The tail of the Blaschke product past a finite index set is holomorphic on the disc. -/
theorem differentiableOn_blaschkeProduct_compl (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ 1 - ‖a i‖) (S : Finset ι) :
    DifferentiableOn ℂ (fun z ↦ ∏' i : ↑((S : Set ι))ᶜ, blaschkeFactor (a i) z) (ball 0 1) := by
  have : (fun z ↦ ∏' i : ↑((S : Set ι))ᶜ, blaschkeFactor (a i) z) =
      fun z ↦ ∏' i : ↑((S : Set ι))ᶜ, (1 + (blaschkeFactor (a i) z - 1)) := by
    funext z; simp
  rw [this]
  exact differentiableOn_tprod_one_add isOpen_ball
    (fun i ↦ (differentiableOn_blaschkeFactor_ball (ha i)).sub_const 1)
    (hasSummableBoundOn_blaschke_compl ha ha0 hs S)

/-- Splitting the Blaschke product into a finite prefix times the complementary tail. -/
theorem blaschkeProduct_eq_finset_prod_mul_tprod_compl (ha : ∀ i, ‖a i‖ < 1)
    (ha0 : ∀ i, a i ≠ 0) (hs : Summable fun i ↦ 1 - ‖a i‖) (S : Finset ι) {z : ℂ}
    (hz : ‖z‖ < 1) :
    blaschkeProduct a z =
      (∏ i ∈ S, blaschkeFactor (a i) z) * ∏' i : ↑((S : Set ι))ᶜ, blaschkeFactor (a i) z := by
  have hsum := (hasSummableBoundOn_blaschke ha ha0 hs).summable_norm (mem_ball_zero_iff.mpr hz)
  have hmulS : Multipliable ((fun i : ι ↦ blaschkeFactor (a i) z) ∘ ((↑) : ↥(S : Set ι) → ι)) := by
    have h2 := multipliable_one_add_of_summable (f := fun i : (S : Set ι) ↦
      blaschkeFactor (a i) z - 1) (hsum.subtype _)
    exact h2.congr fun i ↦ add_sub_cancel _ _
  have hcompl : Multipliable
      ((fun i : ι ↦ blaschkeFactor (a i) z) ∘ ((↑) : ↑((S : Set ι))ᶜ → ι)) :=
    multipliable_blaschke_compl ha ha0 hs S hz
  have hsplit := Multipliable.tprod_mul_tprod_compl (f := fun i : ι ↦ blaschkeFactor (a i) z)
    (s := (S : Set ι)) hmulS hcompl
  rw [blaschkeProduct, ← hsplit]
  congr 1
  exact Finset.tprod_subtype' S (fun i ↦ blaschkeFactor (a i) z)

/-- A finite product of Blaschke factors with nonzero parameters in the open unit disc has norm one
on the unit circle. -/
theorem norm_finset_prod_blaschkeFactor_eq_one (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (S : Finset ι) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖∏ i ∈ S, blaschkeFactor (a i) z‖ = 1 := by
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ ↦ ?_
  rw [norm_blaschkeFactor _ _ (ha0 i)]
  exact norm_discMobius_eq_one (ha i) hz

/-- A finite Blaschke product is continuous on the closed disc, since its poles lie strictly
outside it. -/
theorem continuousOn_finset_prod_blaschkeFactor (ha : ∀ i, ‖a i‖ < 1) (S : Finset ι) :
    ContinuousOn (fun z ↦ ‖∏ i ∈ S, blaschkeFactor (a i) z‖) (closedBall 0 1) := by
  refine continuous_norm.comp_continuousOn ?_
  refine continuousOn_finsetProd S fun i _ ↦ ?_
  have hden : ∀ z ∈ closedBall (0 : ℂ) 1, (1 : ℂ) - conj (a i) * z ≠ 0 := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    intro h
    have h1 : conj (a i) * z = 1 := by linear_combination -h
    have h2 : ‖conj (a i) * z‖ = 1 := by rw [h1, norm_one]
    rw [norm_mul, norm_conj] at h2
    have hprod : ‖a i‖ * ‖z‖ ≤ ‖a i‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    nlinarith [ha i]
  unfold blaschkeFactor
  exact (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).div
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) hden

/-- As `‖z‖ → 1⁻`, the finite Blaschke product's modulus is uniformly close to `1`. -/
theorem exists_lt_one_forall_norm_ge (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0) (S : Finset ι)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r₀ < 1, ∀ r, r₀ < r → r < 1 →
      ∀ z : ℂ, ‖z‖ = r → 1 - ε ≤ ‖∏ i ∈ S, blaschkeFactor (a i) z‖ := by
  have hcont := continuousOn_finset_prod_blaschkeFactor ha S
  have hUC := (isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδ, hunif⟩ := hUC ε hε
  set r₀ : ℝ := max 0 (1 - δ)
  have hr₀1 : r₀ < 1 := max_lt (by norm_num) (by linarith)
  refine ⟨r₀, hr₀1, fun r hr0 hr1 z hz ↦ ?_⟩
  have hr0' : 0 < r := lt_of_le_of_lt (le_max_left 0 (1 - δ)) hr0
  have hδr : 1 - r < δ := by
    have := lt_of_le_of_lt (le_max_right 0 (1 - δ)) hr0
    linarith
  set w : ℂ := z / (r : ℂ) with hw_def
  have hw1 : ‖w‖ = 1 := by
    rw [hw_def, norm_div, hz, Complex.norm_real, Real.norm_of_nonneg hr0'.le, div_self hr0'.ne']
  have hr0c : (r : ℂ) ≠ 0 := by exact_mod_cast hr0'.ne'
  have hwz : dist w z < δ := by
    rw [hw_def, dist_eq_norm]
    have heq : z / (r : ℂ) - z = z * (((1 - r : ℝ) : ℂ) / (r : ℂ)) := by
      field_simp
      push_cast
      ring
    rw [heq, norm_mul, hz, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - r), Complex.norm_real,
      Real.norm_of_nonneg hr0'.le]
    calc r * ((1 - r) / r) = 1 - r := by field_simp
      _ < δ := hδr
  have hdist := hunif w (by rw [mem_closedBall_zero_iff, hw1]) z
    (by rw [mem_closedBall_zero_iff, hz]; linarith) hwz
  rw [dist_eq_norm] at hdist
  have hwval : ‖∏ i ∈ S, blaschkeFactor (a i) w‖ = 1 :=
    norm_finset_prod_blaschkeFactor_eq_one ha ha0 S hw1
  rw [hwval, Real.norm_eq_abs] at hdist
  have := abs_lt.mp hdist
  linarith [this.1]

/-- The maximum-modulus step for `norm_le_of_finset_factorization`: comparing on a circle of
radius `r` close to `1`, where the finite Blaschke prefix has modulus at least `1 - η`, gives
`‖h z0‖ ≤ M / (1 - η) ^ (m + 1)`. -/
private theorem norm_le_div_of_finset_factorization {f h : ℂ → ℂ}
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) {m : ℕ}
    (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0) (S : Finset ι)
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hfh : ∀ z ∈ ball (0 : ℂ) 1, f z = z ^ m * (∏ i ∈ S, blaschkeFactor (a i) z) * h z)
    {z0 : ℂ} (hz0 : z0 ∈ ball (0 : ℂ) 1) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ‖h z0‖ ≤ M / (1 - η) ^ (m + 1) := by
  obtain ⟨B, hB1, hB⟩ : ∃ B : ℝ, B < 1 ∧ ∀ i ∈ S, ‖a i‖ ≤ B := by
    rcases S.eq_empty_or_nonempty with hS | hS
    · exact ⟨0, by norm_num, by simp [hS]⟩
    · exact ⟨S.sup' hS fun i ↦ ‖a i‖, (Finset.sup'_lt_iff hS).mpr fun i _ ↦ ha i,
        fun i hi ↦ Finset.le_sup' (fun i ↦ ‖a i‖) hi⟩
  obtain ⟨r₀, hr₀1, hbound⟩ := exists_lt_one_forall_norm_ge ha ha0 S hη0
  obtain ⟨r, hrlt, hrlt1⟩ := exists_between
    (show max (max ‖z0‖ B) (max r₀ (1 - η)) < 1 by
      refine max_lt (max_lt (mem_ball_zero_iff.mp hz0) hB1) (max_lt hr₀1 (by linarith)))
  have hzr : ‖z0‖ < r := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hrlt
  have hBr : B < r := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hrlt
  have hr0r : r₀ < r := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hrlt
  have hηr : 1 - η < r := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hrlt
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg z0) hzr
  have hr1 : r < 1 := hrlt1
  -- f = z^m * finiteProd * h, with the finite product nonzero on the r-circle
  have hSne : ∀ z : ℂ, ‖z‖ = r → ∏ i ∈ S, blaschkeFactor (a i) z ≠ 0 := by
    intro z hz hcontra
    rw [Finset.prod_eq_zero_iff] at hcontra
    obtain ⟨i, hiS, hi0⟩ := hcontra
    have hai : ‖a i‖ < 1 := ha i
    have hiff := blaschkeFactor_eq_zero_iff hai (ha0 i) (by rw [hz]; exact hr1.le)
    rw [hiff] at hi0
    have heqz : ‖a i‖ = r := by rw [← hi0]; exact hz
    have hle := hB i hiS
    rw [heqz] at hle
    exact absurd hle (not_le.mpr hBr)
  have hbdry : ∀ z ∈ frontier (ball (0 : ℂ) r), ‖h z‖ ≤ M / (r ^ m * (1 - η)) := by
    intro z hz
    rw [frontier_ball (0:ℂ) hr0.ne', mem_sphere_zero_iff_norm] at hz
    have hzb : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hz ▸ hr1)
    have hSz : ∏ i ∈ S, blaschkeFactor (a i) z ≠ 0 := hSne z hz
    have hzm : (z ^ m : ℂ) ≠ 0 :=
      pow_ne_zero _ (by rintro rfl; simp at hz; linarith [hz.symm ▸ hr0])
    have heq := hfh z hzb
    have hD0 : z ^ m * (∏ i ∈ S, blaschkeFactor (a i) z) ≠ 0 := mul_ne_zero hzm hSz
    have hval : h z = f z / (z ^ m * (∏ i ∈ S, blaschkeFactor (a i) z)) :=
      (eq_div_iff hD0).mpr (by rw [heq]; ring)
    rw [hval, norm_div, norm_mul, norm_pow, hz]
    have hSb : 1 - η ≤ ‖∏ i ∈ S, blaschkeFactor (a i) z‖ := hbound r hr0r hr1 z hz
    have hMz : ‖f z‖ ≤ M := hM z hzb
    have hη' : (0:ℝ) < 1 - η := by linarith
    have hrm : (0:ℝ) < r ^ m := pow_pos hr0 m
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hstep : ‖f z‖ * (r ^ m * (1 - η)) ≤ M * (r ^ m * (1 - η)) :=
      mul_le_mul_of_nonneg_right hMz (by positivity)
    have hstep2 : M * (r ^ m * (1 - η)) ≤ M * (r ^ m * ‖∏ i ∈ S, blaschkeFactor (a i) z‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSb hrm.le) hM0
    linarith [hstep, hstep2]
  have hDC : DiffContOnCl ℂ h (ball (0 : ℂ) r) :=
    ⟨(hh.mono (ball_subset_ball hr1.le)),
      (hh.continuousOn.mono (closure_ball_subset_closedBall.trans
        (fun z hz ↦ mem_ball_zero_iff.mpr
          (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) hr1))))⟩
  have hzmem : z0 ∈ closure (ball (0 : ℂ) r) := by
    rw [closure_ball (0:ℂ) hr0.ne']
    exact mem_closedBall_zero_iff.mpr hzr.le
  have hmm := norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hDC hbdry hzmem
  calc ‖h z0‖ ≤ M / (r ^ m * (1 - η)) := hmm
    _ ≤ M / ((1 - η) ^ m * (1 - η)) := by
        apply div_le_div_of_nonneg_left hM0 (by positivity)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hηr.le m) (by linarith)
    _ = M / (1 - η) ^ (m + 1) := by rw [pow_succ]

/-- **Boundedness of the quotient by a finite Blaschke prefix.** If `f` is bounded by `M ≥ 0`
on the disc and `f = z^m * (finite Blaschke prefix) * h` for `h` holomorphic on the disc, then
`h` is also bounded by `M`. -/
theorem norm_le_of_finset_factorization {f h : ℂ → ℂ}
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) {m : ℕ}
    (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0) (S : Finset ι)
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hfh : ∀ z ∈ ball (0 : ℂ) 1, f z = z ^ m * (∏ i ∈ S, blaschkeFactor (a i) z) * h z)
    {z0 : ℂ} (hz0 : z0 ∈ ball (0 : ℂ) 1) : ‖h z0‖ ≤ M := by
  have key : ∀ η : ℝ, 0 < η → η < 1 → ‖h z0‖ ≤ M / (1 - η) ^ (m + 1) := fun η hη0 hη1 ↦
    norm_le_div_of_finset_factorization hM0 hM ha ha0 S hh hfh hz0 hη0 hη1
  have : (𝓝[Set.Ioo (0:ℝ) 1] (0:ℝ)).NeBot := left_nhdsWithin_Ioo_neBot one_pos
  have htend : Tendsto (fun η : ℝ ↦ M / (1 - η) ^ (m + 1)) (𝓝[Set.Ioo (0:ℝ) 1] (0:ℝ))
      (𝓝 M) := by
    have hb : Tendsto (fun η : ℝ ↦ M / (1 - η) ^ (m + 1)) (𝓝 (0:ℝ)) (𝓝 (M / (1-0)^(m+1))) := by
      apply Tendsto.div tendsto_const_nhds
      · exact ((tendsto_const_nhds).sub tendsto_id).pow (m+1)
      · norm_num
    simpa using hb.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with η hη using key η hη.1 hη.2

section
variable [Countable ι]

omit [Countable ι] in
/-- The finite prefix of the Blaschke product, along a chosen enumeration, converges to the
full product away from its zero set. -/
theorem tendsto_finset_prod_blaschkeFactor (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ 1 - ‖a i‖) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun S : Finset ι ↦ ∏ i ∈ S, blaschkeFactor (a i) z) Filter.atTop
      (𝓝 (blaschkeProduct a z)) := by
  have hsum := (hasSummableBoundOn_blaschke ha ha0 hs).summable_norm (mem_ball_zero_iff.mpr hz)
  have hmul : Multipliable (fun i : ι ↦ blaschkeFactor (a i) z) :=
    (multipliable_one_add_of_summable (f := fun i : ι ↦ blaschkeFactor (a i) z - 1) hsum).congr
      fun i ↦ add_sub_cancel _ _
  have := hmul.hasProd
  rwa [blaschkeProduct]

/-- **Boundedness of the cofactor in a Riesz factorization.** If `f` is bounded by `M ≥ 0` on
the disc and `f = z^m * (blaschke product of the `a i`) * g`, then `g` is also bounded by `M`. -/
theorem norm_le_of_blaschkeProduct_bounded {f : ℂ → ℂ}
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M)
    (ha0 : ∀ i, a i ≠ 0) (hab : ∀ i, ‖a i‖ < 1) (hs : Summable (fun i ↦ 1 - ‖a i‖))
    (hBne : ∃ z ∈ ball (0 : ℂ) 1, blaschkeProduct a z ≠ 0) {m : ℕ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1))
    (hfg : ∀ z ∈ ball (0 : ℂ) 1, f z = z ^ m * blaschkeProduct a z * g z) :
    ∀ z0 ∈ ball (0 : ℂ) 1, ‖g z0‖ ≤ M := by
  have hBan : AnalyticOnNhd ℂ (blaschkeProduct a) (ball 0 1) :=
    (differentiableOn_blaschkeProduct hab ha0 hs).analyticOnNhd isOpen_ball
  have caseA : ∀ z0 ∈ ball (0 : ℂ) 1, blaschkeProduct a z0 ≠ 0 → ‖g z0‖ ≤ M := by
    intro z0 hz0 hBz0
    obtain ⟨S, hSseq⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset ι))
    have hbound : ∀ T : Finset ι,
        ‖(∏' i : ↑((T : Set ι))ᶜ, blaschkeFactor (a i) z0) * g z0‖ ≤ M := by
      intro T
      refine norm_le_of_finset_factorization (f := f) (m := m) hM0 hM hab ha0 T
        ((differentiableOn_blaschkeProduct_compl hab ha0 hs T).mul hg) (fun z hz ↦ ?_) hz0
      rw [hfg z hz, blaschkeProduct_eq_finset_prod_mul_tprod_compl hab ha0 hs T
        (mem_ball_zero_iff.mp hz)]
      simp only [Pi.mul_apply]
      ring
    have hconvProd := (tendsto_finset_prod_blaschkeFactor hab ha0 hs
      (mem_ball_zero_iff.mp hz0)).comp hSseq
    have hSNz0 : ∀ N, ∏ i ∈ S N, blaschkeFactor (a i) z0 ≠ 0 := by
      intro N hcontra
      apply hBz0
      rw [blaschkeProduct_eq_finset_prod_mul_tprod_compl hab ha0 hs (S N)
        (mem_ball_zero_iff.mp hz0), hcontra, zero_mul]
    have heqh : ∀ N, (∏' i : ↑((S N : Set ι))ᶜ, blaschkeFactor (a i) z0) * g z0 =
        blaschkeProduct a z0 / (∏ i ∈ S N, blaschkeFactor (a i) z0) * g z0 := by
      intro N
      congr 1
      rw [eq_div_iff (hSNz0 N),
        blaschkeProduct_eq_finset_prod_mul_tprod_compl hab ha0 hs (S N) (mem_ball_zero_iff.mp hz0)]
      ring
    have htendh : Tendsto
        (fun N ↦ (∏' i : ↑((S N : Set ι))ᶜ, blaschkeFactor (a i) z0) * g z0)
        atTop (𝓝 (g z0)) := by
      have hd : Tendsto (fun N ↦ blaschkeProduct a z0 / (∏ i ∈ S N, blaschkeFactor (a i) z0)
          * g z0) atTop (𝓝 (blaschkeProduct a z0 / blaschkeProduct a z0 * g z0)) :=
        (Tendsto.div tendsto_const_nhds hconvProd hBz0).mul tendsto_const_nhds
      rw [div_self hBz0, one_mul] at hd
      simpa only [heqh] using hd
    exact le_of_tendsto htendh.norm (Eventually.of_forall fun N ↦ hbound (S N))
  intro z0 hz0
  by_cases hBz0 : blaschkeProduct a z0 ≠ 0
  · exact caseA z0 hz0 hBz0
  · push Not at hBz0
    have hne : NeBot (𝓝[≠] z0) := by infer_instance
    have hnloc : ¬ blaschkeProduct a =ᶠ[𝓝 z0] 0 := by
      intro hev
      obtain ⟨z₁, hz₁, hBz₁⟩ := hBne
      exact hBz₁ (hBan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball (0:ℂ) 1).isPreconnected hz0 hev hz₁)
    have hisol := ((hBan z0 hz0).eventually_eq_zero_or_eventually_ne_zero).resolve_left hnloc
    have heventually : ∀ᶠ z in 𝓝[≠] z0, ‖g z‖ ≤ M := by
      have h1 : ∀ᶠ z in 𝓝[≠] z0, z ≠ z0 → blaschkeProduct a z ≠ 0 :=
        eventually_nhdsWithin_iff.mp hisol |>.filter_mono nhdsWithin_le_nhds
      have hballnhds : ball (0 : ℂ) 1 ∈ 𝓝 z0 :=
        mem_nhds_iff.mpr ⟨ball 0 1, subset_rfl, isOpen_ball, hz0⟩
      have h2 : ∀ᶠ z in 𝓝[≠] z0, z ∈ ball (0 : ℂ) 1 :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds hballnhds
      filter_upwards [h1, h2, self_mem_nhdsWithin] with z hz1 hz2 hz3
      exact caseA z hz2 (hz1 hz3)
    have hganAt : AnalyticAt ℂ g z0 := (hg.analyticOnNhd isOpen_ball) z0 hz0
    have hcont : Tendsto g (𝓝[≠] z0) (𝓝 (g z0)) :=
      hganAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto hcont.norm heventually

end

/-- **The Riesz factorization theorem.** A bounded holomorphic function on the disc, not
identically zero, factors as `f = z ^ m * B * g` where `B` is the Blaschke product of the
zeros of `f` counted with multiplicity and `g` is holomorphic, nonvanishing, and bounded on
the disc by the same bound as `f`. -/
theorem exists_rieszFactorization {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    {M : ℝ} (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) (hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) :
    ∃ (ι : Type) (_ : Countable ι) (a : ι → ℂ) (m : ℕ) (g : ℂ → ℂ),
      (∀ i, a i ≠ 0) ∧ (∀ i, ‖a i‖ < 1) ∧ Summable (fun i ↦ 1 - ‖a i‖) ∧ (∀ i, f (a i) = 0) ∧
      DifferentiableOn ℂ g (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ M) ∧
      ∀ z ∈ ball (0 : ℂ) 1, f z = z ^ m * blaschkeProduct a z * g z := by
  classical
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  have hpc : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball _ _).isPreconnected
  have htopw : ∀ w ∈ ball (0 : ℂ) 1, analyticOrderAt f w ≠ ⊤ :=
    fun w hw ↦ hfan.analyticOrderAt_ne_top_of_exists_ne_zero hpc hne hw
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (htopw 0 (mem_ball_self one_pos))
  -- enumerate the nonzero zeros with multiplicity
  set ZS : Set ℂ := {w : ℂ | ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0}
  set n : ℂ → ℕ := fun w ↦ (analyticOrderAt f w).toNat
  have hn : ∀ w ∈ ball (0 : ℂ) 1, (n w : ℕ∞) = analyticOrderAt f w :=
    fun w hw ↦ ENat.natCast_toNat (htopw w hw)
  let ι := Σ w : ZS, Fin (n w)
  let a : ι → ℂ := fun i ↦ i.1
  have ha0 : ∀ i, a i ≠ 0 := fun i ↦ i.1.2.2.2
  have hab : ∀ i, ‖a i‖ < 1 := fun i ↦ i.1.2.1
  have hfa : ∀ i, f (a i) = 0 := fun i ↦ i.1.2.2.1
  have hcount : Countable ι := by
    have : Countable ZS := ((hfan.countable_zeros hpc hne).mono fun w (hw : w ∈ ZS) ↦
      (⟨mem_ball_zero_iff.mpr hw.1, hw.2.1⟩ : w ∈ {z ∈ ball 0 1 | f z = 0})).to_subtype
    infer_instance
  -- summability of `1 - ‖a i‖` over `ι`
  have hs : Summable fun i : ι ↦ 1 - ‖a i‖ := by
    rw [summable_sigma_of_nonneg fun i ↦ sub_nonneg.mpr (hab i).le]
    refine ⟨fun w ↦ (hasSum_fintype _).summable, ?_⟩
    exact (summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded hf hM hne).congr
      fun w ↦ by simp [a, n, tsum_fintype, mul_sub]
  -- the orders of `z ^ m * B` match those of `f`
  have hBan : AnalyticOnNhd ℂ (blaschkeProduct a) (ball 0 1) :=
    (differentiableOn_blaschkeProduct hab ha0 hs).analyticOnNhd isOpen_ball
  have hordmatch : ∀ w ∈ ball (0 : ℂ) 1,
      analyticOrderAt (fun z ↦ z ^ m * blaschkeProduct a z) w = analyticOrderAt f w := by
    intro w hw
    have hpow : AnalyticAt ℂ (fun z : ℂ ↦ z ^ m) w := analyticAt_id.pow m
    rw [show (fun z : ℂ ↦ z ^ m * blaschkeProduct a z) = (fun z : ℂ ↦ z ^ m) * blaschkeProduct a
      from rfl, analyticOrderAt_mul hpow (hBan w hw),
      analyticOrderAt_blaschkeProduct hab ha0 hs (mem_ball_zero_iff.mp hw),
      ← Set.ncard_eq_toFinset_card _ (finite_setOf_eq_of_summable hs (mem_ball_zero_iff.mp hw)),
      Set.ncard_sigma_fin_fiber]
    by_cases hw0 : w = 0
    · subst hw0
      have h1 : analyticOrderAt (fun z : ℂ ↦ z ^ m) (0 : ℂ) = m := by
        rw [show (fun z : ℂ ↦ z ^ m) = (id : ℂ → ℂ) ^ m from rfl,
          analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
        simp
      simp [ZS, h1, hm]
    · rw [hpow.analyticOrderAt_eq_zero.mpr (pow_ne_zero m hw0), zero_add]
      split_ifs with hwZ
      · exact hn w hw
      · rw [(hfan w hw).analyticOrderAt_eq_zero.mpr fun h ↦
          hwZ ⟨mem_ball_zero_iff.mp hw, h, hw0⟩]
        rfl
  -- divide `f` by `z ^ m * B`
  have hBan' : AnalyticOnNhd ℂ (fun z ↦ z ^ m * blaschkeProduct a z) (ball 0 1) :=
    fun z hz ↦ (analyticAt_id.pow m).mul (hBan z hz)
  have hBne : ∃ z ∈ ball (0 : ℂ) 1, z ^ m * blaschkeProduct a z ≠ 0 := by
    obtain ⟨z₀, hz₀, hfz₀⟩ := hne
    refine ⟨z₀, hz₀, (hBan' z₀ hz₀).analyticOrderAt_eq_zero.mp ?_⟩
    rw [hordmatch z₀ hz₀]
    exact (hfan z₀ hz₀).analyticOrderAt_eq_zero.mpr hfz₀
  obtain ⟨g, hg, hgne, hfg⟩ := hfan.exists_ne_zero_mul_of_analyticOrderAt_eq hBan' isOpen_ball
    hpc hBne hordmatch
  have hfg' : ∀ z ∈ ball (0 : ℂ) 1, f z = z ^ m * blaschkeProduct a z * g z := fun z hz ↦ by
    rw [hfg z hz]
    ring
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (mem_ball_self one_pos))
  have hBne' : ∃ z ∈ ball (0 : ℂ) 1, blaschkeProduct a z ≠ 0 := by
    obtain ⟨z₀, hz₀, hBz₀⟩ := hBne
    exact ⟨z₀, hz₀, right_ne_zero_of_mul hBz₀⟩
  exact ⟨ι, hcount, a, m, g, ha0, hab, hs, hfa, hg.differentiableOn, hgne,
    norm_le_of_blaschkeProduct_bounded hM0 hM ha0 hab hs hBne' hg.differentiableOn hfg', hfg'⟩

end Complex

end
