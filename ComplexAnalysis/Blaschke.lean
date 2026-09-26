/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.DiscMobius
public import ComplexAnalysis.InfiniteProduct
public import ComplexAnalysis.Hadamard

/-!
# Blaschke products and the Blaschke condition

The Blaschke factor `b_a z = (‖a‖ / a) * (a - z) / (1 - conj a * z)` for `0 < ‖a‖ < 1` is a
disc Möbius transformation normalized by `b_a 0 = ‖a‖ > 0`; it satisfies
`‖1 - b_a z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) * (1 - ‖a‖)` on the disc. Hence for a family `a i` of
nonzero points of the disc with `∑ (1 - ‖a i‖) < ∞` the **Blaschke product** `∏' i, b_{a i} z`
converges locally uniformly on the disc to a holomorphic function of modulus at most one whose
zeros are exactly the `a i`, with the right multiplicities.

Conversely, the **Blaschke condition** (F. Riesz): the nonzero zeros `w` of a bounded holomorphic
function on the disc, not identically zero, satisfy `∑ (1 - ‖w‖) < ∞`. This follows from
Jensen's formula (Mathlib). As a corollary, a bounded holomorphic function vanishing on a
family `a i` with `∑ (1 - ‖a i‖) = ∞` vanishes identically.

## Main definitions

* `Complex.blaschkeFactor a z`, `Complex.blaschkeProduct a z`.

## Main results

* `Complex.differentiableOn_blaschkeProduct`, `Complex.blaschkeProduct_eq_zero_iff`,
  `Complex.analyticOrderAt_blaschkeProduct`, `Complex.norm_blaschkeProduct_le_one`.
* `Complex.summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded`: the
  multiplicity-weighted Blaschke condition.
* `Complex.summable_one_sub_norm_of_bounded`: the unweighted Blaschke condition.
* `Complex.eqOn_zero_of_not_summable`: the uniqueness theorem.

## References

* B. Simon, *Basic Complex Analysis*, Section 9.9.
* J. B. Conway, *Functions of One Complex Variable II*, Section 20.2.
* J. B. Conway, *Functions of One Complex Variable I*, Exercise VII.5.
-/

@[expose] public noncomputable section

open Set Metric Filter Function MeromorphicOn Real
open scoped Topology ComplexConjugate

namespace Complex

/-- The Blaschke factor `(‖a‖ / a) * (a - z) / (1 - conj a * z)`. -/
def blaschkeFactor (a z : ℂ) : ℂ := (‖a‖ / a) * (a - z) / (1 - conj a * z)

variable {a z : ℂ}

/-- A Blaschke factor is the disc Möbius map multiplied by its normalizing scalar. -/
theorem blaschkeFactor_eq_mul_discMobius (a z : ℂ) :
    blaschkeFactor a z = -(‖a‖ / a) * discMobius a z := by
  rw [blaschkeFactor, discMobius, mul_div_assoc, neg_mul, ← mul_neg, ← neg_div, neg_sub]

/-- For a nonzero parameter, the Blaschke factor at the origin is the norm of the parameter. -/
theorem blaschkeFactor_zero_right (ha0 : a ≠ 0) : blaschkeFactor a 0 = ‖a‖ := by
  rw [blaschkeFactor]
  field_simp
  ring

/-- For a nonzero parameter, the scalar normalizing a Blaschke factor has norm one. -/
theorem norm_neg_norm_div (ha0 : a ≠ 0) : ‖-((‖a‖ : ℂ) / a)‖ = 1 := by
  rw [norm_neg, norm_div, norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr ha0)]

/-- For a nonzero parameter, the Blaschke factor and its disc Möbius map have the same norm. -/
theorem norm_blaschkeFactor (a z : ℂ) (ha0 : a ≠ 0) :
    ‖blaschkeFactor a z‖ = ‖discMobius a z‖ := by
  rw [blaschkeFactor_eq_mul_discMobius, norm_mul, norm_neg_norm_div ha0, one_mul]

/-- A Blaschke factor with nonzero parameter in the open unit disc has norm less than one there. -/
theorem norm_blaschkeFactor_lt_one (ha : ‖a‖ < 1) (ha0 : a ≠ 0) (hz : ‖z‖ < 1) :
    ‖blaschkeFactor a z‖ < 1 := by
  rw [norm_blaschkeFactor a z ha0]
  exact norm_discMobius_lt_one ha hz

/-- A Blaschke factor with nonzero parameter in the open unit disc has norm at most one on the
closed unit disc. -/
theorem norm_blaschkeFactor_le_one (ha : ‖a‖ < 1) (ha0 : a ≠ 0) (hz : ‖z‖ ≤ 1) :
    ‖blaschkeFactor a z‖ ≤ 1 := by
  rw [norm_blaschkeFactor a z ha0]
  exact norm_discMobius_le_one ha hz

/-- For a nonzero parameter in the open unit disc, the unique zero of its Blaschke factor on the
closed unit disc is the parameter itself. -/
theorem blaschkeFactor_eq_zero_iff (ha : ‖a‖ < 1) (ha0 : a ≠ 0) (hz : ‖z‖ ≤ 1) :
    blaschkeFactor a z = 0 ↔ z = a := by
  rw [blaschkeFactor_eq_mul_discMobius, mul_eq_zero, or_iff_right, discMobius_eq_zero_iff
    (one_sub_conj_mul_ne_zero ha hz)]
  exact neg_ne_zero.mpr (div_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr ha0) ha0)

/-- A Blaschke factor with parameter in the open unit disc is holomorphic on that disc. -/
theorem differentiableOn_blaschkeFactor_ball (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (blaschkeFactor a) (ball 0 1) := by
  have : blaschkeFactor a = fun z ↦ -(‖a‖ / a) * discMobius a z :=
    funext (blaschkeFactor_eq_mul_discMobius a)
  rw [this]
  exact (differentiableOn_discMobius_ball ha).const_mul _

/-- The Blaschke factor vanishes to first order at `a`. -/
theorem analyticOrderAt_blaschkeFactor_self (ha : ‖a‖ < 1) (ha0 : a ≠ 0) :
    analyticOrderAt (blaschkeFactor a) a = 1 := by
  have hfun : blaschkeFactor a = (fun _ ↦ -(‖a‖ / a : ℂ)) * discMobius a :=
    funext (blaschkeFactor_eq_mul_discMobius a)
  have hc : -((‖a‖ : ℂ) / a) ≠ 0 := by
    rw [neg_ne_zero, div_ne_zero_iff]
    exact ⟨by exact_mod_cast (norm_ne_zero_iff.mpr ha0), ha0⟩
  have hd : AnalyticAt ℂ (discMobius a) a :=
    (differentiableOn_discMobius_ball ha).analyticOnNhd isOpen_ball a (mem_ball_zero_iff.mpr ha)
  rw [hfun, analyticOrderAt_mul analyticAt_const hd,
    (analyticAt_const.analyticOrderAt_eq_zero).mpr hc, zero_add]
  refine hd.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (discMobius_self a) ?_
  rw [deriv_discMobius_self ha]
  refine inv_ne_zero ?_
  rw [sub_ne_zero]
  intro h
  have h' : normSq a = 1 := by exact_mod_cast h.symm
  rw [normSq_eq_norm_sq] at h'
  nlinarith [norm_nonneg a]

/-- **The basic estimate.** `‖1 - b_a z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) * (1 - ‖a‖)` on the disc. -/
theorem norm_one_sub_blaschkeFactor_le (ha : ‖a‖ < 1) (ha0 : a ≠ 0) (hz : ‖z‖ < 1) :
    ‖1 - blaschkeFactor a z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) * (1 - ‖a‖) := by
  have hd := one_sub_conj_mul_ne_zero ha hz.le
  have hid : 1 - blaschkeFactor a z =
      (1 - ‖a‖) * (a + ‖a‖ * z) / (a * (1 - conj a * z)) := by
    have h1 : conj a * a = ((‖a‖ : ℂ)) ^ 2 := conj_mul' a
    have hX : blaschkeFactor a z = (‖a‖ * (a - z)) / (a * (1 - conj a * z)) := by
      rw [blaschkeFactor, div_mul_eq_mul_div, div_div]
    rw [hX, one_sub_div (mul_ne_zero ha0 hd)]
    congr 1
    linear_combination (-(z : ℂ)) * h1
  have hnum : ‖a + ‖a‖ * z‖ ≤ ‖a‖ * (1 + ‖z‖) := by
    calc ‖a + ‖a‖ * z‖ ≤ ‖a‖ + ‖(‖a‖ : ℂ) * z‖ := norm_add_le _ _
      _ = ‖a‖ * (1 + ‖z‖) := by
          rw [norm_mul, norm_real, Real.norm_of_nonneg (norm_nonneg _)]
          ring
  have hden : 1 - ‖z‖ ≤ ‖1 - conj a * z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (conj a * z)
    rw [norm_one, norm_mul, norm_conj] at this
    nlinarith [norm_nonneg a, norm_nonneg z, mul_le_mul_of_nonneg_right ha.le (norm_nonneg z)]
  have hz1 : 0 < 1 - ‖z‖ := by linarith
  have ha1 : 0 ≤ 1 - ‖a‖ := by linarith
  have ha0' : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have h1a : ‖(1 : ℂ) - ‖a‖‖ = 1 - ‖a‖ := by
    rw [show (1 : ℂ) - ‖a‖ = ((1 - ‖a‖ : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg ha1]
  rw [hid, norm_div, norm_mul, norm_mul, h1a, div_le_iff₀ (by positivity)]
  calc (1 - ‖a‖) * ‖a + ‖a‖ * z‖ ≤ (1 - ‖a‖) * (‖a‖ * (1 + ‖z‖)) := by gcongr
    _ = (1 + ‖z‖) / (1 - ‖z‖) * (1 - ‖a‖) * (‖a‖ * (1 - ‖z‖)) := by
        field_simp
    _ ≤ (1 + ‖z‖) / (1 - ‖z‖) * (1 - ‖a‖) * (‖a‖ * ‖1 - conj a * z‖) := by gcongr

variable {ι : Type*} {a : ι → ℂ}

/-- The Blaschke product with zeros `a i`. -/
def blaschkeProduct (a : ι → ℂ) (z : ℂ) : ℂ := ∏' i, blaschkeFactor (a i) z

/-- Every value in the disc is taken finitely often by a family with `∑ (1 - ‖a i‖) < ∞`. -/
theorem finite_setOf_eq_of_summable (hs : Summable fun i ↦ 1 - ‖a i‖) {w : ℂ} (hw : ‖w‖ < 1) :
    {i | a i = w}.Finite := by
  have h := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (sub_pos.mpr hw))
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun i hi ↦ ?_
  have : a i = w := hi
  change ¬ (1 - ‖a i‖ < 1 - ‖w‖)
  rw [this]
  exact lt_irrefl _

/-- The terms `b_{a i} z - 1` have summable uniform bounds on every compact subset of the
disc. -/
theorem hasSummableBoundOn_blaschke (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ 1 - ‖a i‖) :
    HasSummableBoundOn (fun i z ↦ blaschkeFactor (a i) z - 1) (ball 0 1) := by
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨fun _ ↦ 0, summable_zero, Eventually.of_forall fun i z hz ↦ by simp [hKe] at hz⟩
  obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
  set r : ℝ := ‖z₀‖
  have hr1 : r < 1 := mem_ball_zero_iff.mp (hKU hz₀)
  have hr0 : 0 ≤ r := norm_nonneg _
  refine ⟨fun i ↦ (1 + r) / (1 - r) * (1 - ‖a i‖), hs.mul_left _,
    Eventually.of_forall fun i z hz ↦ ?_⟩
  have hzr : ‖z‖ ≤ r := hmax hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hKU hz)
  calc ‖blaschkeFactor (a i) z - 1‖ = ‖1 - blaschkeFactor (a i) z‖ := norm_sub_rev _ _
    _ ≤ (1 + ‖z‖) / (1 - ‖z‖) * (1 - ‖a i‖) :=
        norm_one_sub_blaschkeFactor_le (ha i) (ha0 i) hz1
    _ ≤ (1 + r) / (1 - r) * (1 - ‖a i‖) := by
        have h1 : 1 - ‖a i‖ ≥ 0 := by linarith [ha i]
        refine mul_le_mul_of_nonneg_right ?_ h1
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith

/-- A Blaschke product can be written as a product of factors of the form `1 + f i z`. -/
theorem blaschkeProduct_eq_tprod_one_add (z : ℂ) :
    blaschkeProduct a z = ∏' i, (1 + (blaschkeFactor (a i) z - 1)) := by
  simp [blaschkeProduct]

/-- Subtracting one from each Blaschke factor preserves holomorphy on the open unit disc. -/
theorem differentiableOn_blaschkeFactor_sub_one (ha : ∀ i, ‖a i‖ < 1) (i : ι) :
    DifferentiableOn ℂ (fun z ↦ blaschkeFactor (a i) z - 1) (ball 0 1) :=
  (differentiableOn_blaschkeFactor_ball (ha i)).sub_const 1

/-- **The Blaschke product is holomorphic on the disc.** -/
theorem differentiableOn_blaschkeProduct (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ 1 - ‖a i‖) :
    DifferentiableOn ℂ (blaschkeProduct a) (ball 0 1) := by
  have : blaschkeProduct a = fun z ↦ ∏' i, (1 + (blaschkeFactor (a i) z - 1)) :=
    funext blaschkeProduct_eq_tprod_one_add
  rw [this]
  exact differentiableOn_tprod_one_add isOpen_ball (differentiableOn_blaschkeFactor_sub_one ha)
    (hasSummableBoundOn_blaschke ha ha0 hs)

/-- **The zeros of the Blaschke product** are exactly the `a i`. -/
theorem blaschkeProduct_eq_zero_iff (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ 1 - ‖a i‖) {z : ℂ} (hz : ‖z‖ < 1) :
    blaschkeProduct a z = 0 ↔ ∃ i, z = a i := by
  rw [blaschkeProduct_eq_tprod_one_add, tprod_one_add_eq_zero_iff
    (hasSummableBoundOn_blaschke ha ha0 hs) (mem_ball_zero_iff.mpr hz)]
  simp only [add_sub_cancel]
  exact exists_congr fun i ↦ blaschkeFactor_eq_zero_iff (ha i) (ha0 i) hz.le

/-- **Orders of the Blaschke product.** The order at a point `w` of the disc is the number of
`i` with `a i = w`. -/
theorem analyticOrderAt_blaschkeProduct (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ 1 - ‖a i‖) {w : ℂ} (hw : ‖w‖ < 1) :
    analyticOrderAt (blaschkeProduct a) w =
      ((finite_setOf_eq_of_summable hs hw).toFinset.card : ℕ∞) := by
  classical
  have hb := hasSummableBoundOn_blaschke ha ha0 hs
  have hwb : w ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hw
  have hfun : blaschkeProduct a = fun z ↦ ∏' i, (1 + (blaschkeFactor (a i) z - 1)) :=
    funext blaschkeProduct_eq_tprod_one_add
  rw [hfun, analyticOrderAt_tprod_one_add isOpen_ball (differentiableOn_blaschkeFactor_sub_one ha)
    hb hwb]
  have hset : (finite_setOf_one_add_eq_zero hb hwb).toFinset =
      (finite_setOf_eq_of_summable hs hw).toFinset := by
    ext i
    simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, add_sub_cancel,
      blaschkeFactor_eq_zero_iff (ha i) (ha0 i) hw.le]
    exact eq_comm
  rw [hset, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Set.Finite.mem_toFinset, mem_ofPred_eq] at hi
  simp only [add_sub_cancel, Nat.cast_one]
  rw [← hi]
  exact analyticOrderAt_blaschkeFactor_self (ha i) (ha0 i)

/-- A product of factors of modulus at most one has modulus at most one. -/
theorem norm_tprod_le_one {g : ι → ℂ} (hg : Multipliable g) (h : ∀ i, ‖g i‖ ≤ 1) :
    ‖∏' i, g i‖ ≤ 1 := by
  have ht : Tendsto (fun F : Finset ι ↦ ‖∏ i ∈ F, g i‖) atTop (𝓝 ‖∏' i, g i‖) :=
    Filter.Tendsto.norm hg.hasProd
  refine le_of_tendsto ht (Eventually.of_forall fun F ↦ ?_)
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i _ ↦ norm_nonneg _) fun i _ ↦ h i

/-- **The Blaschke product has modulus at most one** on the disc. -/
theorem norm_blaschkeProduct_le_one (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i ↦ 1 - ‖a i‖) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖blaschkeProduct a z‖ ≤ 1 := by
  have hsum := (hasSummableBoundOn_blaschke ha ha0 hs).summable_norm (mem_ball_zero_iff.mpr hz)
  have hmul : Multipliable fun i ↦ blaschkeFactor (a i) z := by
    have := multipliable_one_add_of_summable (f := fun i ↦ blaschkeFactor (a i) z - 1) hsum
    exact this.congr fun i ↦ add_sub_cancel _ _
  exact norm_tprod_le_one hmul fun i ↦ norm_blaschkeFactor_le_one (ha i) (ha0 i) hz.le

/-! ### The Blaschke condition -/

variable {f : ℂ → ℂ}

/-- Jensen's formula bounds the logarithmic zero sum on each smaller disc by the
boundary norm bound and the value at the origin. -/
private theorem jensen_divisor_sum_le (hf : DifferentiableOn ℂ f (ball 0 1))
    {M : ℝ} (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) (h0 : f 0 ≠ 0)
    {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) :
    ∑ᶠ u, ((divisor f (closedBall 0 R) u : ℤ) : ℝ) *
      Real.log (R * ‖(0 : ℂ) - u‖⁻¹) ≤ Real.log (max 1 M) - Real.log ‖f 0‖ := by
  have hfan := hf.analyticOnNhd isOpen_ball
  have hR : |R| = R := abs_of_pos hR0
  have hfR : AnalyticOnNhd ℂ f (closedBall 0 |R|) := by
    rw [hR]; exact hfan.mono (closedBall_subset_ball hR1)
  have hJ := hfR.circleAverage_log_norm hR0.ne' h0
  have hlog : circleAverage (fun z ↦ Real.log ‖f z‖) 0 R ≤ Real.log (max 1 M) := by
    refine circleAverage_mono_on_of_le_circle
      ((hfR.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm)
      fun z hz ↦ ?_
    rw [hR, mem_sphere_zero_iff_norm] at hz
    have hzb : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (by rw [hz]; exact hR1)
    rcases eq_or_ne ‖f z‖ 0 with h | h
    · rw [h, Real.log_zero]; exact Real.log_nonneg (le_max_left _ _)
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))
        ((hM z hzb).trans (le_max_right _ _))
  rw [hR] at hJ
  linarith

/-- The weighted logarithmic zero sum over any finite set of zeros inside the disc of radius
`R < 1` is bounded, via Jensen's formula, by `log (max 1 M) - log ‖f 0‖`. -/
private theorem sum_toNat_mul_log_le (hf : DifferentiableOn ℂ f (ball 0 1))
    {M : ℝ} (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) (h0 : f 0 ≠ 0) {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1)
    (S : Finset {w : ℂ // ‖w‖ < 1 ∧ f w = 0}) (hwR : ∀ w ∈ S, ‖(w : ℂ)‖ ≤ R) :
    ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ) * Real.log (R * ‖(0 : ℂ) - (w : ℂ)‖⁻¹) ≤
      Real.log (max 1 M) - Real.log ‖f 0‖ := by
  classical
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  have htop : ∀ w : ℂ, ‖w‖ < 1 → analyticOrderAt f w ≠ ⊤ := fun w hw ↦
    hfan.analyticOrderAt_ne_top_of_exists_ne_zero (convex_ball _ _).isPreconnected
      ⟨0, mem_ball_self one_pos, h0⟩ (mem_ball_zero_iff.mpr hw)
  have hfR : AnalyticOnNhd ℂ f (closedBall 0 R) := hfan.mono (closedBall_subset_ball hR1)
  set D := divisor f (closedBall 0 R)
  have hDfin := D.finiteSupport (isCompact_closedBall 0 R)
  set T := hDfin.toFinset
  set g : ℂ → ℝ := fun u ↦ ((D u : ℤ) : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹)
  have hDeq : ∀ w ∈ S, ((D (w : ℂ) : ℤ) : ℝ) = ((analyticOrderAt f w).toNat : ℝ) := by
    intro w hw
    rw [AnalyticOnNhd.divisor_apply hfR (mem_closedBall_zero_iff.mpr (hwR w hw))]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (htop w w.2.1)
    rw [← hn]
    simp
  have hnonneg : ∀ u ∈ T, 0 ≤ g u := by
    intro u hu
    have huD : u ∈ closedBall (0 : ℂ) R :=
      D.supportWithinDomain ((Set.Finite.mem_toFinset _).mp hu)
    refine mul_nonneg ?_ ?_
    · rw [AnalyticOnNhd.divisor_apply hfR huD]
      generalize analyticOrderAt f u = o
      induction o using ENat.recTopCoe <;> simp
    · rcases eq_or_ne u 0 with rfl | hu0
      · simp
      · rw [zero_sub, norm_neg]
        apply Real.log_nonneg
        rw [le_mul_inv_iff₀ (norm_pos_iff.mpr hu0), one_mul]
        exact mem_closedBall_zero_iff.mp huD
  have himg : S.image (fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0} ↦ (w : ℂ)) ⊆ T := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    rw [Set.Finite.mem_toFinset, mem_support]
    intro h
    have hne : analyticOrderAt f w ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hfan w (mem_ball_zero_iff.mpr w.2.1), w.2.2⟩
    have := hDeq w hw
    rw [h, Int.cast_zero, eq_comm, Nat.cast_eq_zero, ENat.toNat_eq_zero] at this
    exact this.elim hne (htop w w.2.1)
  calc ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ) * Real.log (R * ‖(0 : ℂ) - (w : ℂ)‖⁻¹)
      = ∑ w ∈ S, g (w : ℂ) := Finset.sum_congr rfl fun w hw ↦ by simp only [g, hDeq w hw]
    _ = ∑ u ∈ S.image (fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0} ↦ (w : ℂ)), g u :=
        (Finset.sum_image fun w _ w' _ h ↦ Subtype.val_injective h).symm
    _ ≤ ∑ u ∈ T, g u := Finset.sum_le_sum_of_subset_of_nonneg himg fun u hu _ ↦ hnonneg u hu
    _ = ∑ᶠ u, g u := (finsum_eq_sum_of_support_subset g fun u hu ↦
        (Set.Finite.mem_toFinset _).mpr fun h ↦ hu (by simp [g, h])).symm
    _ ≤ _ := jensen_divisor_sum_le hf hM h0 hR0 hR1

/-- **The multiplicity-weighted Blaschke condition**, at a point where `f` does not vanish.
The zeros of a bounded holomorphic function on the disc with `f 0 ≠ 0`, weighted by their
multiplicity, satisfy `∑ ord(w) (1 - ‖w‖) < ∞`. -/
theorem summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded_of_ne_zero
    (hf : DifferentiableOn ℂ f (ball 0 1)) {M : ℝ} (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M)
    (h0 : f 0 ≠ 0) :
    Summable fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0} ↦
      ((analyticOrderAt f w).toNat : ℝ) * (1 - ‖(w : ℂ)‖) := by
  classical
  set K : ℝ := Real.log (max 1 M) - Real.log ‖f 0‖
  have hK0 : 0 ≤ K := sub_nonneg.mpr (Real.log_le_log (norm_pos_iff.mpr h0)
    ((hM 0 (mem_ball_self one_pos)).trans (le_max_right _ _)))
  refine summable_of_sum_le (fun w ↦ mul_nonneg (Nat.cast_nonneg _)
    (sub_nonneg.mpr w.2.1.le)) (c := K) fun S ↦ le_of_forall_pos_le_add fun ε hε ↦ ?_
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.sum_empty]; linarith
  -- choose `R < 1` beyond the zeros in `S` with `log R ≥ -η`
  set nS : ℝ := ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ)
  have hnS0 : 0 ≤ nS := Finset.sum_nonneg fun w _ ↦ by positivity
  set η : ℝ := ε / (nS + 1)
  have hη : 0 < η := by positivity
  set R : ℝ := max (S.sup' hS fun w ↦ ‖(w : ℂ)‖) (Real.exp (-η))
  have hR0 : 0 < R := lt_max_of_lt_right (Real.exp_pos _)
  have hR1 : R < 1 := max_lt ((Finset.sup'_lt_iff hS).mpr fun w _ ↦ w.2.1)
    (Real.exp_lt_one_iff.mpr (by linarith))
  have hwR : ∀ w ∈ S, ‖(w : ℂ)‖ ≤ R := fun w hw ↦
    (Finset.le_sup' (fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0} ↦ ‖(w : ℂ)‖) hw).trans
      (le_max_left _ _)
  -- termwise: `1 - ‖w‖ ≤ log (R / ‖w‖) + η`
  have hterm : ∀ w ∈ S, 1 - ‖(w : ℂ)‖ ≤ Real.log (R * ‖(0 : ℂ) - (w : ℂ)‖⁻¹) + η := by
    intro w _
    have hwpos : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr fun h ↦ h0 (by simpa [h] using w.2.2)
    rw [zero_sub, norm_neg, Real.log_mul hR0.ne' (inv_ne_zero hwpos.ne'), Real.log_inv]
    have h1 : Real.log ‖(w : ℂ)‖ ≤ ‖(w : ℂ)‖ - 1 := Real.log_le_sub_one_of_pos hwpos
    have h2 : -η ≤ Real.log R := by
      rw [← Real.log_exp (-η)]; exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
    linarith
  have hcard : nS * η ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    linarith
  calc ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ) * (1 - ‖(w : ℂ)‖)
      ≤ ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ) *
          (Real.log (R * ‖(0 : ℂ) - (w : ℂ)‖⁻¹) + η) :=
        Finset.sum_le_sum fun w hw ↦ mul_le_mul_of_nonneg_left (hterm w hw) (by positivity)
    _ = ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ) * Real.log (R * ‖(0 : ℂ) - (w : ℂ)‖⁻¹)
          + nS * η := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun w _ ↦ by ring
    _ ≤ K + ε := by linarith [sum_toNat_mul_log_le hf hM h0 hR0 hR1 S hwR]

/-- **The multiplicity-weighted Blaschke condition**, general form. The nonzero zeros of a
bounded holomorphic function on the disc that is not identically zero, weighted by their
multiplicity, satisfy `∑ ord(w) (1 - ‖w‖) < ∞`. -/
theorem summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded
    (hf : DifferentiableOn ℂ f (ball 0 1)) {M : ℝ} (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M)
    (hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) :
    Summable fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0} ↦
      ((analyticOrderAt f w).toNat : ℝ) * (1 - ‖(w : ℂ)‖) := by
  classical
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  -- divide out the zero at the origin: `f z = z ^ m * g z`
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (hfan.analyticOrderAt_ne_top_of_exists_ne_zero (convex_ball _ _).isPreconnected hne h0)
  obtain ⟨g, hg, hg0, hfg⟩ := hfan.exists_eq_sub_pow_mul h0 hm.symm
  simp only [sub_zero] at hfg
  -- `g` is bounded on the disc
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (hg.continuousOn.mono (closedBall_subset_ball (by norm_num)))
  have hMg : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ max M₀ (M * 2 ^ m) := by
    intro z hz
    rcases le_or_gt ‖z‖ (1 / 2) with hz2 | hz2
    · exact (hM₀ z (mem_closedBall_zero_iff.mpr hz2)).trans (le_max_left _ _)
    · have hzpos : 0 < ‖z‖ := by linarith
      refine le_trans ?_ (le_max_right _ _)
      rw [← mul_le_mul_iff_of_pos_left (pow_pos hzpos m), ← norm_pow, ← norm_mul, ← hfg z hz]
      have h2 : (1 : ℝ) ≤ 2 ^ m * ‖z‖ ^ m := by
        rw [← mul_pow]; exact one_le_pow₀ (by linarith)
      calc ‖f z‖ ≤ M := hM z hz
        _ ≤ M * (2 ^ m * ‖z‖ ^ m) := le_mul_of_one_le_right ((norm_nonneg _).trans (hM z hz)) h2
        _ = ‖z ^ m‖ * (M * 2 ^ m) := by rw [norm_pow]; ring
  have hsum := summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded_of_ne_zero
    hg.differentiableOn hMg hg0
  -- the nonzero zeros and their orders agree for `f` and `g`
  have hfg' : ∀ w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0},
      g w = 0 ∧ analyticOrderAt f w = analyticOrderAt g w := by
    intro w
    have hw1 : (w : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr w.2.1
    have hpow : AnalyticAt ℂ (fun z : ℂ ↦ z ^ m) (w : ℂ) := analyticAt_id.pow m
    refine ⟨?_, ?_⟩
    · have := hfg w hw1
      rw [w.2.2.1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ w.2.2.2)
    · rw [analyticOrderAt_congr (Filter.eventually_of_mem (isOpen_ball.mem_nhds hw1) hfg),
        show (fun z : ℂ ↦ z ^ m * g z) = (fun z : ℂ ↦ z ^ m) * g from rfl,
        analyticOrderAt_mul hpow (hg _ hw1),
        hpow.analyticOrderAt_eq_zero.mpr (pow_ne_zero m w.2.2.2), zero_add]
  exact (hsum.comp_injective (i := fun w ↦ ⟨w, w.2.1, (hfg' w).1⟩)
    fun w w' h ↦ Subtype.ext (by simpa using congrArg Subtype.val h)).congr
    fun w ↦ by simp [(hfg' w).2]

/-- At a zero of finite order in the disc, `1 - ‖w‖ ≤ ord(w) (1 - ‖w‖)`. -/
private theorem one_sub_norm_le_toNat_mul (hf : DifferentiableOn ℂ f (ball 0 1))
    (hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) {w : ℂ} (hw : ‖w‖ < 1) (hfw : f w = 0) :
    1 - ‖w‖ ≤ ((analyticOrderAt f w).toNat : ℝ) * (1 - ‖w‖) := by
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  have hw' : w ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hw
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (hfan.analyticOrderAt_ne_top_of_exists_ne_zero (convex_ball _ _).isPreconnected hne hw')
  have hn0 : n ≠ 0 := fun h ↦ analyticOrderAt_ne_zero.mpr ⟨hfan w hw', hfw⟩ (by rw [← hn, h]; rfl)
  rw [← hn, ENat.toNat_natCast]
  exact le_mul_of_one_le_left (sub_nonneg.mpr hw.le)
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)

/-- **The Blaschke condition (F. Riesz).** The zeros of a bounded holomorphic function on the
disc with `f 0 ≠ 0` satisfy `∑ (1 - ‖w‖) < ∞`. -/
theorem summable_one_sub_norm_of_bounded_of_ne_zero (hf : DifferentiableOn ℂ f (ball 0 1))
    {M : ℝ} (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) (h0 : f 0 ≠ 0) :
    Summable fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0} ↦ 1 - ‖(w : ℂ)‖ :=
  (summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded_of_ne_zero hf hM h0).of_nonneg_of_le
    (fun w ↦ sub_nonneg.mpr w.2.1.le)
    fun w ↦ one_sub_norm_le_toNat_mul hf ⟨0, mem_ball_self one_pos, h0⟩ w.2.1 w.2.2

/-- **The Blaschke condition (F. Riesz), general form.** The nonzero zeros of a bounded
holomorphic function on the disc that is not identically zero satisfy `∑ (1 - ‖w‖) < ∞`. -/
theorem summable_one_sub_norm_of_bounded (hf : DifferentiableOn ℂ f (ball 0 1)) {M : ℝ}
    (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) (hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) :
    Summable fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0} ↦ 1 - ‖(w : ℂ)‖ :=
  (summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded hf hM hne).of_nonneg_of_le
    (fun w ↦ sub_nonneg.mpr w.2.1.le) fun w ↦ one_sub_norm_le_toNat_mul hf hne w.2.1 w.2.2.1

/-- **Uniqueness theorem.** A bounded holomorphic function on the disc vanishing on an injective
family of nonzero points `a i` with `∑ (1 - ‖a i‖) = ∞` vanishes identically. -/
theorem eqOn_zero_of_not_summable (hf : DifferentiableOn ℂ f (ball 0 1)) {M : ℝ}
    (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hinj : Injective a) (hfa : ∀ i, f (a i) = 0) (hns : ¬ Summable fun i ↦ 1 - ‖a i‖) :
    EqOn f 0 (ball 0 1) := by
  by_contra h
  have hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0 := by
    by_contra h'
    push Not at h'
    exact h fun z hz ↦ h' z hz
  apply hns
  exact (summable_one_sub_norm_of_bounded hf hM hne).comp_injective
    (i := fun i ↦ (⟨a i, ha i, hfa i, ha0 i⟩ : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0}))
    fun i j hij ↦ hinj (by simpa using congrArg Subtype.val hij)

end Complex

end
