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
* `Complex.summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded_of_ne_zero`:
  the multiplicity-weighted Blaschke condition when the origin is not a zero.
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
  have : blaschkeFactor a = fun z => -(‖a‖ / a) * discMobius a z :=
    funext (blaschkeFactor_eq_mul_discMobius a)
  rw [this]
  exact (differentiableOn_discMobius_ball ha).const_mul _

/-- The Blaschke factor vanishes to first order at `a`. -/
theorem analyticOrderAt_blaschkeFactor_self (ha : ‖a‖ < 1) (ha0 : a ≠ 0) :
    analyticOrderAt (blaschkeFactor a) a = 1 := by
  have hfun : blaschkeFactor a = (fun _ => -(‖a‖ / a : ℂ)) * discMobius a :=
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
theorem finite_setOf_eq_of_summable (hs : Summable fun i => 1 - ‖a i‖) {w : ℂ} (hw : ‖w‖ < 1) :
    {i | a i = w}.Finite := by
  have h := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (sub_pos.mpr hw))
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun i hi => ?_
  have : a i = w := hi
  change ¬ (1 - ‖a i‖ < 1 - ‖w‖)
  rw [this]
  exact lt_irrefl _

/-- The terms `b_{a i} z - 1` have summable uniform bounds on every compact subset of the
disc. -/
theorem hasSummableBoundOn_blaschke (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i => 1 - ‖a i‖) :
    HasSummableBoundOn (fun i z => blaschkeFactor (a i) z - 1) (ball 0 1) := by
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨fun _ => 0, summable_zero, Eventually.of_forall fun i z hz => by simp [hKe] at hz⟩
  obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
  set r : ℝ := ‖z₀‖ with hr_def
  have hr1 : r < 1 := mem_ball_zero_iff.mp (hKU hz₀)
  have hr0 : 0 ≤ r := norm_nonneg _
  refine ⟨fun i => (1 + r) / (1 - r) * (1 - ‖a i‖), hs.mul_left _,
    Eventually.of_forall fun i z hz => ?_⟩
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
    DifferentiableOn ℂ (fun z => blaschkeFactor (a i) z - 1) (ball 0 1) :=
  (differentiableOn_blaschkeFactor_ball (ha i)).sub_const 1

/-- **The Blaschke product is holomorphic on the disc.** -/
theorem differentiableOn_blaschkeProduct (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i => 1 - ‖a i‖) :
    DifferentiableOn ℂ (blaschkeProduct a) (ball 0 1) := by
  have : blaschkeProduct a = fun z => ∏' i, (1 + (blaschkeFactor (a i) z - 1)) :=
    funext blaschkeProduct_eq_tprod_one_add
  rw [this]
  exact differentiableOn_tprod_one_add isOpen_ball (differentiableOn_blaschkeFactor_sub_one ha)
    (hasSummableBoundOn_blaschke ha ha0 hs)

/-- **The zeros of the Blaschke product** are exactly the `a i`. -/
theorem blaschkeProduct_eq_zero_iff (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i => 1 - ‖a i‖) {z : ℂ} (hz : ‖z‖ < 1) :
    blaschkeProduct a z = 0 ↔ ∃ i, z = a i := by
  rw [blaschkeProduct_eq_tprod_one_add, tprod_one_add_eq_zero_iff
    (hasSummableBoundOn_blaschke ha ha0 hs) (mem_ball_zero_iff.mpr hz)]
  simp only [add_sub_cancel]
  exact exists_congr fun i => blaschkeFactor_eq_zero_iff (ha i) (ha0 i) hz.le

/-- **Orders of the Blaschke product.** The order at a point `w` of the disc is the number of
`i` with `a i = w`. -/
theorem analyticOrderAt_blaschkeProduct (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i => 1 - ‖a i‖) {w : ℂ} (hw : ‖w‖ < 1) :
    analyticOrderAt (blaschkeProduct a) w =
      ((finite_setOf_eq_of_summable hs hw).toFinset.card : ℕ∞) := by
  classical
  have hb := hasSummableBoundOn_blaschke ha ha0 hs
  have hwb : w ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hw
  have hfun : blaschkeProduct a = fun z => ∏' i, (1 + (blaschkeFactor (a i) z - 1)) :=
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
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Set.Finite.mem_toFinset, mem_ofPred_eq] at hi
  simp only [add_sub_cancel, Nat.cast_one]
  rw [← hi]
  exact analyticOrderAt_blaschkeFactor_self (ha i) (ha0 i)

/-- A product of factors of modulus at most one has modulus at most one. -/
theorem norm_tprod_le_one {g : ι → ℂ} (hg : Multipliable g) (h : ∀ i, ‖g i‖ ≤ 1) :
    ‖∏' i, g i‖ ≤ 1 := by
  have ht : Tendsto (fun F : Finset ι => ‖∏ i ∈ F, g i‖) atTop (𝓝 ‖∏' i, g i‖) :=
    Filter.Tendsto.norm hg.hasProd
  refine le_of_tendsto ht (Eventually.of_forall fun F => ?_)
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => h i

/-- **The Blaschke product has modulus at most one** on the disc. -/
theorem norm_blaschkeProduct_le_one (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i => 1 - ‖a i‖) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖blaschkeProduct a z‖ ≤ 1 := by
  have hsum := (hasSummableBoundOn_blaschke ha ha0 hs).summable_norm (mem_ball_zero_iff.mpr hz)
  have hmul : Multipliable fun i => blaschkeFactor (a i) z := by
    have := multipliable_one_add_of_summable (f := fun i => blaschkeFactor (a i) z - 1) hsum
    exact this.congr fun i => add_sub_cancel _ _
  exact norm_tprod_le_one hmul fun i => norm_blaschkeFactor_le_one (ha i) (ha0 i) hz.le

/-! ### The Blaschke condition -/

variable {f : ℂ → ℂ}

/-- For `f` holomorphic on the disc with `f 0 ≠ 0`, the order at every point of the disc is
finite. -/
theorem analyticOrderAt_ne_top_of_ball (hf : DifferentiableOn ℂ f (ball 0 1)) (h0 : f 0 ≠ 0)
    {w : ℂ} (hw : ‖w‖ < 1) : analyticOrderAt f w ≠ ⊤ := by
  refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf.analyticOnNhd isOpen_ball)
    (convex_ball _ _).isPreconnected (mem_ball_self one_pos) (mem_ball_zero_iff.mpr hw) ?_
  rw [Ne, analyticOrderAt_eq_top]
  exact fun h => h0 h.self_of_nhds

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
  have hlog : circleAverage (fun z => Real.log ‖f z‖) 0 R ≤ Real.log (max 1 M) := by
    refine circleAverage_mono_on_of_le_circle
      ((hfR.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm)
      fun z hz => ?_
    rw [hR, mem_sphere_zero_iff_norm] at hz
    have hzb : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (by rw [hz]; exact hR1)
    rcases eq_or_ne ‖f z‖ 0 with h | h
    · rw [h, Real.log_zero]; exact Real.log_nonneg (le_max_left _ _)
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))
        ((hM z hzb).trans (le_max_right _ _))
  rw [hR] at hJ
  linarith

/-- **The multiplicity-weighted Blaschke condition**, at a point where `f` does not vanish.
The zeros of a bounded holomorphic function on the disc with `f 0 ≠ 0`, weighted by their
multiplicity, satisfy `∑ ord(w) (1 - ‖w‖) < ∞`. -/
theorem summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded_of_ne_zero
    (hf : DifferentiableOn ℂ f (ball 0 1)) {M : ℝ} (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M)
    (h0 : f 0 ≠ 0) :
    Summable fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0} =>
      ((analyticOrderAt f w).toNat : ℝ) * (1 - ‖(w : ℂ)‖) := by
  classical
  set K : ℝ := Real.log (max 1 M) - Real.log ‖f 0‖ with hK_def
  have hf0pos : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hMf : ‖f 0‖ ≤ max 1 M := (hM 0 (mem_ball_self one_pos)).trans (le_max_right _ _)
  have hK0 : 0 ≤ K := by
    rw [hK_def, sub_nonneg]
    exact Real.log_le_log hf0pos hMf
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  have htop : ∀ w : ℂ, ‖w‖ < 1 → analyticOrderAt f w ≠ ⊤ :=
    fun w hw => AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hfan
      (convex_ball _ _).isPreconnected (mem_ball_self one_pos) (mem_ball_zero_iff.mpr hw)
      (by rw [Ne, analyticOrderAt_eq_top]; exact fun h => h0 h.self_of_nhds)
  have hterm : ∀ w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0},
      0 ≤ ((analyticOrderAt f w).toNat : ℝ) * (1 - ‖(w : ℂ)‖) := fun w => by
    have := w.2.1
    positivity
  have hw0 : ∀ w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0}, (w : ℂ) ≠ 0 := fun w h => by
    have := w.2.2
    rw [h] at this
    exact h0 this
  refine summable_of_sum_le hterm (c := K) fun S => ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.sum_empty]; linarith
  set r₀ : ℝ := S.sup' hS fun w => ‖(w : ℂ)‖ with hr₀_def
  have hr₀ : r₀ < 1 := (Finset.sup'_lt_iff hS).mpr fun w _ => w.2.1
  set nS : ℝ := ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ) with hnS_def
  have hnS0 : 0 ≤ nS := Finset.sum_nonneg fun w _ => by positivity
  set η : ℝ := ε / (nS + 1) with hη_def
  have hη : 0 < η := by positivity
  set R : ℝ := max r₀ (Real.exp (-η)) with hR_def
  have hR0 : 0 < R := lt_max_of_lt_right (Real.exp_pos _)
  have hR1 : R < 1 := max_lt hr₀ (Real.exp_lt_one_iff.mpr (by linarith))
  have hwR : ∀ w ∈ S, ‖(w : ℂ)‖ ≤ R := fun w hw =>
    (Finset.le_sup' (fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0} => ‖(w : ℂ)‖) hw).trans
      (le_max_left _ _)
  -- termwise: `1 - ‖w‖ ≤ log (R / ‖w‖) + η`
  have hterm' : ∀ w ∈ S, 1 - ‖(w : ℂ)‖ ≤ Real.log (R * ‖(0 : ℂ) - (w : ℂ)‖⁻¹) + η := by
    intro w hw
    have hwpos : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr (hw0 w)
    rw [zero_sub, norm_neg, Real.log_mul hR0.ne' (inv_ne_zero hwpos.ne'), Real.log_inv]
    have h1 : Real.log ‖(w : ℂ)‖ ≤ ‖(w : ℂ)‖ - 1 := Real.log_le_sub_one_of_pos hwpos
    have h2 : -η ≤ Real.log R := by
      rw [← Real.log_exp (-η)]; exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
    linarith
  -- the weighted sum of the logarithms is bounded by the Jensen sum
  have hsum : ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ) *
      Real.log (R * ‖(0 : ℂ) - (w : ℂ)‖⁻¹) ≤ K := by
    have hfR : AnalyticOnNhd ℂ f (closedBall 0 R) := hfan.mono (closedBall_subset_ball hR1)
    set D := divisor f (closedBall 0 R) with hD_def
    have hDfin := D.finiteSupport (isCompact_closedBall 0 R)
    set T := hDfin.toFinset with hT_def
    set g : ℂ → ℝ := fun u => ((D u : ℤ) : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹) with hg_def
    have hDeq : ∀ w ∈ S, ((D (w : ℂ) : ℤ) : ℝ) = ((analyticOrderAt f w).toNat : ℝ) := by
      intro w hw
      have hwR' : (w : ℂ) ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.mpr (hwR w hw)
      rw [hD_def, AnalyticOnNhd.divisor_apply hfR hwR']
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (htop w w.2.1)
      rw [← hn]
      simp
    have hsupp : support g ⊆ ↑T := by
      intro u hu
      rw [mem_support] at hu
      have : D u ≠ 0 := fun h => hu (by simp [hg_def, h])
      exact (Set.Finite.mem_toFinset _).mpr this
    have hfin : ∑ᶠ u, g u = ∑ u ∈ T, g u := finsum_eq_sum_of_support_subset g hsupp
    have hlognn : ∀ u : ℂ, ‖u‖ ≤ R → 0 ≤ Real.log (R * ‖(0 : ℂ) - u‖⁻¹) := by
      intro u hu
      rcases eq_or_ne u 0 with rfl | hu0
      · simp
      · rw [zero_sub, norm_neg]
        apply Real.log_nonneg
        rw [le_mul_inv_iff₀ (norm_pos_iff.mpr hu0), one_mul]
        exact hu
    have hDnn : ∀ u ∈ closedBall (0 : ℂ) R, (0 : ℝ) ≤ ((D u : ℤ) : ℝ) := by
      intro u hu
      rw [hD_def, AnalyticOnNhd.divisor_apply hfR hu]
      generalize analyticOrderAt f u = o
      induction o using ENat.recTopCoe <;> simp
    have hnonneg : ∀ u ∈ T, 0 ≤ g u := by
      intro u hu
      have huD : u ∈ closedBall (0 : ℂ) R := D.supportWithinDomain
        ((Set.Finite.mem_toFinset _).mp hu)
      exact mul_nonneg (hDnn u huD) (hlognn u (mem_closedBall_zero_iff.mp huD))
    have hordne : ∀ w ∈ S, (analyticOrderAt f w).toNat ≠ 0 := by
      intro w hw
      rw [ne_eq, ENat.toNat_eq_zero]
      push Not
      refine ⟨?_, htop w w.2.1⟩
      exact analyticOrderAt_ne_zero.mpr ⟨hfan w (mem_ball_zero_iff.mpr w.2.1), w.2.2⟩
    have hDne : ∀ w ∈ S, D (w : ℂ) ≠ 0 := fun w hw h => by
      have := hDeq w hw
      rw [h] at this
      exact hordne w hw (by exact_mod_cast this.symm)
    have himg : S.image (fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0} => (w : ℂ)) ⊆ T := by
      intro u hu
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      rw [hT_def, Set.Finite.mem_toFinset, mem_support]
      exact hDne w hw
    calc ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ) *
        Real.log (R * ‖(0 : ℂ) - (w : ℂ)‖⁻¹)
        = ∑ w ∈ S, g (w : ℂ) := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [hg_def]
          simp only
          rw [hDeq w hw]
      _ = ∑ u ∈ S.image (fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0} => (w : ℂ)), g u :=
          (Finset.sum_image fun w _ w' _ h => Subtype.val_injective h).symm
      _ ≤ ∑ u ∈ T, g u := Finset.sum_le_sum_of_subset_of_nonneg himg fun u hu _ => hnonneg u hu
      _ = ∑ᶠ u, g u := hfin.symm
      _ ≤ K := jensen_divisor_sum_le hf hM h0 hR0 hR1
  have hcard : nS * η ≤ ε := by
    rw [hη_def, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    linarith
  calc ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ) * (1 - ‖(w : ℂ)‖)
      ≤ ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ) *
          (Real.log (R * ‖(0 : ℂ) - (w : ℂ)‖⁻¹) + η) := by
        refine Finset.sum_le_sum fun w hw => ?_
        exact mul_le_mul_of_nonneg_left (hterm' w hw) (by positivity)
    _ = ∑ w ∈ S, ((analyticOrderAt f w).toNat : ℝ) * Real.log (R * ‖(0 : ℂ) - (w : ℂ)‖⁻¹)
          + nS * η := by
        rw [hnS_def, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        ring
    _ ≤ K + ε := by linarith

/-- **The Blaschke condition (F. Riesz).** The zeros of a bounded holomorphic function on the
disc with `f 0 ≠ 0` satisfy `∑ (1 - ‖w‖) < ∞`. -/
theorem summable_one_sub_norm_of_bounded_of_ne_zero (hf : DifferentiableOn ℂ f (ball 0 1))
    {M : ℝ} (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) (h0 : f 0 ≠ 0) :
    Summable fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0} => 1 - ‖(w : ℂ)‖ := by
  have hweighted := summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded_of_ne_zero
    hf hM h0
  refine Summable.of_nonneg_of_le (fun w => sub_nonneg.mpr w.2.1.le) (fun w => ?_) hweighted
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_ball hf h0 w.2.1)
  have hne : analyticOrderAt f w ≠ 0 := analyticOrderAt_ne_zero.mpr
    ⟨hf.analyticOnNhd isOpen_ball w (mem_ball_zero_iff.mpr w.2.1), w.2.2⟩
  have hn0 : n ≠ 0 := fun h => hne (by rw [← hn, h]; rfl)
  have hone : (1 : ℝ) ≤ (analyticOrderAt f w).toNat := by
    rw [← hn]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact le_mul_of_one_le_left (sub_nonneg.mpr w.2.1.le) hone

/-- **Dividing out the zero at the origin on the disc.** -/
theorem exists_differentiableOn_eq_pow_mul_ball (hf : DifferentiableOn ℂ f (ball 0 1)) {m : ℕ}
    (hm : analyticOrderAt f 0 = m) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) ∧ g 0 ≠ 0 ∧
      ∀ z ∈ ball (0 : ℂ) 1, f z = z ^ m * g z := by
  classical
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  obtain ⟨g₀, hg₀, hg₀0, hfeq⟩ :=
    ((hf.analyticOnNhd isOpen_ball 0 h0b).analyticOrderAt_eq_natCast).mp hm
  set g : ℂ → ℂ := fun z => if z = 0 then g₀ 0 else f z / z ^ m with hg_def
  have hg_ne : ∀ z, z ≠ 0 → g z = f z / z ^ m := fun z hz => by
    simp only [hg_def]
    rw [ite_eq_right_iff]
    exact fun h => absurd h hz
  have hgeq : g =ᶠ[𝓝 0] g₀ := by
    filter_upwards [hfeq] with z hz
    by_cases h0 : z = 0
    · simp [hg_def, h0]
    · rw [hg_ne z h0, hz, sub_zero, smul_eq_mul, mul_div_cancel_left₀ _ (pow_ne_zero _ h0)]
  refine ⟨g, fun z hz => ?_, by simp [hg_def, hg₀0], fun z _ => ?_⟩
  · by_cases h0 : z = 0
    · subst h0
      exact (hg₀.congr hgeq.symm).differentiableAt.differentiableWithinAt
    · have hev : g =ᶠ[𝓝 z] fun w => f w / w ^ m := by
        filter_upwards [isOpen_ne.mem_nhds h0] with w hw
        exact hg_ne w hw
      exact (((hf.differentiableAt (isOpen_ball.mem_nhds hz)).div (differentiableAt_pow m)
        (pow_ne_zero _ h0)).congr_of_eventuallyEq hev).differentiableWithinAt
  · by_cases h0 : z = 0
    · subst h0
      have := hfeq.self_of_nhds
      simpa [hg_def] using this
    · rw [hg_ne z h0, mul_div_cancel₀ _ (pow_ne_zero _ h0)]

/-- **The Blaschke condition (F. Riesz), general form.** The nonzero zeros of a bounded
holomorphic function on the disc that is not identically zero satisfy `∑ (1 - ‖w‖) < ∞`. -/
theorem summable_one_sub_norm_of_bounded (hf : DifferentiableOn ℂ f (ball 0 1)) {M : ℝ}
    (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) (hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) :
    Summable fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0} => 1 - ‖(w : ℂ)‖ := by
  classical
  have htop : analyticOrderAt f 0 ≠ ⊤ := by
    obtain ⟨z₀, hz₀, hfz₀⟩ := hne
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf.analyticOnNhd isOpen_ball)
      (convex_ball _ _).isPreconnected hz₀ (mem_ball_self one_pos) ?_
    rw [Ne, analyticOrderAt_eq_top]
    exact fun h => hfz₀ h.self_of_nhds
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨g, hg, hg0, hfg⟩ := exists_differentiableOn_eq_pow_mul_ball hf hm.symm
  -- `g` is bounded on the disc
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (hg.continuousOn.mono (closedBall_subset_ball (by norm_num)))
  have hMg : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ max M₀ (M * 2 ^ m) := by
    intro z hz
    rcases le_or_gt ‖z‖ (1 / 2) with hz2 | hz2
    · exact (hM₀ z (mem_closedBall_zero_iff.mpr hz2)).trans (le_max_left _ _)
    · have hz0 : z ≠ 0 := by
        rintro rfl
        norm_num at hz2
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hgz : ‖g z‖ = ‖f z‖ / ‖z‖ ^ m := by
        rw [hfg z hz, norm_mul, norm_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hzpos.ne')]
      rw [hgz]
      refine le_trans ?_ (le_max_right _ _)
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1 / 2 : ℝ) ^ m ≤ ‖z‖ ^ m := pow_le_pow_left₀ (by norm_num) hz2.le m
      have h2 : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = 1 := by
        rw [← mul_pow]
        norm_num
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
      calc ‖f z‖ ≤ M := hM z hz
        _ = M * 2 ^ m * (1 / 2 : ℝ) ^ m := by rw [mul_assoc, h2, mul_one]
        _ ≤ M * 2 ^ m * ‖z‖ ^ m := by gcongr
  have hsum := summable_one_sub_norm_of_bounded_of_ne_zero hg hMg hg0
  refine hsum.comp_injective (i := fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0} =>
    (⟨w, w.2.1, ?_⟩ : {w : ℂ // ‖w‖ < 1 ∧ g w = 0})) ?_
  · have := hfg w (mem_ball_zero_iff.mpr w.2.1)
    rw [w.2.2.1] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ w.2.2.2)
  · intro w w' h
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa using this

/-- **Uniqueness theorem.** A bounded holomorphic function on the disc vanishing on an injective
family of nonzero points `a i` with `∑ (1 - ‖a i‖) = ∞` vanishes identically. -/
theorem eqOn_zero_of_not_summable (hf : DifferentiableOn ℂ f (ball 0 1)) {M : ℝ}
    (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hinj : Injective a) (hfa : ∀ i, f (a i) = 0) (hns : ¬ Summable fun i => 1 - ‖a i‖) :
    EqOn f 0 (ball 0 1) := by
  by_contra h
  have hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0 := by
    by_contra h'
    push Not at h'
    exact h fun z hz => h' z hz
  apply hns
  exact (summable_one_sub_norm_of_bounded hf hM hne).comp_injective
    (i := fun i => (⟨a i, ha i, hfa i, ha0 i⟩ : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0}))
    fun i j hij => hinj (by simpa using congrArg Subtype.val hij)

end Complex

end
