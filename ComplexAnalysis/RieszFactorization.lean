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

The proof extends the multiplicity-weighted Blaschke condition of `Blaschke.lean` to functions
that may vanish at the origin
(`summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded`), builds an intrinsic countable
index type enumerating the zeros with multiplicity (mirroring the enumeration used for
Hadamard's factorization theorem), forms the matching Blaschke product `B`, and shows that
`f / B` extends holomorphically across the zeros of `B` with the same bound `M`, by comparing
`f` to the finite partial Blaschke products on circles of radius `r → 1`.

## Main results

* `Complex.summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded`: the multiplicity-weighted
  Blaschke condition.
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

/-! ### The multiplicity-weighted Blaschke condition -/


/-! ### Dividing by a matching-order function on the disc -/

/-- **Division by a matching-order function on the disc.** If `f` and `P` are holomorphic on
the disc, `P` is not identically zero, and `P` has the same order as `f` at every point of the
disc, then `f = H * P` for a holomorphic, nonvanishing `H` on the disc. -/
theorem exists_differentiableOn_ne_zero_mul_of_analyticOrderAt_eq_ball {f P : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hP : DifferentiableOn ℂ P (ball 0 1))
    (hPne : ∃ z ∈ ball (0 : ℂ) 1, P z ≠ 0)
    (hPord : ∀ w ∈ ball (0 : ℂ) 1, analyticOrderAt P w = analyticOrderAt f w) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, H z ≠ 0) ∧
      ∀ z ∈ ball (0 : ℂ) 1, f z = H z * P z := by
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  have hPan : AnalyticOnNhd ℂ P (ball 0 1) := hP.analyticOnNhd isOpen_ball
  -- local factorization at every point of the disc
  have hloc : ∀ w ∈ ball (0 : ℂ) 1, ∃ (m : ℕ) (f₁ P₁ : ℂ → ℂ), AnalyticAt ℂ f₁ w ∧ f₁ w ≠ 0 ∧
      AnalyticAt ℂ P₁ w ∧ P₁ w ≠ 0 ∧ (∀ᶠ z in 𝓝 w, f z = (z - w) ^ m * f₁ z) ∧
      ∀ᶠ z in 𝓝 w, P z = (z - w) ^ m * P₁ z := by
    intro w hw
    have hPtop : analyticOrderAt P w ≠ ⊤ := by
      obtain ⟨z₀, hz₀m, hz₀⟩ := hPne
      refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hPan
        (convex_ball (0 : ℂ) 1).isPreconnected hz₀m hw ?_
      rw [Ne, analyticOrderAt_eq_top]
      exact fun h => hz₀ h.self_of_nhds
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hPtop
    obtain ⟨f₁, hf₁, hf₁w, hfeq⟩ := ((hfan w hw).analyticOrderAt_eq_natCast (n := m)).mp
      (by rw [← hPord w hw, ← hm]; rfl)
    obtain ⟨P₁, hP₁, hP₁w, hPeq⟩ := ((hPan w hw).analyticOrderAt_eq_natCast).mp hm.symm
    exact ⟨m, f₁, P₁, hf₁, hf₁w, hP₁, hP₁w, by simpa [smul_eq_mul] using hfeq,
      by simpa [smul_eq_mul] using hPeq⟩
  -- the quotient `f / P` extends to a holomorphic nonvanishing function on the disc
  have hquot : AnalyticOnNhd ℂ (fun z => f z / P z) (ball 0 1 \ P ⁻¹' {0}) := fun z hz =>
    (hfan z hz.1).div (hPan z hz.1) (by simpa using hz.2)
  obtain ⟨H, hH, hHeq⟩ := exists_analyticOnNhd_extension_zeroSet_oneVariable isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected hPan hPne hquot (by
      intro w hw _
      obtain ⟨m, f₁, P₁, hf₁, hf₁w, hP₁, hP₁w, hfeq, hPeq⟩ := hloc w hw
      have hcont : ContinuousAt (fun z => f₁ z / P₁ z) w :=
        hf₁.continuousAt.div hP₁.continuousAt hP₁w
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
        ((hfeq.and hPeq).and (hcont.eventually (Metric.ball_mem_nhds _ one_pos)))
      refine ⟨r, hr, ‖f₁ w / P₁ w‖ + 1, fun z hz => ?_⟩
      obtain ⟨⟨hfz, hPz⟩, hclose⟩ := hball hz.1
      have hPz0 : P z ≠ 0 := by simpa using hz.2.2
      have hzw' : (z - w) ^ m ≠ 0 := fun h => hPz0 (by rw [hPz, h, zero_mul])
      have heq1 : f z / P z = f₁ z / P₁ z := by rw [hfz, hPz, mul_div_mul_left _ _ hzw']
      rw [heq1]
      have hclose' : ‖f₁ z / P₁ z - f₁ w / P₁ w‖ < 1 := by rwa [dist_eq_norm] at hclose
      calc ‖f₁ z / P₁ z‖ = ‖(f₁ z / P₁ z - f₁ w / P₁ w) + f₁ w / P₁ w‖ := by rw [sub_add_cancel]
        _ ≤ ‖f₁ z / P₁ z - f₁ w / P₁ w‖ + ‖f₁ w / P₁ w‖ := norm_add_le _ _
        _ ≤ 1 + ‖f₁ w / P₁ w‖ := by linarith
        _ = ‖f₁ w / P₁ w‖ + 1 := by ring)
  have hHdiff : DifferentiableOn ℂ H (ball 0 1) :=
    fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  -- `H` does not vanish
  have hHne : ∀ w ∈ ball (0 : ℂ) 1, H w ≠ 0 := by
    intro w hw
    obtain ⟨m, f₁, P₁, hf₁, hf₁w, hP₁, hP₁w, hfeq, hPeq⟩ := hloc w hw
    have hev : ∀ᶠ z in 𝓝[≠] w, H z = f₁ z / P₁ z := by
      have hU : ball (0 : ℂ) 1 ∈ 𝓝 w := isOpen_ball.mem_nhds hw
      filter_upwards [nhdsWithin_le_nhds hfeq, nhdsWithin_le_nhds hPeq,
        nhdsWithin_le_nhds (hP₁.continuousAt.eventually_ne hP₁w),
        nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with z hfz hPz hP₁z hzU hzw
      have hzw' : z ≠ w := hzw
      have hPz0 : P z ≠ 0 := by
        rw [hPz]; exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzw')) hP₁z
      rw [hHeq ⟨hzU, by simpa using hPz0⟩]
      change f z / P z = f₁ z / P₁ z
      rw [hfz, hPz, mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr hzw'))]
    have hlim1 : Tendsto H (𝓝[≠] w) (𝓝 (H w)) :=
      ((hH w hw).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto H (𝓝[≠] w) (𝓝 (f₁ w / P₁ w)) := by
      have := ((hf₁.continuousAt.div hP₁.continuousAt hP₁w).tendsto).mono_left
        (nhdsWithin_le_nhds (s := {w}ᶜ))
      exact this.congr' (hev.mono fun z hz => hz.symm)
    have hHw : H w = f₁ w / P₁ w := tendsto_nhds_unique hlim1 hlim2
    rw [hHw]; exact div_ne_zero hf₁w hP₁w
  refine ⟨H, hHdiff, hHne, fun z hz => ?_⟩
  by_cases hPz : P z = 0
  · rw [hPz, mul_zero]
    have hord : analyticOrderAt f z ≠ 0 := by
      rw [← hPord z hz]
      intro h
      exact ((hPan z hz).analyticOrderAt_eq_zero).mp h hPz
    by_contra hfz
    exact hord (((hfan z hz).analyticOrderAt_eq_zero).mpr hfz)
  · rw [hHeq ⟨hz, by simpa using hPz⟩]
    change f z = f z / P z * P z
    rw [div_mul_cancel₀ _ hPz]

/-- **The multiplicity-weighted Blaschke condition**, general form. The nonzero zeros of a
bounded holomorphic function on the disc that is not identically zero, weighted by their
multiplicity, satisfy `∑ ord(w) (1 - ‖w‖) < ∞`. -/
theorem summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded
    (hf : DifferentiableOn ℂ f (ball 0 1)) {M : ℝ} (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M)
    (hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) :
    Summable fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0} =>
      ((analyticOrderAt f w).toNat : ℝ) * (1 - ‖(w : ℂ)‖) := by
  classical
  have htop : analyticOrderAt f 0 ≠ ⊤ := by
    obtain ⟨z₀, hz₀, hfz₀⟩ := hne
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf.analyticOnNhd isOpen_ball)
      (convex_ball _ _).isPreconnected hz₀ (mem_ball_self one_pos) ?_
    rw [Ne, analyticOrderAt_eq_top]
    exact fun h => hfz₀ h.self_of_nhds
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨g, hg, hg0, hfg⟩ := exists_differentiableOn_eq_pow_mul_ball hf hm.symm
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (hg.continuousOn.mono (closedBall_subset_ball (by norm_num)))
  have hMg : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ max M₀ (M * 2 ^ m) := by
    intro z hz
    rcases le_or_gt ‖z‖ (1 / 2) with hz2 | hz2
    · exact (hM₀ z (mem_closedBall_zero_iff.mpr hz2)).trans (le_max_left _ _)
    · have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz2
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hgz : ‖g z‖ = ‖f z‖ / ‖z‖ ^ m := by
        rw [hfg z hz, norm_mul, norm_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hzpos.ne')]
      rw [hgz]
      refine le_trans ?_ (le_max_right _ _)
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1 / 2 : ℝ) ^ m ≤ ‖z‖ ^ m := pow_le_pow_left₀ (by norm_num) hz2.le m
      have h2 : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = 1 := by rw [← mul_pow]; norm_num
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
      calc ‖f z‖ ≤ M := hM z hz
        _ = M * 2 ^ m * (1 / 2 : ℝ) ^ m := by rw [mul_assoc, h2, mul_one]
        _ ≤ M * 2 ^ m * ‖z‖ ^ m := by gcongr
  have hsum := summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded_of_ne_zero hg hMg hg0
  have hg' : AnalyticAt ℂ g 0 := (hg.analyticOnNhd isOpen_ball) 0 (mem_ball_self one_pos)
  have hordeq : ∀ w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0},
      analyticOrderAt f (w : ℂ) = analyticOrderAt g (w : ℂ) := by
    intro w
    have hw1 : (w : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr w.2.1
    have hev : f =ᶠ[𝓝 (w : ℂ)] fun z => z ^ m * g z := by
      filter_upwards [isOpen_ball.mem_nhds hw1] with z hz using hfg z hz
    rw [analyticOrderAt_congr hev]
    have hidan : AnalyticAt ℂ (fun z : ℂ => z ^ m) (w : ℂ) := analyticAt_id.pow m
    have hgan : AnalyticAt ℂ g (w : ℂ) := (hg.analyticOnNhd isOpen_ball) (w : ℂ) hw1
    have heq : (fun z : ℂ => z ^ m * g z) = (fun z : ℂ => z ^ m) * g := rfl
    rw [heq, analyticOrderAt_mul hidan hgan,
      hidan.analyticOrderAt_eq_zero.mpr (pow_ne_zero m w.2.2.2), zero_add]
  have hgz : ∀ w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0}, g (w : ℂ) = 0 := fun w => by
    have := hfg w (mem_ball_zero_iff.mpr w.2.1)
    rw [w.2.2.1] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ w.2.2.2)
  have hcomp := hsum.comp_injective (i := fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0} =>
    (⟨w, w.2.1, hgz w⟩ : {w : ℂ // ‖w‖ < 1 ∧ g w = 0}))
    (fun w w' h => Subtype.ext (by simpa using congrArg Subtype.val h))
  have hfinal : Summable fun w : {w : ℂ // ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0} =>
      ((analyticOrderAt f w).toNat : ℝ) * (1 - ‖(w : ℂ)‖) := by
    refine hcomp.congr fun w => ?_
    simp only [Function.comp_apply, hordeq w]
  exact hfinal

/-! ### The Riesz factorization theorem -/

variable {a : ι → ℂ}

/-- Restricting the Blaschke summable bound to the complement of a finite index set. -/
theorem hasSummableBoundOn_blaschke_compl (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i => 1 - ‖a i‖) (S : Finset ι) :
    HasSummableBoundOn (fun (i : ↑((S : Set ι))ᶜ) (z : ℂ) => blaschkeFactor (a i) z - 1)
      (ball 0 1) :=
  (hasSummableBoundOn_blaschke ha ha0 hs).comp_subtype _

/-- The Blaschke factors past a finite index set are multipliable at any point of the disc. -/
theorem multipliable_blaschke_compl (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i => 1 - ‖a i‖) (S : Finset ι) {z : ℂ} (hz : ‖z‖ < 1) :
    Multipliable (fun i : ↑((S : Set ι))ᶜ => blaschkeFactor (a i) z) := by
  have hsum := (hasSummableBoundOn_blaschke_compl ha ha0 hs S).summable_norm
    (mem_ball_zero_iff.mpr hz)
  have h2 := multipliable_one_add_of_summable (f := fun i : ↑((S : Set ι))ᶜ =>
    blaschkeFactor (a i) z - 1) hsum
  exact h2.congr fun i => add_sub_cancel _ _

/-- The tail of the Blaschke product past a finite index set is holomorphic on the disc. -/
theorem differentiableOn_blaschkeProduct_compl (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (hs : Summable fun i => 1 - ‖a i‖) (S : Finset ι) :
    DifferentiableOn ℂ (fun z => ∏' i : ↑((S : Set ι))ᶜ, blaschkeFactor (a i) z) (ball 0 1) := by
  have : (fun z => ∏' i : ↑((S : Set ι))ᶜ, blaschkeFactor (a i) z) =
      fun z => ∏' i : ↑((S : Set ι))ᶜ, (1 + (blaschkeFactor (a i) z - 1)) := by
    funext z; simp
  rw [this]
  exact differentiableOn_tprod_one_add isOpen_ball
    (fun i => (differentiableOn_blaschkeFactor_ball (ha i)).sub_const 1)
    (hasSummableBoundOn_blaschke_compl ha ha0 hs S)

/-- Splitting the Blaschke product into a finite prefix times the complementary tail. -/
theorem blaschkeProduct_eq_finset_prod_mul_tprod_compl (ha : ∀ i, ‖a i‖ < 1)
    (ha0 : ∀ i, a i ≠ 0) (hs : Summable fun i => 1 - ‖a i‖) (S : Finset ι) {z : ℂ}
    (hz : ‖z‖ < 1) :
    blaschkeProduct a z =
      (∏ i ∈ S, blaschkeFactor (a i) z) * ∏' i : ↑((S : Set ι))ᶜ, blaschkeFactor (a i) z := by
  have hsum := (hasSummableBoundOn_blaschke ha ha0 hs).summable_norm (mem_ball_zero_iff.mpr hz)
  have hmulS : Multipliable ((fun i : ι => blaschkeFactor (a i) z) ∘ ((↑) : ↥(S : Set ι) → ι)) := by
    have h2 := multipliable_one_add_of_summable (f := fun i : (S : Set ι) =>
      blaschkeFactor (a i) z - 1) (hsum.subtype _)
    exact h2.congr fun i => add_sub_cancel _ _
  have hcompl : Multipliable
      ((fun i : ι => blaschkeFactor (a i) z) ∘ ((↑) : ↑((S : Set ι))ᶜ → ι)) :=
    multipliable_blaschke_compl ha ha0 hs S hz
  have hsplit := Multipliable.tprod_mul_tprod_compl (f := fun i : ι => blaschkeFactor (a i) z)
    (s := (S : Set ι)) hmulS hcompl
  rw [blaschkeProduct, ← hsplit]
  congr 1
  exact Finset.tprod_subtype' S (fun i => blaschkeFactor (a i) z)

/-- A finite product of Blaschke factors with nonzero parameters in the open unit disc has norm one
on the unit circle. -/
theorem norm_finset_prod_blaschkeFactor_eq_one (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0)
    (S : Finset ι) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖∏ i ∈ S, blaschkeFactor (a i) z‖ = 1 := by
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [norm_blaschkeFactor _ _ (ha0 i)]
  exact norm_discMobius_eq_one (ha i) hz

/-- A finite Blaschke product is continuous on the closed disc, since its poles lie strictly
outside it. -/
theorem continuousOn_finset_prod_blaschkeFactor (ha : ∀ i, ‖a i‖ < 1) (S : Finset ι) :
    ContinuousOn (fun z => ‖∏ i ∈ S, blaschkeFactor (a i) z‖) (closedBall 0 1) := by
  refine continuous_norm.comp_continuousOn ?_
  refine continuousOn_finsetProd S fun i _ => ?_
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
  set r₀ : ℝ := max 0 (1 - δ) with hr₀_def
  have hr₀1 : r₀ < 1 := max_lt (by norm_num) (by linarith)
  refine ⟨r₀, hr₀1, fun r hr0 hr1 z hz => ?_⟩
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

/-- **Boundedness of the quotient by a finite Blaschke prefix.** If `f` is bounded by `M ≥ 0`
on the disc and `f = z^m * (finite Blaschke prefix) * h` for `h` holomorphic on the disc, then
`h` is also bounded by `M`. -/
theorem norm_le_of_finset_factorization {f h : ℂ → ℂ}
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) {m : ℕ}
    (ha : ∀ i, ‖a i‖ < 1) (ha0 : ∀ i, a i ≠ 0) (S : Finset ι)
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hfh : ∀ z ∈ ball (0 : ℂ) 1, f z = z ^ m * (∏ i ∈ S, blaschkeFactor (a i) z) * h z)
    {z0 : ℂ} (hz0 : z0 ∈ ball (0 : ℂ) 1) : ‖h z0‖ ≤ M := by
  obtain ⟨B, hB1, hB⟩ : ∃ B : ℝ, B < 1 ∧ ∀ i ∈ S, ‖a i‖ ≤ B := by
    rcases S.eq_empty_or_nonempty with hS | hS
    · exact ⟨0, by norm_num, by simp [hS]⟩
    · exact ⟨S.sup' hS fun i => ‖a i‖, (Finset.sup'_lt_iff hS).mpr fun i _ => ha i,
        fun i hi => Finset.le_sup' (fun i => ‖a i‖) hi⟩
  have key : ∀ η : ℝ, 0 < η → η < 1 → ‖h z0‖ ≤ M / (1 - η) ^ (m + 1) := by
    intro η hη0 hη1
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
          (fun z hz => mem_ball_zero_iff.mpr
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
  have : (𝓝[Set.Ioo (0:ℝ) 1] (0:ℝ)).NeBot := left_nhdsWithin_Ioo_neBot one_pos
  have htend : Tendsto (fun η : ℝ => M / (1 - η) ^ (m + 1)) (𝓝[Set.Ioo (0:ℝ) 1] (0:ℝ))
      (𝓝 M) := by
    have hb : Tendsto (fun η : ℝ => M / (1 - η) ^ (m + 1)) (𝓝 (0:ℝ)) (𝓝 (M / (1-0)^(m+1))) := by
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
    (hs : Summable fun i => 1 - ‖a i‖) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun S : Finset ι => ∏ i ∈ S, blaschkeFactor (a i) z) Filter.atTop
      (𝓝 (blaschkeProduct a z)) := by
  have hsum := (hasSummableBoundOn_blaschke ha ha0 hs).summable_norm (mem_ball_zero_iff.mpr hz)
  have hmul : Multipliable (fun i : ι => blaschkeFactor (a i) z) :=
    (multipliable_one_add_of_summable (f := fun i : ι => blaschkeFactor (a i) z - 1) hsum).congr
      fun i => add_sub_cancel _ _
  have := hmul.hasProd
  rwa [blaschkeProduct]

/-- A countable index type admits a sequence of finite subsets exhausting it. -/
theorem exists_finset_seq_tendsto_atTop :
    ∃ S : ℕ → Finset ι, Tendsto S Filter.atTop Filter.atTop := by
  obtain ⟨finj, hfinj⟩ := Countable.exists_injective_nat ι
  refine ⟨fun N => Finset.preimage (Finset.range N) finj (hfinj.injOn), ?_⟩
  rw [Filter.tendsto_atTop]
  intro s
  rw [Filter.eventually_atTop]
  by_cases hse : s.Nonempty
  · refine ⟨(s.image finj).sup id + 1, fun N hN i hi => ?_⟩
    rw [Finset.mem_preimage]
    have : finj i ∈ s.image finj := Finset.mem_image_of_mem finj hi
    have hle : finj i ≤ (s.image finj).sup id := Finset.le_sup (f := id) this
    have hlt : finj i < N := by omega
    exact Finset.mem_range.mpr hlt
  · rw [Finset.not_nonempty_iff_eq_empty] at hse
    exact ⟨0, fun N _ => hse ▸ Finset.empty_subset _⟩


/-- **Boundedness of the cofactor in a Riesz factorization.** If `f` is bounded by `M ≥ 0` on
the disc and `f = z^m * (blaschke product of the `a i`) * g`, then `g` is also bounded by `M`. -/
theorem norm_le_of_blaschkeProduct_bounded {f : ℂ → ℂ}
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M)
    (ha0 : ∀ i, a i ≠ 0) (hab : ∀ i, ‖a i‖ < 1) (hs : Summable (fun i => 1 - ‖a i‖))
    (hBne : ∃ z ∈ ball (0 : ℂ) 1, blaschkeProduct a z ≠ 0) {m : ℕ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1))
    (hfg : ∀ z ∈ ball (0 : ℂ) 1, f z = z ^ m * blaschkeProduct a z * g z) :
    ∀ z0 ∈ ball (0 : ℂ) 1, ‖g z0‖ ≤ M := by
  have hBan : AnalyticOnNhd ℂ (blaschkeProduct a) (ball 0 1) :=
    (differentiableOn_blaschkeProduct hab ha0 hs).analyticOnNhd isOpen_ball
  have caseA : ∀ z0 ∈ ball (0 : ℂ) 1, blaschkeProduct a z0 ≠ 0 → ‖g z0‖ ≤ M := by
    intro z0 hz0 hBz0
    obtain ⟨S, hSseq⟩ := exists_finset_seq_tendsto_atTop (ι := ι)
    have hbound : ∀ T : Finset ι,
        ‖(∏' i : ↑((T : Set ι))ᶜ, blaschkeFactor (a i) z0) * g z0‖ ≤ M := by
      intro T
      refine norm_le_of_finset_factorization (f := f) (m := m) hM0 hM hab ha0 T
        ((differentiableOn_blaschkeProduct_compl hab ha0 hs T).mul hg) (fun z hz => ?_) hz0
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
        (fun N => (∏' i : ↑((S N : Set ι))ᶜ, blaschkeFactor (a i) z0) * g z0)
        atTop (𝓝 (g z0)) := by
      have hd : Tendsto (fun N => blaschkeProduct a z0 / (∏ i ∈ S N, blaschkeFactor (a i) z0)
          * g z0) atTop (𝓝 (blaschkeProduct a z0 / blaschkeProduct a z0 * g z0)) :=
        (Tendsto.div tendsto_const_nhds hconvProd hBz0).mul tendsto_const_nhds
      rw [div_self hBz0, one_mul] at hd
      simpa only [heqh] using hd
    exact le_of_tendsto htendh.norm (Eventually.of_forall fun N => hbound (S N))
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

/-- For `f` holomorphic on the disc, not identically zero, the order of `f` at every point of
the disc is finite. -/
theorem analyticOrderAt_ne_top_of_ball_of_exists_ne_zero (hf : DifferentiableOn ℂ f (ball 0 1))
    (hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    analyticOrderAt f w ≠ ⊤ := by
  obtain ⟨z₀, hz₀, hfz₀⟩ := hne
  refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf.analyticOnNhd isOpen_ball)
    (convex_ball (0 : ℂ) 1).isPreconnected hz₀ hw ?_
  rw [Ne, analyticOrderAt_eq_top]
  exact fun h => hfz₀ h.self_of_nhds

/-- The zeros of a nonzero holomorphic function on the disc, in a smaller closed disc, are
finitely many. -/
theorem finite_zeros_closedBall_lt_one (hf : DifferentiableOn ℂ f (ball 0 1))
    (hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) {R : ℝ} (hR : R < 1) :
    {w | f w = 0 ∧ ‖w‖ ≤ R}.Finite := by
  have hsub : closedBall (0 : ℂ) R ⊆ ball 0 1 := closedBall_subset_ball hR
  have hfR : AnalyticOnNhd ℂ f (closedBall 0 R) := (hf.analyticOnNhd isOpen_ball).mono hsub
  refine ((MeromorphicOn.divisor f (closedBall 0 R)).finiteSupport
    (isCompact_closedBall 0 R)).subset ?_
  intro w hw
  have hwR : w ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.mpr hw.2
  rw [Function.mem_support, MeromorphicOn.AnalyticOnNhd.divisor_apply hfR hwR]
  have h1 : analyticOrderAt f w ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hfR w hwR, hw.1⟩
  obtain ⟨n, hn⟩ :=
    ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_ball_of_exists_ne_zero hf hne (hsub hwR))
  rw [← hn] at h1 ⊢
  intro h
  apply h1
  have hn0 : (n : ℤ) = 0 := by simpa using h
  have : n = 0 := by exact_mod_cast hn0
  simp [this]

/-- **The Riesz factorization theorem.** A bounded holomorphic function on the disc, not
identically zero, factors as `f = z ^ m * B * g` where `B` is the Blaschke product of the
zeros of `f` counted with multiplicity and `g` is holomorphic, nonvanishing, and bounded on
the disc by the same bound as `f`. -/
theorem exists_rieszFactorization {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    {M : ℝ} (hM : ∀ z ∈ ball 0 1, ‖f z‖ ≤ M) (hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0) :
    ∃ (ι : Type) (_ : Countable ι) (a : ι → ℂ) (m : ℕ) (g : ℂ → ℂ),
      (∀ i, a i ≠ 0) ∧ (∀ i, ‖a i‖ < 1) ∧ Summable (fun i => 1 - ‖a i‖) ∧ (∀ i, f (a i) = 0) ∧
      DifferentiableOn ℂ g (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, g z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ M) ∧
      ∀ z ∈ ball (0 : ℂ) 1, f z = z ^ m * blaschkeProduct a z * g z := by
  classical
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  have htopw : ∀ w ∈ ball (0 : ℂ) 1, analyticOrderAt f w ≠ ⊤ :=
    fun w hw => analyticOrderAt_ne_top_of_ball_of_exists_ne_zero hf hne hw
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (htopw 0 (mem_ball_self one_pos))
  set ZS : Set ℂ := {w : ℂ | ‖w‖ < 1 ∧ f w = 0 ∧ w ≠ 0} with hZS_def
  set n : ZS → ℕ := fun w => (analyticOrderAt f w).toNat with hn_def
  have hn : ∀ w : ZS, (n w : ℕ∞) = analyticOrderAt f w :=
    fun w => ENat.natCast_toNat (htopw w (mem_ball_zero_iff.mpr w.2.1))
  let ι := Σ w : ZS, Fin (n w)
  let a : ι → ℂ := fun i => i.1
  have ha0 : ∀ i, a i ≠ 0 := fun i => i.1.2.2.2
  have hab : ∀ i, ‖a i‖ < 1 := fun i => i.1.2.1
  have hfa : ∀ i, f (a i) = 0 := fun i => i.1.2.2.1
  -- countability of the index type
  have hcount : Countable ι := by
    have hZc : Countable ZS := by
      have hsub : ZS ⊆ ⋃ N : ℕ, {w | f w = 0 ∧ ‖w‖ ≤ 1 - 1 / (N + 2)} := by
        intro w hw
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - ‖w‖))
        refine mem_iUnion.mpr ⟨N, hw.2.1, ?_⟩
        have hw1 : 0 < 1 - ‖w‖ := by linarith [hw.1]
        have hN2 : 1 / (1 - ‖w‖) < N + 2 := by linarith
        rw [div_lt_iff₀ hw1] at hN2
        have : 1 / (N + 2 : ℝ) < 1 - ‖w‖ := by
          rw [div_lt_iff₀ (by positivity)]
          linarith [mul_comm (N + 2 : ℝ) (1 - ‖w‖)]
        linarith
      exact ((Set.countable_iUnion fun N : ℕ =>
        (finite_zeros_closedBall_lt_one hf hne (R := 1 - 1 / (N + 2)) (by
          have : (0:ℝ) < 1 / (N+2) := by positivity
          linarith)).countable).mono hsub).to_subtype
    infer_instance
  -- summability of `1 - ‖a i‖` over `ι`
  have hMweighted : Summable fun w : ZS => (n w : ℝ) * (1 - ‖(w : ℂ)‖) := by
    have h := summable_analyticOrderAt_toNat_mul_one_sub_norm_of_bounded hf hM hne
    exact h.congr fun w => by rw [hn_def]
  have hs : Summable fun i : ι => 1 - ‖a i‖ := by
    have hnonneg : ∀ i : ι, 0 ≤ 1 - ‖a i‖ := fun i => by have := hab i; linarith
    rw [summable_sigma_of_nonneg hnonneg]
    refine ⟨fun w => (hasSum_fintype (fun j : Fin (n w) => 1 - ‖a (⟨w, j⟩ : ι)‖)).summable, ?_⟩
    have heq : ∀ w : ZS, ∑' j : Fin (n w), (1 - ‖a (⟨w, j⟩ : ι)‖)
        = (n w : ℝ) * (1 - ‖(w : ℂ)‖) := by
      intro w
      rw [(hasSum_fintype (fun j : Fin (n w) => 1 - ‖a (⟨w, j⟩ : ι)‖)).tsum_eq]
      have hconst : ∀ j : Fin (n w), a (⟨w, j⟩ : ι) = (w : ℂ) := fun j => rfl
      simp_rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [heq]
    exact hMweighted
  have hordmatch : ∀ w ∈ ball (0 : ℂ) 1,
      analyticOrderAt (fun z => z ^ m * blaschkeProduct a z) w = analyticOrderAt f w := by
    intro w hw
    have hidan : AnalyticAt ℂ (fun z : ℂ => z ^ m) w := analyticAt_id.pow m
    have hban : AnalyticAt ℂ (blaschkeProduct a) w := by
      have := differentiableOn_blaschkeProduct hab ha0 hs
      exact (this.analyticOnNhd isOpen_ball) w hw
    have heqfun : (fun z : ℂ => z ^ m * blaschkeProduct a z) =
        (fun z : ℂ => z ^ m) * blaschkeProduct a := rfl
    rw [heqfun, analyticOrderAt_mul hidan hban]
    by_cases hw0 : w = 0
    · subst hw0
      have h1 : analyticOrderAt (fun z : ℂ => z ^ m) (0 : ℂ) = m := by
        have heq : (fun z : ℂ => z ^ m) = (id : ℂ → ℂ) ^ m := rfl
        rw [heq, analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
        simp
      have h2 : analyticOrderAt (blaschkeProduct a) (0 : ℂ) = 0 := by
        rw [analyticOrderAt_blaschkeProduct hab ha0 hs (mem_ball_zero_iff.mp hw)]
        have hempty : {i : ι | a i = 0} = ∅ := by
          ext i; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; exact ha0 i
        simp [hempty]
      rw [h1, h2, add_zero]
      exact hm
    · have h1 : analyticOrderAt (fun z : ℂ => z ^ m) w = 0 :=
        hidan.analyticOrderAt_eq_zero.mpr (pow_ne_zero m hw0)
      rw [h1, zero_add,
        analyticOrderAt_blaschkeProduct hab ha0 hs (mem_ball_zero_iff.mp hw),
        ← Set.ncard_eq_toFinset_card _ (finite_setOf_eq_of_summable hs (mem_ball_zero_iff.mp hw))]
      by_cases hfw : f w = 0
      · have hwZ : (⟨w, mem_ball_zero_iff.mp hw, hfw, hw0⟩ : ZS) = (⟨w, mem_ball_zero_iff.mp hw,
            hfw, hw0⟩ : ZS) := rfl
        set wZ : ZS := ⟨w, mem_ball_zero_iff.mp hw, hfw, hw0⟩ with hwZ_def
        have hrange : {i : ι | a i = w} = Set.range fun j : Fin (n wZ) => (⟨wZ, j⟩ : ι) := by
          ext ⟨w', j⟩
          simp only [mem_ofPred_eq, mem_range]
          constructor
          · intro h
            have h' : w' = wZ := Subtype.ext h
            subst h'
            exact ⟨j, rfl⟩
          · rintro ⟨j', hj⟩
            cases hj
            rfl
        rw [hrange, Set.ncard_range_of_injective (f := fun j : Fin (n wZ) => (⟨wZ, j⟩ : ι))
          (fun j j' h => eq_of_heq (Sigma.mk.inj_iff.mp h).2),
          Nat.card_eq_fintype_card, Fintype.card_fin, hn]
      · rw [(hfan w hw).analyticOrderAt_eq_zero.mpr hfw]
        have hempty : {i : ι | a i = w} = ∅ := by
          ext ⟨w', j⟩
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          intro h
          exact hfw (h ▸ w'.2.2.1)
        rw [hempty, Set.ncard_empty]
        rfl
  -- divide `f` by the Blaschke product
  set B : ℂ → ℂ := fun z => z ^ m * blaschkeProduct a z with hB_def
  have hBd : DifferentiableOn ℂ B (ball 0 1) :=
    (differentiableOn_pow m).mul (differentiableOn_blaschkeProduct hab ha0 hs)
  have hBne : ∃ z ∈ ball (0 : ℂ) 1, B z ≠ 0 := by
    obtain ⟨z₀, hz₀, hfz₀⟩ := hne
    have hBan : AnalyticAt ℂ B z₀ := hBd.analyticOnNhd isOpen_ball z₀ hz₀
    have hford0 : analyticOrderAt f z₀ = 0 := (hfan z₀ hz₀).analyticOrderAt_eq_zero.mpr hfz₀
    have hBord0 : analyticOrderAt B z₀ = 0 := by rw [hordmatch z₀ hz₀]; exact hford0
    exact ⟨z₀, hz₀, hBan.analyticOrderAt_eq_zero.mp hBord0⟩
  obtain ⟨g, hg, hgne, hfg⟩ := exists_differentiableOn_ne_zero_mul_of_analyticOrderAt_eq_ball
    hf hBd hBne hordmatch
  have hfg' : ∀ z ∈ ball (0 : ℂ) 1, f z = z ^ m * blaschkeProduct a z * g z := by
    intro z hz
    rw [hfg z hz, hB_def]
    ring
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (mem_ball_self one_pos))
  have hBne' : ∃ z ∈ ball (0 : ℂ) 1, blaschkeProduct a z ≠ 0 := by
    obtain ⟨z₀, hz₀, hBz₀⟩ := hBne
    exact ⟨z₀, hz₀, right_ne_zero_of_mul (hB_def ▸ hBz₀)⟩
  have hgbound : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ M :=
    norm_le_of_blaschkeProduct_bounded hM0 hM ha0 hab hs hBne' hg hfg'
  exact ⟨ι, hcount, a, m, g, ha0, hab, hs, hfa, hg, hgne, hgbound, hfg'⟩

end Complex

end
