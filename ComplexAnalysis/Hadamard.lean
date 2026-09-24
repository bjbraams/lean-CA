/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.FiniteOrder
public import ComplexAnalysis.CanonicalProduct.Bounds
public import ComplexAnalysis.CanonicalProduct.GoodRadii
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Hadamard's factorization theorem

An entire function `f` of order at most `ρ < k + 1`, with a zero of order `m` at the origin and
with nonzero zeros `a i` (listed with multiplicity, `‖a i‖ → ∞`), factors as
`f z = exp (P z) * z ^ m * ∏ E_k (z / a i)` with `P` a polynomial of degree at most `k`, and
`∑ ‖a i‖⁻¹ ^ (k + 1)` converges.

The proof follows Stein–Shakarchi. Jensen's formula gives `∑ ‖a i‖ ^ (-ρ') < ∞` for some
`ρ < ρ' < s < k + 1`; the canonical product `E` of genus `k` has the same zeros as `f`, so the
quotient is `exp G` with `G` entire; on good circles `‖z‖ = r` the lower bound for `E` shows
`Re G ≤ C r ^ s`; the Borel–Carathéodory theorem and the Cauchy estimates then force all
Taylor coefficients of `G` of index above `s` to vanish.

## Main results

* `Complex.exists_differentiable_eq_pow_mul`: division by the zero at the origin.
* `Complex.exists_polynomial_of_frequently_re_le`: polynomiality from real-part growth bounds.
* `Complex.hadamard_factorization`: **Hadamard's factorization theorem**.

## References

* E. M. Stein and R. Shakarchi, *Complex Analysis*, Chapter 5, Theorem 5.1.
* S. Lang, *Complex Analysis*, Chapter XIII, Section 3.
* J. B. Conway, *Functions of One Complex Variable I*, Theorem XI.3.4.
-/

public noncomputable section

open Set Metric Filter Function
open scoped Topology

namespace Complex

/-- **Dividing out the zero at the origin.** If `f` is entire with a zero of order `m` at `0`,
then `f z = z ^ m * g z` with `g` entire and `g 0 ≠ 0`. -/
theorem exists_differentiable_eq_pow_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) {m : ℕ}
    (hm : analyticOrderAt f 0 = m) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 ≠ 0 ∧ ∀ z, f z = z ^ m * g z := by
  classical
  obtain ⟨g₀, hg₀, hg₀0, hfeq⟩ := ((hf.analyticAt 0).analyticOrderAt_eq_natCast).mp hm
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
  refine ⟨g, fun z => ?_, by simp [hg_def, hg₀0], fun z => ?_⟩
  · by_cases h0 : z = 0
    · subst h0
      exact (hg₀.congr hgeq.symm).differentiableAt
    · have hev : g =ᶠ[𝓝 z] fun w => f w / w ^ m := by
        filter_upwards [isOpen_ne.mem_nhds h0] with w hw
        exact hg_ne w hw
      exact ((hf z).div (differentiableAt_pow m) (pow_ne_zero _ h0)).congr_of_eventuallyEq hev
  · by_cases h0 : z = 0
    · subst h0
      have := hfeq.self_of_nhds
      simpa [hg_def] using this
    · rw [hg_ne z h0, mul_div_cancel₀ _ (pow_ne_zero _ h0)]

/-- Dividing by `z ^ m` does not increase the order. -/
theorem HasOrderLE.of_pow_mul {f g : ℂ → ℂ} {m : ℕ} (hg : Differentiable ℂ g)
    (hfg : ∀ z, f z = z ^ m * g z) {ρ : ℝ} (h : HasOrderLE f ρ) : HasOrderLE g ρ := by
  obtain ⟨A, B, hA, hB, hbound⟩ := h
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hg.continuous.continuousOn
  refine ⟨max A M₀, B, le_max_of_le_left hA, hB, fun z => ?_⟩
  rcases le_or_gt ‖z‖ 1 with hz | hz
  · calc ‖g z‖ ≤ M₀ := hM₀ z (mem_closedBall_zero_iff.mpr hz)
      _ ≤ max A M₀ * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ max A M₀ * Real.exp (B * ‖z‖ ^ ρ) :=
          mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) (le_max_of_le_left hA)
  · have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num at hz
    have hgz : ‖g z‖ = ‖f z‖ / ‖z‖ ^ m := by
      rw [hfg z, norm_mul, norm_pow, mul_div_cancel_left₀ _ (pow_ne_zero _
        (norm_ne_zero_iff.mpr hz0))]
    rw [hgz]
    calc ‖f z‖ / ‖z‖ ^ m ≤ ‖f z‖ := div_le_self (norm_nonneg _) (one_le_pow₀ hz.le)
      _ ≤ A * Real.exp (B * ‖z‖ ^ ρ) := hbound z
      _ ≤ max A M₀ * Real.exp (B * ‖z‖ ^ ρ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- An entire function whose real part has subdegree polynomial bounds on arbitrarily
large balls is a polynomial of bounded degree. -/
theorem exists_polynomial_of_frequently_re_le {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {k : ℕ} {s C : ℝ} (hsk : s < k + 1) (hC : 0 < C)
    (hgood : ∃ᶠ r : ℝ in atTop, 1 ≤ r ∧ ∀ w ∈ ball (0 : ℂ) r, (G w).re ≤ C * r ^ s) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ z, P.eval z = G z := by
  -- Borel–Carathéodory and the Cauchy estimates on the circle of radius `r / 2`
  have hderiv : ∀ n : ℕ, ∀ r : ℝ, 1 ≤ r →
      (∀ w ∈ ball (0 : ℂ) r, (G w).re ≤ C * r ^ s) →
      ‖iteratedDeriv n G 0‖ ≤ n.factorial * (2 * (C * r ^ s) + 3 * ‖G 0‖) / (r / 2) ^ n := by
    intro n r hr hReG
    have hr0 : 0 < r := by linarith
    have hM : 0 < C * r ^ s := by positivity
    have hGball : ∀ z ∈ sphere (0 : ℂ) (r / 2), ‖G z‖ ≤ 2 * (C * r ^ s) + 3 * ‖G 0‖ := by
      intro z hz
      rw [mem_sphere_zero_iff_norm] at hz
      have hzball : z ∈ ball (0 : ℂ) r := by
        rw [mem_ball_zero_iff, hz]
        linarith
      have := borelCaratheodory hM hG.differentiableOn hReG hr0
        hzball
      rw [hz] at this
      have e1 : 2 * (C * r ^ s) * (r / 2) / (r - r / 2) = 2 * (C * r ^ s) := by
        field_simp
        ring
      have e2 : ‖G 0‖ * (r + r / 2) / (r - r / 2) = 3 * ‖G 0‖ := by
        field_simp
        ring
      linarith
    exact norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by positivity) hG.diffContOnCl
      hGball
  -- the Taylor coefficients of index above `s` vanish
  have hvanish : ∀ n : ℕ, k + 1 ≤ n → iteratedDeriv n G 0 = 0 := by
    intro n hn
    have hns : s < n := by
      have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hn
      linarith
    have hn0 : (0 : ℝ) < n := by
      have h1 : 1 ≤ n := by omega
      have : (1 : ℝ) ≤ n := by exact_mod_cast h1
      linarith
    have htend : Tendsto (fun r : ℝ => n.factorial * (2 * (C * r ^ s) + 3 * ‖G 0‖) / (r / 2) ^ n)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => r ^ (s - n)) atTop (𝓝 0) := by
        have := tendsto_rpow_neg_atTop (y := n - s) (by linarith)
        refine this.congr fun r => ?_
        rw [neg_sub]
      have h2 : Tendsto (fun r : ℝ => r ^ (-(n : ℝ))) atTop (𝓝 0) := tendsto_rpow_neg_atTop hn0
      have h3 : Tendsto (fun r : ℝ => n.factorial * 2 ^ n *
          (2 * C * r ^ (s - n) + 3 * ‖G 0‖ * r ^ (-(n : ℝ)))) atTop
          (𝓝 (n.factorial * 2 ^ n * (2 * C * 0 + 3 * ‖G 0‖ * 0))) :=
        ((h1.const_mul _).add (h2.const_mul _)).const_mul _
      simp only [mul_zero, add_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with r hr
      rw [Real.rpow_sub hr, Real.rpow_neg hr.le, Real.rpow_natCast, div_pow]
      field_simp
    by_contra hne
    have hpos : 0 < ‖iteratedDeriv n G 0‖ := norm_pos_iff.mpr hne
    obtain ⟨r, ⟨hr, hReG⟩, hsmall⟩ :=
      (hgood.and_eventually (htend.eventually (gt_mem_nhds hpos))).exists
    exact absurd (hderiv n r hr hReG) (not_le.mpr hsmall)
  -- `G` is a polynomial of degree at most `k`
  set P : Polynomial ℂ := ∑ n ∈ Finset.range (k + 1),
    Polynomial.C ((n.factorial : ℂ)⁻¹ * iteratedDeriv n G 0) * Polynomial.X ^ n with hP_def
  have hPdeg : P.natDegree ≤ k :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  have hPeval : ∀ z, P.eval z = G z := by
    intro z
    rw [← taylorSeries_eq_of_entire' (c := 0) (z := z) hG,
      tsum_eq_sum (s := Finset.range (k + 1)) (fun n hn => ?_)]
    · rw [hP_def, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    · rw [hvanish n (by simpa [Finset.mem_range, not_lt] using hn)]
      simp
  exact ⟨P, hPdeg, hPeval⟩

/-- **Hadamard's factorization theorem.** Let `f` be entire of order at most `ρ < k + 1`,
with a zero of order `m` at the origin, and let `a i` list its nonzero zeros with multiplicity
(`‖a i‖ → ∞`). Then `∑ ‖a i‖⁻¹ ^ (k + 1)` converges and
`f z = exp (P z) * z ^ m * ∏' i, E_k (z / a i)` for a polynomial `P` of degree at most `k`.

Related factorization theorems are formalized in Matteo Cipollina's Hadamard development. See
`CREDITS.md`. -/
theorem hadamard_factorization {f : ℂ → ℂ} (hf : Differentiable ℂ f) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hord : HasOrderLE f ρ) {k : ℕ} (hk : ρ < k + 1) {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, a i ≠ 0) (hlim : Tendsto (fun i => ‖a i‖) cofinite atTop) {m : ℕ}
    (hm : analyticOrderAt f 0 = m)
    (hzero : ∀ w, w ≠ 0 → analyticOrderAt f w =
      ((finite_setOf_eq_of_tendsto_cofinite hlim w).toFinset.card : ℕ∞)) :
    (Summable fun i => ‖a i‖⁻¹ ^ (k + 1)) ∧ ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧
      ∀ z, f z = exp (P.eval z) * z ^ m * canonicalProduct k a z := by
  classical
  -- remove the zero at the origin
  obtain ⟨g, hg, hg0, hfg⟩ := exists_differentiable_eq_pow_mul hf hm
  have hordg : HasOrderLE g ρ := HasOrderLE.of_pow_mul hg hfg hord
  have hzerog : ∀ w, analyticOrderAt g w =
      ((finite_setOf_eq_of_tendsto_cofinite hlim w).toFinset.card : ℕ∞) := by
    intro w
    by_cases hw : w = 0
    · subst hw
      rw [(hg.analyticAt 0).analyticOrderAt_eq_zero.mpr hg0]
      have : (finite_setOf_eq_of_tendsto_cofinite hlim 0).toFinset = ∅ := by
        ext i
        simp [Set.Finite.mem_toFinset, ha i]
      rw [this]
      simp
    · rw [← hzero w hw]
      have hfun : f = (fun z => z ^ m) * g := funext hfg
      have hpow : AnalyticAt ℂ (fun z : ℂ => z ^ m) w := by fun_prop
      rw [hfun, analyticOrderAt_mul hpow (hg.analyticAt w),
        (hpow.analyticOrderAt_eq_zero).mpr (pow_ne_zero _ hw), zero_add]
  -- the exponents `ρ < ρ' < s < k + 1`, `k ≤ s`
  set s : ℝ := (max ρ k + (k + 1)) / 2 with hs_def
  have hmax : max ρ (k : ℝ) < k + 1 := max_lt hk (by linarith)
  have hks : (k : ℝ) ≤ s := by
    rw [hs_def]
    linarith [le_max_right ρ (k : ℝ)]
  have hρs : ρ < s := by
    rw [hs_def]
    linarith [le_max_left ρ (k : ℝ)]
  have hsk : s < k + 1 := by
    rw [hs_def]
    linarith
  set ρ' : ℝ := (max ρ 0 + s) / 2 with hρ'_def
  have hs0 : 0 < s := by linarith [le_max_right ρ (k : ℝ), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hρ'0 : 0 < ρ' := by
    rw [hρ'_def]
    linarith [le_max_right ρ 0]
  have hρρ' : ρ < ρ' := by
    rw [hρ'_def]
    linarith [le_max_left ρ 0]
  have hρ's : ρ' < s := by
    rw [hρ'_def]
    have : max ρ 0 < s := max_lt hρs hs0
    linarith
  have hsum' : Summable fun i => ‖a i‖ ^ (-ρ') :=
    summable_norm_rpow_neg_of_hasOrderLE hg hg0 hρ0 hordg hlim hzerog hρρ'
  have hs1 : Summable fun i => ‖a i‖⁻¹ ^ (k + 1) :=
    summable_inv_pow_of_summable_rpow hlim (by linarith) hsum'
  refine ⟨hs1, ?_⟩
  -- the canonical product and the entire nonvanishing quotient `H = exp G`
  set E := canonicalProduct k a with hE_def
  have hE : Differentiable ℂ E := differentiable_canonicalProduct ha hs1
  have hEord : ∀ w, analyticOrderAt E w = analyticOrderAt g w := fun w => by
    rw [hE_def, analyticOrderAt_canonicalProduct ha hs1, hzerog]
  obtain ⟨H, hH, hHne, hgH⟩ :=
    exists_differentiable_ne_zero_mul_of_analyticOrderAt_eq hg hE ⟨0, by simp [hE_def]⟩ hEord
  obtain ⟨G, hG, hHG⟩ := exists_exp_eq_of_differentiable hH hHne
  -- growth of `H` on good circles
  obtain ⟨c, hc⟩ := exists_exp_neg_le_norm_canonicalProduct ha hks hsk hρ'0 hρ's hsum'
  obtain ⟨A, B, hA, hB, hbound⟩ := hordg
  set C : ℝ := |Real.log (max 1 A)| + B + |c| + 1 with hC_def
  have hC : 0 < C := by positivity
  have hgood := frequently_forall_norm_sub_ge ha hs1
  have hReG : ∀ r : ℝ, 1 ≤ r →
      (∀ z : ℂ, ‖z‖ = r → ∀ i, ‖a i‖⁻¹ ^ (k + 1) ≤ ‖z - a i‖) →
      ∀ w ∈ ball (0 : ℂ) r, (G w).re ≤ C * r ^ s := by
    intro r hr hgoodr w hw
    have hr0 : 0 < r := by linarith
    have hrs1 : 1 ≤ r ^ s := Real.one_le_rpow hr hs0.le
    have hrρs : r ^ ρ ≤ r ^ s := Real.rpow_le_rpow_of_exponent_le hr hρs.le
    have hsphere : ∀ z ∈ sphere (0 : ℂ) r, ‖H z‖ ≤ Real.exp (C * r ^ s) := by
      intro z hz
      rw [mem_sphere_zero_iff_norm] at hz
      have hz1 : 1 ≤ ‖z‖ := by rw [hz]; exact hr
      have hEz := hc z hz1 (hgoodr z hz)
      rw [hz] at hEz
      have hEpos : 0 < ‖E z‖ := lt_of_lt_of_le (Real.exp_pos _) hEz
      have hHz : ‖H z‖ = ‖g z‖ / ‖E z‖ := by
        rw [hgH z, norm_mul, mul_div_cancel_right₀ _ hEpos.ne']
      rw [hHz, div_le_iff₀ hEpos]
      have hlogA : Real.log (max 1 A) ≤ |Real.log (max 1 A)| * r ^ s :=
        (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hrs1)
      have hcc : c * r ^ s ≤ |c| * r ^ s :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
      have hBr : B * r ^ ρ ≤ B * r ^ s := mul_le_mul_of_nonneg_left hrρs hB
      calc ‖g z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ) := hbound z
        _ ≤ max 1 A * Real.exp (B * r ^ ρ) := by
            rw [hz]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
        _ = Real.exp (Real.log (max 1 A) + B * r ^ ρ) := by
            rw [Real.exp_add, Real.exp_log (by positivity)]
        _ ≤ Real.exp (C * r ^ s + -(c * r ^ s)) := by
            apply Real.exp_le_exp.mpr
            rw [hC_def]
            nlinarith
        _ = Real.exp (C * r ^ s) * Real.exp (-(c * r ^ s)) := Real.exp_add _ _
        _ ≤ Real.exp (C * r ^ s) * ‖E z‖ := by gcongr
    have hHw : ‖H w‖ ≤ Real.exp (C * r ^ s) := by
      refine norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) r) isBounded_ball
        hH.diffContOnCl ?_ (subset_closure hw)
      rw [frontier_ball _ hr0.ne']
      exact hsphere
    rw [hHG w, norm_exp] at hHw
    exact Real.exp_le_exp.mp hHw
  obtain ⟨P, hPdeg, hPeval⟩ := exists_polynomial_of_frequently_re_le hG hsk hC
    ((hgood.and_eventually (eventually_ge_atTop 1)).mono fun r ⟨hgoodr, hr⟩ =>
      ⟨hr, hReG r hr hgoodr⟩)
  refine ⟨P, hPdeg, fun z => ?_⟩
  rw [hPeval, hfg z, hgH z, hHG z]
  ring



section Enumerate

variable {f : ℂ → ℂ}

/-- For `f` entire and not identically zero, the order of `f` at every point is finite. -/
theorem analyticOrderAt_ne_top_of_exists_ne_zero (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0)
    (w : ℂ) : analyticOrderAt f w ≠ ⊤ := by
  obtain ⟨z₀, hz₀⟩ := hne
  refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (fun z _ => hf.analyticAt z)
    isPreconnected_univ (mem_univ z₀) (mem_univ w) ?_
  rw [Ne, analyticOrderAt_eq_top]
  exact fun h => hz₀ h.self_of_nhds

/-- The zeros of a nonzero entire function in a closed disc are finitely many. -/
theorem finite_zeros_closedBall (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) (R : ℝ) :
    {w | f w = 0 ∧ ‖w‖ ≤ R}.Finite := by
  refine ((MeromorphicOn.divisor f (closedBall 0 R)).finiteSupport
    (isCompact_closedBall 0 R)).subset ?_
  intro w hw
  have hwR : w ∈ closedBall 0 R := mem_closedBall_zero_iff.mpr hw.2
  rw [Function.mem_support,
    MeromorphicOn.AnalyticOnNhd.divisor_apply (fun z _ => hf.analyticAt z) hwR]
  have h1 : analyticOrderAt f w ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hf.analyticAt w, hw.1⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_exists_ne_zero hf hne w)
  rw [← hn] at h1 ⊢
  intro h
  apply h1
  have hn0 : (n : ℤ) = 0 := by simpa using h
  have : n = 0 := by exact_mod_cast hn0
  simp [this]

/-- **Hadamard's factorization theorem, intrinsic form.** A nonzero entire function of order
at most `ρ < k + 1` is `exp (P z) * z ^ m * ∏ E_k (z / a i)` for a polynomial `P` of degree at
most `k`, where `a` lists the nonzero zeros with multiplicity over a countable index type,
`‖a i‖ → ∞` and `∑ ‖a i‖⁻¹ ^ (k + 1) < ∞`.

Related factorization theorems are formalized in Matteo Cipollina's Hadamard development. See
`CREDITS.md`. -/
theorem exists_hadamard_factorization (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hord : HasOrderLE f ρ) {k : ℕ} (hk : ρ < k + 1) :
    ∃ (ι : Type) (_ : Countable ι) (a : ι → ℂ) (m : ℕ) (P : Polynomial ℂ),
      (∀ i, a i ≠ 0) ∧ Tendsto (fun i => ‖a i‖) cofinite atTop ∧ (∀ i, f (a i) = 0) ∧
      (Summable fun i => ‖a i‖⁻¹ ^ (k + 1)) ∧ P.natDegree ≤ k ∧
      ∀ z, f z = exp (P.eval z) * z ^ m * canonicalProduct k a z := by
  classical
  set Z : Set ℂ := {w | w ≠ 0 ∧ f w = 0} with hZ_def
  set n : ℂ → ℕ := fun w => (analyticOrderAt f w).toNat with hn_def
  have htop := analyticOrderAt_ne_top_of_exists_ne_zero hf hne
  have hn : ∀ w, (n w : ℕ∞) = analyticOrderAt f w := fun w => ENat.natCast_toNat (htop w)
  let ι := Σ w : Z, Fin (n w)
  let a : ι → ℂ := fun i => i.1
  have ha : ∀ i, a i ≠ 0 := fun i => i.1.2.1
  have hfa : ∀ i, f (a i) = 0 := fun i => i.1.2.2
  -- finiteness in bounded sets
  have hfin : ∀ R, {i : ι | ‖a i‖ ≤ R}.Finite := by
    intro R
    have hZR : {w : Z | ‖(w : ℂ)‖ ≤ R}.Finite := by
      have := Set.Finite.preimage (f := (Subtype.val : Z → ℂ)) (Subtype.val_injective.injOn)
        (finite_zeros_closedBall hf hne R)
      exact this.subset fun w hw => ⟨w.2.2, hw⟩
    refine (hZR.biUnion fun w _ =>
      (Set.finite_range fun j : Fin (n w) => (⟨w, j⟩ : ι))).subset ?_
    rintro ⟨w, j⟩ hi
    exact mem_iUnion₂.mpr ⟨w, hi, mem_range_self j⟩
  have hlim : Tendsto (fun i => ‖a i‖) cofinite atTop := by
    rw [Filter.tendsto_atTop]
    intro R
    rw [Filter.eventually_cofinite]
    exact (hfin R).subset fun i hi => le_of_lt (not_le.mp hi)
  have hcount : Countable ι := by
    have hZc : Countable Z := by
      have hsub : Z ⊆ ⋃ N : ℕ, {w | f w = 0 ∧ ‖w‖ ≤ N} := fun w hw =>
        mem_iUnion.mpr ⟨⌈‖w‖⌉₊, hw.2, Nat.le_ceil _⟩
      exact ((Set.countable_iUnion fun N : ℕ =>
        (finite_zeros_closedBall hf hne N).countable).mono hsub).to_subtype
    infer_instance
  -- the fiber cardinalities are the orders
  have hzero : ∀ w, w ≠ 0 → analyticOrderAt f w =
      ((finite_setOf_eq_of_tendsto_cofinite hlim w).toFinset.card : ℕ∞) := by
    intro w hw
    rw [← Set.ncard_eq_toFinset_card _ (finite_setOf_eq_of_tendsto_cofinite hlim w)]
    by_cases hfw : f w = 0
    · have hwZ : w ∈ Z := ⟨hw, hfw⟩
      have hrange : {i : ι | a i = w} =
          Set.range fun j : Fin (n w) => (⟨⟨w, hwZ⟩, j⟩ : ι) := by
        ext ⟨⟨w', hw'⟩, j⟩
        simp only [Set.mem_ofPred_eq, mem_range]
        constructor
        · intro h
          have h' : w' = w := h
          subst h'
          exact ⟨j, rfl⟩
        · rintro ⟨j', hj⟩
          cases hj
          rfl
      rw [hrange, Set.ncard_range_of_injective (f := fun j : Fin (n w) => (⟨⟨w, hwZ⟩, j⟩ : ι))
        (fun j j' h => eq_of_heq (Sigma.mk.inj_iff.mp h).2),
        Nat.card_eq_fintype_card, Fintype.card_fin, hn]
    · rw [(hf.analyticAt w).analyticOrderAt_eq_zero.mpr hfw]
      have hempty : {i : ι | a i = w} = ∅ := by
        ext ⟨⟨w', hw'⟩, j⟩
        simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro h
        exact hfw (h ▸ hw'.2)
      rw [hempty, Set.ncard_empty]
      rfl
  obtain ⟨hsum, P, hP, hfact⟩ :=
    hadamard_factorization hf hρ0 hord hk ha hlim (hn 0).symm hzero
  exact ⟨ι, hcount, a, n 0, P, ha, hlim, hfa, hsum, hP, hfact⟩

end Enumerate

end Complex

end
