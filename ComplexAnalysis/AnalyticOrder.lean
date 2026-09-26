/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.RemovableSingularity
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Data.Set.Card

/-!
# Orders of zeros and division by zero-matching functions

For a function `f` analytic on a preconnected open set `U ⊆ ℂ` and not identically zero there,
this file collects the facts about its zeros used by the product theorems (Weierstrass,
Hadamard, Blaschke, Riesz): every order of vanishing is finite, the zero set is finite in each
compact subset of `U` and countable, a zero of order `m` at `c` can be divided out as
`(z - c) ^ m`, and `f` is divisible by any analytic function with the same orders of
vanishing, the quotient being analytic and nowhere zero.

It also records the count of the fibres of the enumeration `Σ z : Z, Fin (n z)`, which lists
each point of a set `Z` with multiplicity `n z`.

## Main results

* `AnalyticOnNhd.analyticOrderAt_ne_top_of_exists_ne_zero`: orders of vanishing are finite.
* `AnalyticOnNhd.finite_zeros_of_isCompact`, `AnalyticOnNhd.countable_zeros`: the zero set is
  finite in compact subsets and countable.
* `AnalyticOnNhd.exists_eq_sub_pow_mul`: dividing out a zero of order `m`.
* `AnalyticOnNhd.exists_ne_zero_mul_of_analyticOrderAt_eq`: division by a function with the same
  orders of vanishing.
* `Set.ncard_sigma_fin_fiber`: the fibres of a multiplicity enumeration.
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace AnalyticOnNhd

section Zeros

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set ℂ} {f : ℂ → E}

/-- An analytic function on a preconnected set that is not identically zero there has finite
order of vanishing at every point of the set. -/
theorem analyticOrderAt_ne_top_of_exists_ne_zero (hf : AnalyticOnNhd ℂ f U)
    (hU : IsPreconnected U) (hne : ∃ z ∈ U, f z ≠ 0) {w : ℂ} (hw : w ∈ U) :
    analyticOrderAt f w ≠ ⊤ := by
  obtain ⟨z₀, hz₀, hfz₀⟩ := hne
  refine hf.analyticOrderAt_ne_top_of_isPreconnected hU hz₀ hw ?_
  rw [(hf z₀ hz₀).analyticOrderAt_eq_zero.mpr hfz₀]
  exact ENat.zero_ne_top

/-- An analytic function on a preconnected set that is not identically zero there is nonzero
off a discrete subset. -/
theorem setOf_ne_zero_mem_codiscreteWithin (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    (hne : ∃ z ∈ U, f z ≠ 0) : {z | f z ≠ 0} ∈ codiscreteWithin U :=
  (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hU).resolve_left fun h ↦ by
    obtain ⟨z, hz, hfz⟩ := hne
    exact hfz (h hz)

/-- An analytic function on a preconnected set that is not identically zero there has only
finitely many zeros in each compact subset. -/
theorem finite_zeros_of_isCompact (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    (hne : ∃ z ∈ U, f z ≠ 0) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    {z ∈ K | f z = 0}.Finite :=
  (hK.finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono hKU (hf.setOf_ne_zero_mem_codiscreteWithin hU hne))).subset
    fun _ hz ↦ ⟨hz.1, fun h ↦ h hz.2⟩

/-- An analytic function on a preconnected set that is not identically zero there has only
countably many zeros in the set. -/
theorem countable_zeros (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    (hne : ∃ z ∈ U, f z ≠ 0) : {z ∈ U | f z = 0}.Countable := by
  have h := isDiscrete_of_codiscreteWithin (s := {z | f z ≠ 0}ᶜ)
    (by simpa using hf.setOf_ne_zero_mem_codiscreteWithin hU hne)
  exact ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete h).mono
    fun z (hz : z ∈ U ∧ f z = 0) ↦ (⟨fun h ↦ h hz.2, hz.1⟩ : z ∈ {z | f z ≠ 0}ᶜ ∩ U)

end Zeros

variable {U : Set ℂ} {f : ℂ → ℂ}

/-- **Dividing out a zero.** If `f` is analytic on `U` and has a zero of order `m`
at `c ∈ U`, then `f z = (z - c) ^ m * g z` on `U` with `g` analytic on `U` and `g c ≠ 0`. -/
theorem exists_eq_sub_pow_mul (hf : AnalyticOnNhd ℂ f U) {c : ℂ} (hc : c ∈ U)
    {m : ℕ} (hm : analyticOrderAt f c = m) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ g c ≠ 0 ∧ ∀ z ∈ U, f z = (z - c) ^ m * g z := by
  classical
  obtain ⟨g₀, hg₀, hg₀c, hfeq⟩ := ((hf c hc).analyticOrderAt_eq_natCast).mp hm
  set g : ℂ → ℂ := fun z ↦ if z = c then g₀ c else f z / (z - c) ^ m
  have hpow : ∀ {z}, z ≠ c → (z - c) ^ m ≠ 0 := fun h ↦ pow_ne_zero _ (sub_ne_zero.mpr h)
  have hg_ne : ∀ z, z ≠ c → g z = f z / (z - c) ^ m := fun z hz ↦ by simp [g, hz]
  have hgeq : g =ᶠ[𝓝 c] g₀ := by
    filter_upwards [hfeq] with z hz
    by_cases h0 : z = c
    · simp [g, h0]
    · rw [hg_ne z h0, hz, smul_eq_mul, mul_div_cancel_left₀ _ (hpow h0)]
  refine ⟨g, fun z hz ↦ ?_, by simpa [g] using hg₀c, fun z _ ↦ ?_⟩
  · by_cases h0 : z = c
    · subst h0
      exact hg₀.congr hgeq.symm
    · refine ((hf z hz).div ((analyticAt_id.sub analyticAt_const).pow m) (hpow h0)).congr ?_
      filter_upwards [isOpen_ne.mem_nhds h0] with w hw using (hg_ne w hw).symm
  · by_cases h0 : z = c
    · subst h0
      simpa [g] using hfeq.self_of_nhds
    · rw [hg_ne z h0, mul_div_cancel₀ _ (hpow h0)]

/-- **Division by a function with the same orders of vanishing.** If `f` and `P` are analytic on
the preconnected open set `U`, `P` is not identically zero on `U`, and `P` and `f` have the same
order of vanishing at every point of `U`, then `f = H * P` on `U` with `H` analytic and nowhere
zero on `U`. -/
theorem exists_ne_zero_mul_of_analyticOrderAt_eq {P : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hP : AnalyticOnNhd ℂ P U) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hPne : ∃ z ∈ U, P z ≠ 0) (hord : ∀ w ∈ U, analyticOrderAt P w = analyticOrderAt f w) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H U ∧ (∀ z ∈ U, H z ≠ 0) ∧ ∀ z ∈ U, f z = H z * P z := by
  -- local factorization at every point
  have hloc : ∀ w ∈ U, ∃ (m : ℕ) (f₁ P₁ : ℂ → ℂ), AnalyticAt ℂ f₁ w ∧ f₁ w ≠ 0 ∧
      AnalyticAt ℂ P₁ w ∧ P₁ w ≠ 0 ∧ (∀ᶠ z in 𝓝 w, f z = (z - w) ^ m * f₁ z) ∧
      ∀ᶠ z in 𝓝 w, P z = (z - w) ^ m * P₁ z := by
    intro w hw
    obtain ⟨m, hm⟩ :=
      ENat.ne_top_iff_exists.mp (hP.analyticOrderAt_ne_top_of_exists_ne_zero hUc hPne hw)
    obtain ⟨f₁, hf₁, hf₁w, hfeq⟩ := ((hf w hw).analyticOrderAt_eq_natCast (n := m)).mp
      (by rw [← hord w hw, ← hm])
    obtain ⟨P₁, hP₁, hP₁w, hPeq⟩ := ((hP w hw).analyticOrderAt_eq_natCast).mp hm.symm
    exact ⟨m, f₁, P₁, hf₁, hf₁w, hP₁, hP₁w, by simpa [smul_eq_mul] using hfeq,
      by simpa [smul_eq_mul] using hPeq⟩
  -- near `w`, off the zeros of `P`, the quotient `f / P` is `f₁ / P₁`
  have hquot_eq : ∀ w ∈ U, ∀ {m : ℕ} {f₁ P₁ : ℂ → ℂ} {z : ℂ},
      f z = (z - w) ^ m * f₁ z → P z = (z - w) ^ m * P₁ z → P z ≠ 0 →
      f z / P z = f₁ z / P₁ z := by
    intro w _ m f₁ P₁ z hfz hPz hPz0
    have hzw : (z - w) ^ m ≠ 0 := fun h ↦ hPz0 (by rw [hPz, h, zero_mul])
    rw [hfz, hPz, mul_div_mul_left _ _ hzw]
  -- the quotient extends analytically across the zeros of `P`
  obtain ⟨H, hH, hHeq⟩ := Complex.exists_analyticOnNhd_extension_zeroSet_oneVariable hU hUc hP hPne
    (f := fun z ↦ f z / P z) (fun z hz ↦ (hf z hz.1).div (hP z hz.1) (by simpa using hz.2))
    (by
      intro w hw _
      obtain ⟨m, f₁, P₁, hf₁, -, hP₁, hP₁w, hfeq, hPeq⟩ := hloc w hw
      have hcont : ContinuousAt (fun z ↦ f₁ z / P₁ z) w :=
        hf₁.continuousAt.div hP₁.continuousAt hP₁w
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
        ((hfeq.and hPeq).and (hcont.eventually (Metric.ball_mem_nhds _ one_pos)))
      refine ⟨r, hr, ‖f₁ w / P₁ w‖ + 1, fun z hz ↦ ?_⟩
      obtain ⟨⟨hfz, hPz⟩, hclose⟩ := hball hz.1
      rw [hquot_eq w hw hfz hPz (by simpa using hz.2.2)]
      have := norm_le_norm_add_norm_sub' (f₁ z / P₁ z) (f₁ w / P₁ w)
      rw [← dist_eq_norm] at this
      linarith [mem_ball.mp hclose])
  -- `H` does not vanish
  have hHne : ∀ w ∈ U, H w ≠ 0 := by
    intro w hw
    obtain ⟨m, f₁, P₁, hf₁, hf₁w, hP₁, hP₁w, hfeq, hPeq⟩ := hloc w hw
    have hev : ∀ᶠ z in 𝓝[≠] w, H z = f₁ z / P₁ z := by
      filter_upwards [nhdsWithin_le_nhds hfeq, nhdsWithin_le_nhds hPeq,
        nhdsWithin_le_nhds (hP₁.continuousAt.eventually_ne hP₁w),
        nhdsWithin_le_nhds (hU.mem_nhds hw), self_mem_nhdsWithin] with z hfz hPz hP₁z hzU hzw
      have hPz0 : P z ≠ 0 := by
        rw [hPz]
        exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzw)) hP₁z
      rw [hHeq ⟨hzU, by simpa using hPz0⟩]
      exact hquot_eq w hw hfz hPz hPz0
    have hHw : H w = f₁ w / P₁ w := tendsto_nhds_unique
      ((hH w hw).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (((hf₁.continuousAt.div hP₁.continuousAt hP₁w).tendsto.mono_left
        nhdsWithin_le_nhds).congr' (hev.mono fun z hz ↦ hz.symm))
    rw [hHw]
    exact div_ne_zero hf₁w hP₁w
  refine ⟨H, hH, hHne, fun z hz ↦ ?_⟩
  by_cases hPz : P z = 0
  · -- both sides vanish: `f z = 0` since the order of `f` at `z` is positive
    rw [hPz, mul_zero]
    by_contra hfz
    have h1 := (hf z hz).analyticOrderAt_eq_zero.mpr hfz
    rw [← hord z hz] at h1
    exact (hP z hz).analyticOrderAt_eq_zero.mp h1 hPz
  · rw [hHeq ⟨hz, by simpa using hPz⟩]
    exact (div_mul_cancel₀ _ hPz).symm

end AnalyticOnNhd

open Classical in
/-- **Fibres of a multiplicity enumeration.** In the index type `Σ z : Z, Fin (n z)`, which
lists each point `z` of `Z` with multiplicity `n z`, the fibre over `w` has `n w` elements if
`w ∈ Z` and is empty otherwise. -/
theorem Set.ncard_sigma_fin_fiber {α : Type*} (Z : Set α) (n : α → ℕ) (w : α) :
    {i : Σ z : Z, Fin (n z) | (i.1 : α) = w}.ncard = if w ∈ Z then n w else 0 := by
  split_ifs with hw
  · have hrange : {i : Σ z : Z, Fin (n z) | (i.1 : α) = w} =
        Set.range fun j : Fin (n w) ↦ (⟨⟨w, hw⟩, j⟩ : Σ z : Z, Fin (n z)) := by
      ext ⟨⟨w', hw'⟩, j⟩
      simp only [Set.mem_ofPred_eq, Set.mem_range]
      constructor
      · rintro rfl
        exact ⟨j, rfl⟩
      · rintro ⟨j', hj⟩
        cases hj
        rfl
    rw [hrange, Set.ncard_range_of_injective
      (f := fun j : Fin (n w) ↦ (⟨⟨w, hw⟩, j⟩ : Σ z : Z, Fin (n z)))
      fun j j' h ↦ eq_of_heq (Sigma.mk.inj_iff.mp h).2,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  · convert Set.ncard_empty (Σ z : Z, Fin (n z))
    ext ⟨⟨w', hw'⟩, j⟩
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact hw hw'
