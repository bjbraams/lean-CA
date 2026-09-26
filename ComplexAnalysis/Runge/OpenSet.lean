/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Runge.Theorem

/-!
# Runge's theorem on open sets

A function holomorphic on an open set `U` is, uniformly on every compact subset of `U`, a
limit of rational functions with poles in a prescribed set `A ⊆ Uᶜ` meeting every bounded
component of `Uᶜ`, together with polynomials; if every component of `Uᶜ` is unbounded,
polynomials suffice. The approximants can be chosen as a sequence converging locally uniformly
on `U`.

The proof replaces a compact subset `K` of `U` by the larger compact set
`rungeHull U R δ = closedBall 0 R ∩ {z | ∀ u ∉ U, δ ≤ dist z u}`, every bounded component of
whose complement meets `Uᶜ`; the compact form of Runge's theorem then applies.

## Main definitions

* `Complex.rungeHull U R δ`: the compact subset of `U` used to fill the holes of `K`.

## Main results

* `Complex.exists_compl_mem_connectedComponentIn_rungeHull`: bounded complement components of
  the hull meet `Uᶜ`.
* `Complex.runge_isOpen`: Runge's theorem on open sets, uniformly on compact subsets.
* `Complex.exists_seq_tendstoLocallyUniformlyOn_runge`: a locally uniformly convergent sequence
  of approximants.
* `Complex.exists_polynomial_tendstoLocallyUniformlyOn`: polynomial approximation when every
  component of `Uᶜ` is unbounded.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem VIII.1.8 and Corollary VIII.1.9.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology

namespace Complex

/-- The hole-free compact subset of `U` determined by a radius `R` and a distance `δ` to the
complement. -/
def rungeHull (U : Set ℂ) (R δ : ℝ) : Set ℂ :=
  closedBall 0 R ∩ {z | ∀ u ∈ Uᶜ, δ ≤ dist z u}

/-- The closed set used for the Runge exhaustion is closed for every choice of radius and boundary
distance. -/
theorem isClosed_rungeHull (U : Set ℂ) (R δ : ℝ) : IsClosed (rungeHull U R δ) := by
  refine isClosed_closedBall.inter ?_
  have : {z : ℂ | ∀ u ∈ Uᶜ, δ ≤ dist z u} = ⋂ u ∈ Uᶜ, {z | δ ≤ dist z u} := by
    ext z
    simp
  rw [this]
  exact isClosed_biInter fun u _ ↦
    isClosed_le continuous_const (continuous_id.dist continuous_const)

/-- Each set used for the Runge exhaustion is compact. -/
theorem isCompact_rungeHull (U : Set ℂ) (R δ : ℝ) : IsCompact (rungeHull U R δ) :=
  (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset (isClosed_rungeHull U R δ) inter_subset_left

/-- A positive boundary-distance cutoff ensures that the Runge exhaustion set lies in the original
domain. -/
theorem rungeHull_subset {U : Set ℂ} {R δ : ℝ} (hδ : 0 < δ) : rungeHull U R δ ⊆ U := by
  intro z hz
  by_contra hzU
  have := hz.2 z hzU
  rw [dist_self] at this
  linarith

/-- Increasing the radius and decreasing the boundary-distance cutoff enlarges the Runge exhaustion
set. -/
theorem rungeHull_mono {U : Set ℂ} {R R' δ δ' : ℝ} (hR : R ≤ R') (hδ : δ' ≤ δ) :
    rungeHull U R δ ⊆ rungeHull U R' δ' :=
  fun _ hz ↦ ⟨closedBall_subset_closedBall hR hz.1, fun u hu ↦ hδ.trans (hz.2 u hu)⟩

/-- Every compact subset of an open set lies in a hole-free hull. -/
theorem exists_subset_rungeHull {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ R δ : ℝ, 0 < δ ∧ K ⊆ rungeHull U R δ := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨R, 1, one_pos, by simp [hKe]⟩
  rcases (Uᶜ).eq_empty_or_nonempty with hUe | hUne
  · exact ⟨R, 1, one_pos, fun z hz ↦ ⟨hR hz, fun u hu ↦ by simp [hUe] at hu⟩⟩
  have hcont : ContinuousOn (fun z ↦ infDist z Uᶜ) K := (continuous_infDist_pt _).continuousOn
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne hcont
  have hpos : 0 < infDist z₀ Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hUne).mp (by simpa using hKU hz₀)
  refine ⟨R, infDist z₀ Uᶜ, hpos, fun z hz ↦ ⟨hR hz, fun u hu ↦ ?_⟩⟩
  exact (hmin hz).trans (infDist_le_dist_of_mem hu)

/-- A bounded component of the complement of a hull meets the complement of `U`. -/
theorem exists_compl_mem_connectedComponentIn_rungeHull {U : Set ℂ} {R δ : ℝ}
    {w : ℂ} (hw : w ∉ rungeHull U R δ)
    (hb : Bornology.IsBounded (connectedComponentIn (rungeHull U R δ)ᶜ w)) :
    ∃ u ∈ Uᶜ, u ∈ connectedComponentIn (rungeHull U R δ)ᶜ w := by
  by_cases hwR : w ∈ closedBall (0 : ℂ) R
  · have : ∃ u ∈ Uᶜ, dist w u < δ := by
      by_contra h
      push Not at h
      exact hw ⟨hwR, h⟩
    obtain ⟨u, hu, hwu⟩ := this
    set L : Set ℂ := (fun t : ℝ ↦ w + (t : ℂ) * (u - w)) '' Icc 0 1 with hL_def
    have hLc : IsPreconnected L := isPreconnected_Icc.image _ (by fun_prop)
    have hwL : w ∈ L := ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
    have huL : u ∈ L := ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩
    have hLsub : L ⊆ (rungeHull U R δ)ᶜ := by
      rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩ hmem
      have hdist : dist (w + (t : ℂ) * (u - w)) u = (1 - t) * dist w u := by
        rw [dist_eq_norm, dist_eq_norm]
        have : w + (t : ℂ) * (u - w) - u = ((1 - t : ℝ) : ℂ) * (w - u) := by push_cast; ring
        rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have h1 := hmem.2 u hu
      rw [hdist] at h1
      have : (1 - t) * dist w u ≤ dist w u :=
        mul_le_of_le_one_left dist_nonneg (by linarith)
      linarith
    exact ⟨u, hu, hLc.subset_connectedComponentIn hwL hLsub huL⟩
  · exfalso
    have hwR' : R < ‖w‖ := by simpa using hwR
    set L : Set ℂ := (fun t : ℝ ↦ (t : ℂ) * w) '' Ici 1 with hL_def
    have hLc : IsPreconnected L := isPreconnected_Ici.image _ (by fun_prop)
    have hwL : w ∈ L := ⟨1, le_rfl, by simp⟩
    have hLsub : L ⊆ (rungeHull U R δ)ᶜ := by
      rintro _ ⟨t, ht, rfl⟩ hmem
      have ht' : 1 ≤ t := ht
      have h1 : ‖(t : ℂ) * w‖ ≤ R := by simpa using hmem.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h1
      have : ‖w‖ ≤ t * ‖w‖ := le_mul_of_one_le_left (norm_nonneg _) ht'
      linarith
    have hLW := hLc.subset_connectedComponentIn hwL hLsub
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hb
    have hw0 : 0 < ‖w‖ := by
      rcases eq_or_ne w 0 with hw0 | hw0
      · exfalso
        have hR : R < 0 := by simpa [hw0] using hwR'
        have hH : rungeHull U R δ = ∅ := by
          apply eq_empty_of_subset_empty
          intro z hz
          have := hz.1
          rw [closedBall_eq_empty.mpr hR] at this
          exact this
        rw [hH, compl_empty] at hb
        exact NormedSpace.unbounded_univ ℝ ℂ
          (hb.subset (isPreconnected_univ.subset_connectedComponentIn (mem_univ w) subset_rfl))
      · exact norm_pos_iff.mpr hw0
    set t : ℝ := max 1 ((r + 1) / ‖w‖)
    have htL : (t : ℂ) * w ∈ L := ⟨t, le_max_left _ _, rfl⟩
    have := hr (hLW htL)
    rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (lt_of_lt_of_le one_pos (le_max_left _ _))] at this
    have h2 : (r + 1) / ‖w‖ * ‖w‖ ≤ t * ‖w‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    rw [div_mul_cancel₀ _ hw0.ne'] at h2
    linarith

/-- **Runge's theorem on open sets.** Let `U` be open and `A ⊆ Uᶜ` meet every bounded
component of `Uᶜ`. Every function holomorphic on `U` is uniformly approximable on every compact
subset of `U` by the algebra generated by the identity and the simple poles at points of `A`. -/
theorem runge_isOpen {U : Set ℂ} (hU : IsOpen U) {A : Set ℂ} (hAU : A ⊆ Uᶜ)
    (hA : ∀ w ∉ U, Bornology.IsBounded (connectedComponentIn Uᶜ w) →
      ∃ a ∈ A, a ∈ connectedComponentIn Uᶜ w)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    UniformApproxOn K (Algebra.adjoin ℂ (rungeGenerators A)) f := by
  obtain ⟨R, δ, hδ, hKH⟩ := exists_subset_rungeHull hU hK hKU
  set H := rungeHull U R δ
  have hHU : H ⊆ U := rungeHull_subset hδ
  have hAH : Disjoint A H := disjoint_left.mpr fun a ha haH ↦ hAU ha (hHU haH)
  have hA' : ∀ w ∉ H, Bornology.IsBounded (connectedComponentIn Hᶜ w) →
      ∃ a ∈ A, a ∈ connectedComponentIn Hᶜ w := by
    intro w hw hb
    obtain ⟨u, hu, huW⟩ := exists_compl_mem_connectedComponentIn_rungeHull hw hb
    have hCW : connectedComponentIn Uᶜ u ⊆ connectedComponentIn Hᶜ w := by
      rw [connectedComponentIn_eq huW]
      exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hu)
        ((connectedComponentIn_subset _ _).trans (compl_subset_compl.mpr hHU))
    obtain ⟨a, haA, haC⟩ := hA u hu (hb.subset hCW)
    exact ⟨a, haA, hCW haC⟩
  intro ε hε
  obtain ⟨r, hr, hrε⟩ := runge (isCompact_rungeHull U R δ) hAH hA' hU hHU hf ε hε
  exact ⟨r, hr, fun z hz ↦ hrε z (hKH hz)⟩

/-- The exhaustion of `U` by hole-free hulls. -/
theorem exists_forall_subset_rungeHull_nat {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) : ∃ m : ℕ, ∀ n, m ≤ n → K ⊆ rungeHull U n (1 / (n + 1)) := by
  obtain ⟨R, δ, hδ, hKH⟩ := exists_subset_rungeHull hU hK hKU
  obtain ⟨m, hm⟩ := exists_nat_gt (max R (1 / δ))
  refine ⟨m, fun n hn ↦ hKH.trans (rungeHull_mono ?_ ?_)⟩
  · calc R ≤ max R (1 / δ) := le_max_left _ _
      _ ≤ m := hm.le
      _ ≤ n := by exact_mod_cast hn
  · rw [div_le_iff₀ (by positivity)]
    have h1 : 1 / δ < n := (le_max_right _ _).trans_lt (hm.trans_le (by exact_mod_cast hn))
    have h2 : 1 / δ * δ = 1 := by field_simp
    nlinarith [h1, hδ]

/-- **Runge's theorem on open sets, sequence form.** The approximants can be chosen as a
sequence converging locally uniformly on `U`. -/
theorem exists_seq_tendstoLocallyUniformlyOn_runge {U : Set ℂ} (hU : IsOpen U) {A : Set ℂ}
    (hAU : A ⊆ Uᶜ)
    (hA : ∀ w ∉ U, Bornology.IsBounded (connectedComponentIn Uᶜ w) →
      ∃ a ∈ A, a ∈ connectedComponentIn Uᶜ w)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ r : ℕ → ℂ → ℂ, (∀ n, r n ∈ Algebra.adjoin ℂ (rungeGenerators A)) ∧
      TendstoLocallyUniformlyOn r f atTop U := by
  have hchoice : ∀ n : ℕ, ∃ r ∈ Algebra.adjoin ℂ (rungeGenerators A),
      ∀ z ∈ rungeHull U n (1 / (n + 1)), ‖f z - r z‖ ≤ 1 / (n + 1) := fun n ↦
    runge_isOpen hU hAU hA hf (isCompact_rungeHull U n _)
      (rungeHull_subset (by positivity)) (1 / (n + 1)) (by positivity)
  choose r hr hrε using hchoice
  refine ⟨r, hr, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  obtain ⟨m, hm⟩ := exists_forall_subset_rungeHull_nat hU hK hKU
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop m, (hlim.eventually (gt_mem_nhds hε))] with n hn hnε z hz
  rw [dist_eq_norm]
  exact (hrε n z (hm n hn hz)).trans_lt hnε

/-- **Polynomial approximation on open sets.** If every component of the complement of `U` is
unbounded, every function holomorphic on `U` is a locally uniform limit of polynomials. -/
theorem exists_polynomial_tendstoLocallyUniformlyOn {U : Set ℂ} (hU : IsOpen U)
    (hUc : ∀ w ∉ U, ¬ Bornology.IsBounded (connectedComponentIn Uᶜ w))
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ p : ℕ → Polynomial ℂ, TendstoLocallyUniformlyOn (fun n z ↦ (p n).eval z) f atTop U := by
  obtain ⟨r, hr, hlim⟩ := exists_seq_tendstoLocallyUniformlyOn_runge hU (A := ∅)
    (empty_subset _) (fun w hw hb ↦ absurd hb (hUc w hw)) hf
  have hgen : rungeGenerators ∅ = {fun z : ℂ ↦ z} := by simp [rungeGenerators]
  have hpoly : ∀ n, ∃ p : Polynomial ℂ, ∀ z, r n z = p.eval z := by
    intro n
    have h := hr n
    rw [hgen, Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at h
    obtain ⟨p, hp⟩ := h
    refine ⟨p, fun z ↦ ?_⟩
    rw [← hp, Polynomial.aeval_fn_apply, Polynomial.coe_aeval_eq_eval]
  choose p hp using hpoly
  refine ⟨p, ?_⟩
  have : (fun n z ↦ (p n).eval z) = r := by
    ext n z
    exact (hp n z).symm
  rw [this]
  exact hlim

end Complex

end
