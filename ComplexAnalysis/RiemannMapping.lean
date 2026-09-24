/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.DiscMobius
public import ComplexAnalysis.Montel
public import ComplexAnalysis.Hurwitz
public import ComplexAnalysis.Injective
public import ComplexAnalysis.BranchLog
public import ComplexAnalysis.HolomorphicInverse
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.OpenMapping

/-!
# The Riemann mapping theorem

Every nonempty simply connected proper open subset `U` of the plane admits a biholomorphic
map onto the unit disc, which can be normalized to send a given point `z₀ ∈ U` to `0`
with positive real derivative there.

The proof is the classical extremal argument. Among the injective holomorphic maps of `U` into
the disc sending `z₀` to `0` (`Complex.riemannFamily`), the family is nonempty (by the square
root construction and the open mapping theorem), the derivatives at `z₀` are bounded by the Cauchy
estimate, and Montel's theorem together with Hurwitz's theorem and the open mapping theorem
gives a member maximizing `‖deriv f z₀‖`. If the maximizer omitted a value `w` of the disc, a
holomorphic square root of `φ_w ∘ f` composed with a disc Möbius transformation would give a
member with larger derivative at `z₀`.

## Main results

* `Complex.exists_forall_norm_deriv_le_of_riemannFamily`: the extremal map exists.
* `Complex.ball_subset_image_of_forall_norm_deriv_le`: the extremal map is onto the disc.
* `Complex.exists_riemannMap`: the Riemann mapping theorem.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem VII.4.2.
* T. W. Gamelin, *Complex Analysis*, Section XI.4.
* B. Simon, *Basic Complex Analysis*, Theorem 8.1.1.
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open scoped Topology ComplexConjugate

namespace Complex

variable {U : Set ℂ} {z₀ : ℂ}

/-- The competing family in the proof of the Riemann mapping theorem: injective holomorphic
maps of `U` into the unit disc sending `z₀` to `0`. -/
def riemannFamily (U : Set ℂ) (z₀ : ℂ) : Set (ℂ → ℂ) :=
  {f | DifferentiableOn ℂ f U ∧ InjOn f U ∧ MapsTo f U (ball 0 1) ∧ f z₀ = 0}

/-- The family is nonempty for a simply connected proper open subset. -/
theorem riemannFamily_nonempty (hU : IsOpen U) (hUc : IsSimplyConnected U) (hne : U ≠ univ)
    (hz₀ : z₀ ∈ U) : (riemannFamily U z₀).Nonempty := by
  obtain ⟨a, ha⟩ := (ne_univ_iff_exists_notMem U).mp hne
  -- a holomorphic square root of `z - a`
  have hgd : DifferentiableOn ℂ (fun z => z - a) U := differentiableOn_id.sub_const a
  have hg0 : ∀ z ∈ U, z - a ≠ 0 := fun z hz h0 => ha (sub_eq_zero.mp h0 ▸ hz)
  obtain ⟨h, hh, hhsq⟩ := exists_analyticOnNhd_root hU hUc hgd hg0 two_ne_zero
  have hhd : DifferentiableOn ℂ h U := hh.differentiableOn
  have hhi : InjOn h U := fun x hx y hy hxy => by
    have : x - a = y - a := by rw [← hhsq x hx, ← hhsq y hy, hxy]
    exact sub_left_inj.mp this
  have hh0 : ∀ z ∈ U, h z ≠ 0 := fun z hz h0 => by
    have := hhsq z hz
    rw [h0, zero_pow two_ne_zero] at this
    exact hg0 z hz this.symm
  -- the image is open and disjoint from its negative
  have hopen : IsOpen (h '' U) := isOpen_image_of_injOn hU hhd hhi
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (h z₀) (mem_image_of_mem h hz₀)
  have hfar : ∀ z ∈ U, ε ≤ ‖h z + h z₀‖ := by
    intro z hz
    by_contra hlt
    push Not at hlt
    have hmem : -h z ∈ ball (h z₀) ε := by
      rw [mem_ball, dist_eq_norm, ← norm_neg]
      convert hlt using 2
      ring
    obtain ⟨y, hy, hyz⟩ := hball hmem
    have hya : y - a = z - a := by rw [← hhsq y hy, ← hhsq z hz, hyz, neg_sq]
    rw [sub_left_inj.mp hya] at hyz
    exact hh0 z hz (by linear_combination hyz / 2)
  have hden : ∀ z ∈ U, h z + h z₀ ≠ 0 := fun z hz h0 => by
    have := hfar z hz
    rw [h0, norm_zero] at this
    linarith
  -- the map `z ↦ (ε / 2) / (h z + h z₀)` into the disc
  set k : ℂ → ℂ := fun z => ((ε / 2 : ℝ) : ℂ) / (h z + h z₀) with hk_def
  have hkd : DifferentiableOn ℂ k U := (differentiableOn_const _).div (hhd.add_const _) hden
  have hkm : MapsTo k U (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff, hk_def]
    dsimp only
    rw [norm_div, norm_real, Real.norm_of_nonneg (by positivity),
      div_lt_one (lt_of_lt_of_le hε (hfar z hz))]
    linarith [hfar z hz]
  have hki : InjOn k U := by
    intro x hx y hy hxy
    have hε' : ((ε / 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (half_pos hε).ne'
    have h1 : ((ε / 2 : ℝ) : ℂ) / (h x + h z₀) = ((ε / 2 : ℝ) : ℂ) / (h y + h z₀) := hxy
    rw [div_eq_div_iff (hden x hx) (hden y hy)] at h1
    exact hhi hx hy (add_right_cancel (mul_left_cancel₀ hε' h1)).symm
  have hk1 : ‖k z₀‖ < 1 := mem_ball_zero_iff.mp (hkm hz₀)
  refine ⟨fun z => discMobius (k z₀) (k z), ?_, ?_, ?_, ?_⟩
  · exact (differentiableOn_discMobius_ball hk1).comp hkd hkm
  · intro a ha' b hb' hab
    exact hki ha' hb' (discMobius_injOn hk1 (ball_subset_closedBall (hkm ha'))
      (ball_subset_closedBall (hkm hb')) hab)
  · exact fun z hz => mapsTo_discMobius_ball hk1 (hkm hz)
  · exact discMobius_self _

/-- The Cauchy estimate bounds the derivatives at `z₀` of the members of the family. -/
theorem norm_deriv_le_of_mem_riemannFamily {r : ℝ} (hr : 0 < r) (hrU : closedBall z₀ r ⊆ U)
    {f : ℂ → ℂ} (hf : f ∈ riemannFamily U z₀) : ‖deriv f z₀‖ ≤ 1 / r := by
  obtain ⟨hfd, -, hfm, -⟩ := hf
  refine norm_deriv_le_of_forall_mem_sphere_norm_le hr (hfd.diffContOnCl_ball hrU)
    fun z hz => ?_
  exact (mem_ball_zero_iff.mp (hfm (hrU (sphere_subset_closedBall hz)))).le

/-- **The extremal map exists.** Montel, Hurwitz, and the open mapping theorem provide a
member of the family maximizing `‖deriv f z₀‖`. -/
theorem exists_forall_norm_deriv_le_of_riemannFamily (hU : IsOpen U) (hUc : IsSimplyConnected U)
    (hne : U ≠ univ) (hz₀ : z₀ ∈ U) :
    ∃ g ∈ riemannFamily U z₀, ∀ f ∈ riemannFamily U z₀, ‖deriv f z₀‖ ≤ ‖deriv g z₀‖ := by
  set S := riemannFamily U z₀ with hS_def
  have hSne := riemannFamily_nonempty hU hUc hne hz₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hrU' : closedBall z₀ (r / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hrU
  set D : Set ℝ := (fun f => ‖deriv f z₀‖) '' S with hD_def
  have hDne : D.Nonempty := hSne.image _
  have hDbdd : BddAbove D := by
    refine ⟨1 / (r / 2), ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    exact norm_deriv_le_of_mem_riemannFamily (half_pos hr) hrU' hf
  obtain ⟨u, -, hu, huD⟩ := exists_seq_tendsto_sSup hDne hDbdd
  choose f hfS hfu using huD
  have hfd : ∀ n, DifferentiableOn ℂ (f n) U := fun n => (hfS n).1
  obtain ⟨g, φ, hφ, hgd, hlim⟩ := exists_subseq_tendstoLocallyUniformlyOn_of_bounded_on_compacts
    hU hfd fun K hKU _ => ⟨1, fun n z hz => (mem_ball_zero_iff.mp ((hfS n).2.2.1 (hKU hz))).le⟩
  -- the derivatives at `z₀` converge
  have hderiv : Tendsto (fun n => deriv (f (φ n)) z₀) atTop (𝓝 (deriv g z₀)) :=
    (hlim.deriv (Eventually.of_forall fun n => hfd (φ n)) hU).tendsto_at hz₀
  have hnorm' : Tendsto (fun n => ‖deriv (f (φ n)) z₀‖) atTop (𝓝 (sSup D)) := by
    simp only [hfu]
    exact hu.comp hφ.tendsto_atTop
  have hgM : ‖deriv g z₀‖ = sSup D := tendsto_nhds_unique hderiv.norm hnorm'
  -- the supremum is positive
  obtain ⟨f₀, hf₀⟩ := hSne
  have hM0 : 0 < sSup D :=
    lt_of_lt_of_le (norm_pos_iff.mpr (deriv_ne_zero_of_injOn hU hf₀.1 hf₀.2.1 hz₀))
      (le_csSup hDbdd ⟨f₀, hf₀, rfl⟩)
  have hgz₀ : deriv g z₀ ≠ 0 := by
    rw [← norm_pos_iff, hgM]
    exact hM0
  have hg0 : g z₀ = 0 := by
    have h1 : Tendsto (fun n => f (φ n) z₀) atTop (𝓝 (g z₀)) := hlim.tendsto_at hz₀
    have h2 : Tendsto (fun n => f (φ n) z₀) atTop (𝓝 0) := by
      simp only [(hfS _).2.2.2]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hgle : ∀ z ∈ U, ‖g z‖ ≤ 1 := fun z hz =>
    le_of_tendsto (hlim.tendsto_at hz).norm
      (Eventually.of_forall fun n => (mem_ball_zero_iff.mp ((hfS (φ n)).2.2.1 hz)).le)
  have hUconn : IsPreconnected U := hUc.isPathConnected.isConnected.isPreconnected
  have hnotconst : ¬ ∃ v : ℂ, EqOn g (fun _ => v) U := by
    rintro ⟨v, hv⟩
    apply hgz₀
    rw [(hv.eventuallyEq_of_mem (hU.mem_nhds hz₀)).deriv_eq]
    exact deriv_const _ _
  -- injective by Hurwitz's theorem
  have hgi : InjOn g U :=
    (eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn hU hUconn
      (Eventually.of_forall fun n => hfd (φ n)) (Eventually.of_forall fun n => (hfS (φ n)).2.1)
      hlim).resolve_left hnotconst
  -- maps into the open disc by the open mapping theorem
  have hgm : MapsTo g U (ball 0 1) := by
    have hopen : IsOpen (g '' U) := by
      rcases (hgd.analyticOnNhd hU).is_constant_or_isOpen hUconn with ⟨w, hw⟩ | h
      · exact absurd ⟨w, fun z hz => hw z hz⟩ hnotconst
      · exact h U subset_rfl hU
    intro z hz
    have hsub : g '' U ⊆ closedBall 0 1 := by
      rintro _ ⟨w, hw, rfl⟩
      exact mem_closedBall_zero_iff.mpr (hgle w hw)
    have := interior_maximal hsub hopen (mem_image_of_mem g hz)
    rwa [interior_closedBall' (0 : ℂ) 1] at this
  refine ⟨g, ⟨hgd, hgi, hgm, hg0⟩, fun f hf => ?_⟩
  rw [hgM]
  exact le_csSup hDbdd ⟨f, hf, rfl⟩

/-- **The extremal map is onto the disc.** A member of the family maximizing `‖deriv f z₀‖`
omits no value of the unit disc: otherwise the square root trick produces a member with larger
derivative. -/
theorem ball_subset_image_of_forall_norm_deriv_le (hU : IsOpen U) (hUc : IsSimplyConnected U)
    (hz₀ : z₀ ∈ U) {g : ℂ → ℂ} (hg : g ∈ riemannFamily U z₀)
    (hmax : ∀ f ∈ riemannFamily U z₀, ‖deriv f z₀‖ ≤ ‖deriv g z₀‖) : ball 0 1 ⊆ g '' U := by
  obtain ⟨hgd, hgi, hgm, hg0⟩ := hg
  by_contra hcon
  obtain ⟨w, hw, hwg⟩ := not_subset.mp hcon
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hw0 : w ≠ 0 := fun h => hwg ⟨z₀, hz₀, by rw [hg0, h]⟩
  -- the nonvanishing function `φ_w ∘ g`
  set g₁ : ℂ → ℂ := fun z => discMobius w (g z) with hg₁_def
  have hg₁d : DifferentiableOn ℂ g₁ U := (differentiableOn_discMobius_ball hw1).comp hgd hgm
  have hg₁0 : ∀ z ∈ U, g₁ z ≠ 0 := by
    intro z hz h
    refine hwg ⟨z, hz, ?_⟩
    exact (discMobius_eq_zero_iff
      (one_sub_conj_mul_ne_zero hw1 (mem_ball_zero_iff.mp (hgm hz)).le)).mp h
  have hg₁m : ∀ z ∈ U, ‖g₁ z‖ < 1 := fun z hz =>
    norm_discMobius_lt_one hw1 (mem_ball_zero_iff.mp (hgm hz))
  -- a holomorphic square root
  obtain ⟨h, hh, hhsq⟩ := exists_analyticOnNhd_root hU hUc hg₁d hg₁0 two_ne_zero
  have hhd : DifferentiableOn ℂ h U := hh.differentiableOn
  have hhm : ∀ z ∈ U, ‖h z‖ < 1 := by
    intro z hz
    have : ‖h z‖ ^ 2 < 1 := by
      rw [← norm_pow, hhsq z hz]
      exact hg₁m z hz
    nlinarith [norm_nonneg (h z)]
  have hhi : InjOn h U := by
    intro a ha b hb hab
    have h1 : g₁ a = g₁ b := by rw [← hhsq a ha, ← hhsq b hb, hab]
    exact hgi ha hb (discMobius_injOn hw1 (ball_subset_closedBall (hgm ha))
      (ball_subset_closedBall (hgm hb)) h1)
  set c := h z₀ with hc_def
  have hc1 : ‖c‖ < 1 := hhm z₀ hz₀
  have hcsq : c ^ 2 = -w := by
    rw [hc_def, hhsq z₀ hz₀, hg₁_def]
    simp [hg0]
  have hc0 : c ≠ 0 := by
    intro h0
    apply hw0
    rw [h0] at hcsq
    simpa using hcsq.symm
  -- the competitor `φ_c ∘ h`
  set ψ : ℂ → ℂ := fun z => discMobius c (h z) with hψ_def
  have hψ : ψ ∈ riemannFamily U z₀ := by
    refine ⟨?_, ?_, ?_, discMobius_self c⟩
    · exact (differentiableOn_discMobius_ball hc1).comp hhd
        fun z hz => mem_ball_zero_iff.mpr (hhm z hz)
    · intro a ha b hb hab
      exact hhi ha hb (discMobius_injOn hc1 (mem_closedBall_zero_iff.mpr (hhm a ha).le)
        (mem_closedBall_zero_iff.mpr (hhm b hb).le) hab)
    · exact fun z hz => mapsTo_discMobius_ball hc1 (mem_ball_zero_iff.mpr (hhm z hz))
  -- derivative computations at `z₀`
  have hhz₀ : HasDerivAt h (deriv h z₀) z₀ := (hhd.differentiableAt (hU.mem_nhds hz₀)).hasDerivAt
  have hgz₀ : HasDerivAt g (deriv g z₀) z₀ := (hgd.differentiableAt (hU.mem_nhds hz₀)).hasDerivAt
  have hψd : deriv ψ z₀ = (1 - (normSq c : ℂ))⁻¹ * deriv h z₀ := by
    have h1 : HasDerivAt (discMobius c) (deriv (discMobius c) c) c :=
      (differentiableAt_discMobius (one_sub_conj_mul_ne_zero hc1 hc1.le)).hasDerivAt
    have h2 := h1.comp z₀ hhz₀
    rw [← deriv_discMobius_self hc1]
    exact h2.deriv
  have hkey : 2 * c * deriv h z₀ = (1 - normSq w) * deriv g z₀ := by
    have hev : g₁ =ᶠ[𝓝 z₀] fun z => h z * h z := by
      filter_upwards [hU.mem_nhds hz₀] with z hz
      rw [← sq, hhsq z hz]
    have hd1 : HasDerivAt g₁ (deriv h z₀ * h z₀ + h z₀ * deriv h z₀) z₀ :=
      (hhz₀.mul hhz₀).congr_of_eventuallyEq hev
    have hd2 : HasDerivAt g₁ (deriv (discMobius w) (g z₀) * deriv g z₀) z₀ := by
      have hw' : 1 - conj w * g z₀ ≠ 0 := by
        rw [hg0]
        simp
      exact (differentiableAt_discMobius hw').hasDerivAt.comp z₀ hgz₀
    have := hd1.unique hd2
    rw [hg0, deriv_discMobius_zero] at this
    rw [← hc_def] at this
    linear_combination this
  -- norms
  set t := ‖c‖ with ht_def
  have ht0 : 0 < t := norm_pos_iff.mpr hc0
  have ht1 : t < 1 := hc1
  have hwt : ‖w‖ = t ^ 2 := by
    rw [← norm_neg, ← hcsq, norm_pow]
  have hM : 0 < ‖deriv g z₀‖ := norm_pos_iff.mpr (deriv_ne_zero_of_injOn hU hgd hgi hz₀)
  have h1t : 0 < 1 - t ^ 2 := by nlinarith
  have hA : ‖deriv ψ z₀‖ * (1 - t ^ 2) = ‖deriv h z₀‖ := by
    have hnc : ‖(1 - (normSq c : ℂ))⁻¹‖ = (1 - t ^ 2)⁻¹ := by
      rw [norm_inv, show (1 - (normSq c : ℂ)) = ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) by
        rw [normSq_eq_norm_sq]; push_cast; ring, norm_real, Real.norm_of_nonneg h1t.le]
    rw [hψd, norm_mul, hnc, inv_mul_eq_div, div_mul_cancel₀ _ h1t.ne']
  have hB : 2 * t * ‖deriv h z₀‖ = (1 - t ^ 4) * ‖deriv g z₀‖ := by
    have hnw : ‖(1 - (normSq w : ℂ))‖ = 1 - t ^ 4 := by
      rw [show (1 - (normSq w : ℂ)) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) by
        rw [normSq_eq_norm_sq]; push_cast; ring, norm_real, hwt, Real.norm_of_nonneg (by nlinarith)]
      ring
    have := congrArg norm hkey
    rw [norm_mul, norm_mul, norm_mul, hnw] at this
    simpa using this
  have h2 : 2 * t * ‖deriv ψ z₀‖ = (1 + t ^ 2) * ‖deriv g z₀‖ := by
    have : (1 - t ^ 2) * (2 * t * ‖deriv ψ z₀‖) = (1 - t ^ 2) * ((1 + t ^ 2) * ‖deriv g z₀‖) := by
      linear_combination (2 * t) * hA + hB
    exact mul_left_cancel₀ h1t.ne' this
  have hlt : ‖deriv g z₀‖ < ‖deriv ψ z₀‖ := by
    have h3 : 2 * t * (‖deriv ψ z₀‖ - ‖deriv g z₀‖) = (1 - t) ^ 2 * ‖deriv g z₀‖ := by
      linear_combination h2
    have hpos : 0 < (1 - t) ^ 2 * ‖deriv g z₀‖ := mul_pos (pow_pos (sub_pos.mpr ht1) 2) hM
    nlinarith
  exact absurd (hmax ψ hψ) (not_le.mpr hlt)

/-- **The Riemann mapping theorem.** A simply connected open proper subset `U` of the plane
is mapped by an injective holomorphic function onto the unit disc, normalized so that a given
point `z₀ ∈ U` goes to `0` with positive real derivative.

Related formalizations: Vincent Beffara's RMT4 and Yury Kudryashov's Mathlib PR #33505. See
`CREDITS.md`. -/
theorem exists_riemannMap (hU : IsOpen U) (hUc : IsSimplyConnected U) (hne : U ≠ univ)
    (hz₀ : z₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ InjOn f U ∧ f '' U = ball 0 1 ∧ f z₀ = 0 ∧
      ∃ r : ℝ, 0 < r ∧ deriv f z₀ = r := by
  obtain ⟨g, hg, hmax⟩ := exists_forall_norm_deriv_le_of_riemannFamily hU hUc hne hz₀
  have himg : g '' U = ball 0 1 :=
    Subset.antisymm hg.2.2.1.image_subset
      (ball_subset_image_of_forall_norm_deriv_le hU hUc hz₀ hg hmax)
  obtain ⟨hgd, hgi, hgm, hg0⟩ := hg
  set d := deriv g z₀ with hd_def
  have hd0 : d ≠ 0 := deriv_ne_zero_of_injOn hU hgd hgi hz₀
  have hdc : (‖d‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hd0)
  set c : ℂ := conj d / ‖d‖ with hc_def
  have hc1 : ‖c‖ = 1 := by
    rw [hc_def, norm_div, norm_conj, norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hd0)]
  have hc0 : c ≠ 0 := by
    rw [← norm_ne_zero_iff, hc1]
    exact one_ne_zero
  refine ⟨fun z => c * g z, hgd.const_mul c, ?_, ?_, by simp [hg0], ‖d‖, norm_pos_iff.mpr hd0, ?_⟩
  · exact fun a ha b hb hab => hgi ha hb (mul_left_cancel₀ hc0 hab)
  · rw [← Set.image_image (fun w => c * w) g U, himg]
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [mem_ball_zero_iff] at hv ⊢
      rw [norm_mul, hc1, one_mul]
      exact hv
    · intro hw
      refine ⟨c⁻¹ * w, ?_, mul_inv_cancel_left₀ hc0 w⟩
      rw [mem_ball_zero_iff] at hw ⊢
      rw [norm_mul, norm_inv, hc1, inv_one, one_mul]
      exact hw
  · have hderiv : deriv (fun z => c * g z) z₀ = c * d :=
      ((hgd.differentiableAt (hU.mem_nhds hz₀)).hasDerivAt.const_mul c).deriv
    rw [hderiv, hc_def, div_mul_eq_mul_div, conj_mul', sq, mul_div_assoc, div_self hdc, mul_one]

end Complex

end
