/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Perron

/-!
# Barriers and the Dirichlet problem on general domains

A **barrier** at a boundary point `ζ` of an open set `U` is a continuous subharmonic function
`β` on `U`, negative on `U`, tending to `0` at `ζ`, and bounded away from `0` outside every
neighborhood of `ζ`. At a boundary point with a barrier, the Perron function for boundary data
`g` continuous at `ζ` tends to `g ζ`. Boundary points satisfying the **exterior disc
condition** have the barrier `log (R / ‖z - c‖)`. Consequently the Dirichlet problem is
solvable on every bounded open set all of whose boundary points satisfy the exterior disc
condition, for continuous boundary data.

## Main definitions

* `Complex.IsBarrier U ζ β`.

## Main results

* `Complex.tendsto_perronFunction_of_isBarrier`: regularity of boundary points with a barrier.
* `Complex.isBarrier_log_of_exteriorDisc`: the exterior disc criterion.
* `Complex.exists_harmonicOnNhd_tendsto_of_exteriorDisc`: the Dirichlet problem.

## References

* L. V. Ahlfors, *Complex Analysis*, Section 6.4.
* T. W. Gamelin, *Complex Analysis*, Section XV.4.
* J. B. Conway, *Functions of One Complex Variable I*, Section X.4.
-/

public noncomputable section

open Set Metric Filter Function InnerProductSpace Real
open scoped Topology

namespace Complex

variable {U : Set ℂ} {ζ : ℂ} {g : ℂ → ℝ}

/-- The barrier conditions for a function on `U` relative to a point `ζ`. Membership of `ζ`
in the boundary of `U` is a separate hypothesis in applications. -/
structure IsBarrier (U : Set ℂ) (ζ : ℂ) (β : ℂ → ℝ) : Prop where
  /-- Subharmonic on `U`. -/
  subharmonicOn : SubharmonicOn β U
  /-- Continuous on `U`. -/
  continuousOn : ContinuousOn β U
  /-- Negative on `U`. -/
  neg : ∀ z ∈ U, β z < 0
  /-- Tends to `0` at `ζ`. -/
  tendsto : Tendsto β (𝓝[U] ζ) (𝓝 0)
  /-- Bounded away from `0` outside every neighborhood of `ζ`. -/
  far : ∀ δ > 0, ∃ η > 0, ∀ z ∈ U, δ ≤ dist z ζ → β z ≤ -η

/-- **Regularity of boundary points with a barrier.** If `ζ ∈ frontier U` has a barrier and the
bounded boundary data `g` is continuous at `ζ` along the frontier, then the Perron function
tends to `g ζ` at `ζ`. -/
theorem tendsto_perronFunction_of_isBarrier (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {m M : ℝ} (hm : ∀ ξ ∈ frontier U, m ≤ g ξ) (hgM : ∀ ξ ∈ frontier U, g ξ ≤ M)
    (hζ : ζ ∈ frontier U) (hg : ContinuousWithinAt g (frontier U) ζ) {β : ℂ → ℝ}
    (hβ : IsBarrier U ζ β) : Tendsto (perronFunction U g) (𝓝[U] ζ) (𝓝 (g ζ)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hζU : ζ ∉ U := by
    rw [hU.frontier_eq] at hζ
    exact hζ.2
  have hmM : m ≤ M := (hm ζ hζ).trans (hgM ζ hζ)
  -- continuity of `g` at `ζ`
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.mp hg (ε / 2) (half_pos hε)
  -- the barrier is bounded away from zero at distance `δ / 2` from `ζ`
  obtain ⟨η, hη, hηβ⟩ := hβ.far (δ / 2) (half_pos hδ)
  set K : ℝ := (M - m) / η with hK_def
  have hK0 : 0 ≤ K := by positivity
  have hKη : K * η = M - m := by rw [hK_def]; field_simp
  -- points of `U` near a boundary point far from `ζ` are far from `ζ`
  have hfar : ∀ ξ ∈ frontier U, δ ≤ dist ξ ζ → ∀ᶠ z in 𝓝[U] ξ, δ / 2 ≤ dist z ζ := by
    intro ξ hξ hξζ
    apply nhdsWithin_le_nhds
    have : ∀ᶠ z in 𝓝 ξ, dist z ξ < δ / 2 := ball_mem_nhds ξ (half_pos hδ)
    filter_upwards [this] with z hz
    have := dist_triangle ξ z ζ
    rw [dist_comm ξ z] at this
    linarith
  -- lower bound: the member `g ζ - ε / 2 + K β`
  have hlower : ∀ z ∈ U, g ζ - ε / 2 + K * β z ≤ perronFunction U g z := by
    intro z hz
    have hmem : IsPerronMember U g fun z ↦ g ζ - ε / 2 + K * β z := by
      refine ⟨(subharmonicOn_const _ _).add (hβ.subharmonicOn.const_mul hK0),
        continuousOn_const.add (continuousOn_const.mul hβ.continuousOn), fun ξ hξ ε' hε' ↦ ?_⟩
      by_cases hξζ : dist ξ ζ < δ
      · have h1 := hδg hξ hξζ
        rw [Real.dist_eq, abs_lt] at h1
        filter_upwards [self_mem_nhdsWithin] with z hz
        have : K * β z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK0 (hβ.neg z hz).le
        linarith
      · push Not at hξζ
        filter_upwards [hfar ξ hξ hξζ, self_mem_nhdsWithin] with z hz hzU
        have h1 := hηβ z hzU hz
        have h2 : K * β z ≤ K * (-η) := mul_le_mul_of_nonneg_left h1 hK0
        have h3 := hm ξ hξ
        have h4 := hgM ζ hζ
        nlinarith
    exact hmem.le_perronFunction hU hUb hgM hz
  -- upper bound: every member is at most `g ζ + ε / 2 - K β`
  have hupper : ∀ z ∈ U, perronFunction U g z ≤ g ζ + ε / 2 - K * β z := by
    intro z hz
    have : Nonempty {v : ℂ → ℝ // IsPerronMember U g v} := ⟨⟨_, isPerronMember_const hm⟩⟩
    refine ciSup_le fun v ↦ ?_
    have hsub : SubharmonicOn (fun z ↦ v.1 z + K * β z + (-(g ζ + ε / 2))) U :=
      (v.2.subharmonicOn.add (hβ.subharmonicOn.const_mul hK0)).add (subharmonicOn_const _ _)
    have hle := hsub.le_of_frontier hU hUb (M := 0) fun ξ hξ ε' hε' ↦ ?_
    · have := hle z hz
      linarith
    · by_cases hξζ : dist ξ ζ < δ
      · have h1 := hδg hξ hξζ
        rw [Real.dist_eq, abs_lt] at h1
        filter_upwards [v.2.boundary ξ hξ ε' hε', self_mem_nhdsWithin] with z hz hzU
        have : K * β z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK0 (hβ.neg z hzU).le
        linarith
      · push Not at hξζ
        filter_upwards [v.2.boundary ξ hξ ε' hε', hfar ξ hξ hξζ, self_mem_nhdsWithin]
          with z hz hzfar hzU
        have h1 := hηβ z hzU hzfar
        have h2 : K * β z ≤ K * (-η) := mul_le_mul_of_nonneg_left h1 hK0
        have h3 := hgM ξ hξ
        have h4 := hm ζ hζ
        nlinarith
  -- the barrier is small near `ζ`
  have hβsmall : ∀ᶠ z in 𝓝[U] ζ, -(ε / 2) < K * β z := by
    have hpos : 0 < ε / 2 / (K + 1) := by positivity
    filter_upwards [hβ.tendsto (Metric.ball_mem_nhds (0 : ℝ) hpos)] with z hz
    rw [mem_preimage, mem_ball, Real.dist_eq, sub_zero, abs_lt] at hz
    have h1 : K * (-(ε / 2 / (K + 1))) ≤ K * β z := mul_le_mul_of_nonneg_left hz.1.le hK0
    have h2 : K / (K + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    have h3 : K * (ε / 2 / (K + 1)) < ε / 2 := by
      calc K * (ε / 2 / (K + 1)) = ε / 2 * (K / (K + 1)) := by ring
        _ < ε / 2 := mul_lt_of_lt_one_right (half_pos hε) h2
    linarith
  obtain ⟨δ', hδ', hδ'β⟩ := Metric.mem_nhdsWithin_iff.mp hβsmall
  refine ⟨δ', hδ', fun z hz hzζ ↦ ?_⟩
  have h1 := hlower z hz
  have h2 := hupper z hz
  have h3 : -(ε / 2) < K * β z := hδ'β ⟨mem_ball.mpr hzζ, hz⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **The exterior disc criterion.** If a closed disc meets the closure of `U` exactly in the
boundary point `ζ`, then `log (R / ‖z - c‖)` is a barrier at `ζ`. -/
theorem isBarrier_log_of_exteriorDisc (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hζ : ζ ∈ frontier U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hdisc : closedBall c R ∩ closure U = {ζ}) :
    IsBarrier U ζ fun z ↦ Real.log (R / ‖z - c‖) := by
  have hζU : ζ ∉ U := by
    rw [hU.frontier_eq] at hζ
    exact hζ.2
  have hζcl : ζ ∈ closure U := frontier_subset_closure hζ
  have hζmem : ζ ∈ closedBall c R ∩ closure U := by
    rw [hdisc]
    exact mem_singleton ζ
  have hζc : ‖ζ - c‖ ≤ R := mem_closedBall_iff_norm.mp hζmem.1
  -- points of the closure other than `ζ` lie outside the closed disc
  have hout' : ∀ z ∈ closure U, z ≠ ζ → R < ‖z - c‖ := by
    intro z hz hzζ
    by_contra h
    push Not at h
    have : z ∈ closedBall c R ∩ closure U := ⟨mem_closedBall_iff_norm.mpr h, hz⟩
    rw [hdisc, mem_singleton_iff] at this
    exact hzζ this
  have hout : ∀ z ∈ U, R < ‖z - c‖ := fun z hz ↦
    hout' z (subset_closure hz) fun h ↦ hζU (h ▸ hz)
  have hζR : ‖ζ - c‖ = R := by
    refine le_antisymm hζc ?_
    by_contra hlt
    push Not at hlt
    have hmem : ball c R ∈ 𝓝 ζ := isOpen_ball.mem_nhds (mem_ball_iff_norm.mpr hlt)
    obtain ⟨z, hzb, hzU⟩ := mem_closure_iff_nhds.mp hζcl _ hmem
    exact absurd (mem_ball_iff_norm.mp hzb) (not_lt.mpr (hout z hzU).le)
  have hne : ∀ z ∈ U, z - c ≠ 0 := fun z hz h ↦ by
    have := hout z hz
    rw [h, norm_zero] at this
    linarith
  -- harmonicity
  have hharm : HarmonicOnNhd (fun z ↦ Real.log (R / ‖z - c‖)) U := by
    intro z hz
    have h1 : HarmonicAt (fun w ↦ Real.log ‖(fun w ↦ w - c) w‖) z :=
      (analyticAt_id.sub analyticAt_const).harmonicAt_log_norm (hne z hz)
    have hev : (fun z ↦ Real.log (R / ‖z - c‖)) =ᶠ[𝓝 z]
        (fun _ ↦ Real.log R) - fun w ↦ Real.log ‖(fun w ↦ w - c) w‖ := by
      have hopen : IsOpen {w : ℂ | w - c ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
      filter_upwards [hopen.mem_nhds (hne z hz)] with w hw
      simp only [Pi.sub_apply]
      rw [Real.log_div hR.ne' (norm_ne_zero_iff.mpr hw)]
    rw [harmonicAt_congr_nhds hev]
    exact (harmonicAt_const _).sub h1
  refine ⟨hharm.subharmonicOn hU, ?_, fun z hz ↦ ?_, ?_, fun δ hδ ↦ ?_⟩
  · -- continuity
    refine ContinuousOn.log (continuousOn_const.div (by fun_prop) fun z hz ↦
      norm_ne_zero_iff.mpr (hne z hz)) fun z hz ↦ ?_
    exact div_ne_zero hR.ne' (norm_ne_zero_iff.mpr (hne z hz))
  · -- negativity
    have := hout z hz
    exact Real.log_neg (div_pos hR (by linarith)) ((div_lt_one (by linarith)).mpr this)
  · -- the limit at `ζ`
    have h1 : Tendsto (fun z ↦ R / ‖z - c‖) (𝓝[U] ζ) (𝓝 (R / ‖ζ - c‖)) :=
      (tendsto_const_nhds.div ((continuous_norm.comp (continuous_id.sub continuous_const)).tendsto
        ζ) (by simp only [Function.comp_apply, Pi.sub_apply, id]; rw [hζR]; exact hR.ne')).mono_left
        nhdsWithin_le_nhds
    have h2 := h1.log (by rw [hζR]; exact (div_pos hR hR).ne')
    rwa [hζR, div_self hR.ne', Real.log_one] at h2
  · -- bounded away from zero far from `ζ`
    set Kset : Set ℂ := closure U \ ball ζ δ
    have hcomp : IsCompact (closure U) := by
      obtain ⟨R', hR'⟩ := hUb.subset_closedBall 0
      exact (isCompact_closedBall 0 R').of_isClosed_subset isClosed_closure
        (isClosed_closedBall.closure_subset_iff.mpr hR')
    have hKc : IsCompact Kset := hcomp.diff isOpen_ball
    rcases Kset.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨1, one_pos, fun z hz hzδ ↦ ?_⟩
      exfalso
      have : z ∈ Kset := ⟨subset_closure hz, fun h ↦ absurd (mem_ball.mp h) (not_lt.mpr hzδ)⟩
      rw [hKe] at this
      exact this
    · obtain ⟨z₀, hz₀, hmin⟩ := hKc.exists_isMinOn hKne
        (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
      have hz₀ζ : z₀ ≠ ζ := fun h ↦ hz₀.2 (h ▸ mem_ball_self hδ)
      have hz₀R : R < ‖z₀ - c‖ := hout' z₀ hz₀.1 hz₀ζ
      refine ⟨Real.log (‖z₀ - c‖ / R), Real.log_pos ((one_lt_div hR).mpr hz₀R), fun z hz hzδ ↦ ?_⟩
      have hzK : z ∈ Kset := ⟨subset_closure hz, fun h ↦ absurd (mem_ball.mp h) (not_lt.mpr hzδ)⟩
      have h1 : ‖z₀ - c‖ ≤ ‖z - c‖ := hmin hzK
      rw [← Real.log_inv, inv_div]
      exact Real.log_le_log (div_pos hR (by linarith))
        (div_le_div_of_nonneg_left hR.le (by linarith) h1)

/-- **The Dirichlet problem on domains with the exterior disc property.** On a bounded open set
all of whose boundary points satisfy the exterior disc condition, continuous boundary data on
the frontier are the boundary values of a harmonic function. -/
theorem exists_harmonicOnNhd_tendsto_of_exteriorDisc (hU : IsOpen U)
    (hUb : Bornology.IsBounded U)
    (hext : ∀ ζ ∈ frontier U, ∃ (c : ℂ) (R : ℝ), 0 < R ∧ closedBall c R ∩ closure U = {ζ})
    (hg : ContinuousOn g (frontier U)) :
    ∃ u : ℂ → ℝ, HarmonicOnNhd u U ∧ ∀ ζ ∈ frontier U, Tendsto u (𝓝[U] ζ) (𝓝 (g ζ)) := by
  have hcomp : IsCompact (closure U) := by
    obtain ⟨R', hR'⟩ := hUb.subset_closedBall 0
    exact (isCompact_closedBall 0 R').of_isClosed_subset isClosed_closure
      (isClosed_closedBall.closure_subset_iff.mpr hR')
  have hfr : IsCompact (frontier U) := hcomp.of_isClosed_subset isClosed_frontier
    frontier_subset_closure
  obtain ⟨C, hC⟩ := hfr.exists_bound_of_continuousOn hg
  have hm : ∀ ζ ∈ frontier U, -C ≤ g ζ := fun ζ hζ ↦ by
    have := hC ζ hζ
    rw [Real.norm_eq_abs, abs_le] at this
    exact this.1
  have hM : ∀ ζ ∈ frontier U, g ζ ≤ C := fun ζ hζ ↦ by
    have := hC ζ hζ
    rw [Real.norm_eq_abs, abs_le] at this
    exact this.2
  refine ⟨perronFunction U g, harmonicOnNhd_perronFunction hU hUb hm hM, fun ζ hζ ↦ ?_⟩
  obtain ⟨c, R, hR, hdisc⟩ := hext ζ hζ
  exact tendsto_perronFunction_of_isBarrier hU hUb hm hM hζ (hg ζ hζ)
    (isBarrier_log_of_exteriorDisc hU hUb hζ hR hdisc)

end Complex

end
