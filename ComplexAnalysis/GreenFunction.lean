/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Perron.Barrier

/-!
# The Green function of a domain

For a bounded open set `U` with the exterior disc property and a pole `w ∈ U`, the **Green
function** `G(·, w)` is the harmonic compensator for the logarithmic singularity at `w`: a
function `G : ℂ → ℝ`, harmonic on `U \ {w}`, with `G(z) + log ‖z - w‖` extending harmonically
across `w`, vanishing at the boundary of `U`, and nonnegative on `U \ {w}` (the sharper
classical strict positivity needs the strong maximum principle on the preconnected punctured
domain and is not proved here).

The construction solves the Dirichlet problem (`Perron.Barrier`) with boundary data
`ζ ↦ log ‖ζ - w‖`, giving a harmonic `h` on `U` with these boundary values, and sets
`G z = h z - log ‖z - w‖`. Nonnegativity follows from the maximum principle for the
subharmonic function `-G` on the punctured domain `U \ {w}`, whose frontier is
`frontier U ∪ {w}`: `-G → 0` at `frontier U` and `-G → -∞` at `w`.

Symmetry `G(z, w) = G(w, z)`, the deeper classical fact about the Green function, is not proved
here.

## Main results

* `Complex.exists_greenFunction`: existence, the harmonic compensator, boundary vanishing, and
  nonnegativity of the Green function.

## References

* T. Gamelin, *Complex Analysis*, Chapter XV, Sections 2–3.
* J. B. Conway, *Functions of One Complex Variable II*, Section 19.7–19.9.
-/

public noncomputable section

open Set Metric Filter InnerProductSpace
open scoped Topology

namespace Complex

variable {U : Set ℂ}

/-- A frontier point of the punctured open set `U \ {w}` is either a frontier point of `U` or
equals `w`. -/
theorem mem_frontier_or_eq_of_mem_frontier_diff_singleton (hU : IsOpen U) {w ζ : ℂ}
    (hζ : ζ ∈ frontier (U \ {w})) : ζ ∈ frontier U ∨ ζ = w := by
  by_cases hζw : ζ = w
  · exact Or.inr hζw
  · refine Or.inl ?_
    have hcl : ζ ∈ closure (U \ {w}) := frontier_subset_closure hζ
    have hcl' : ζ ∈ closure U := closure_mono sdiff_subset hcl
    have hnU : ζ ∉ U \ {w} := by
      have hPO : IsOpen (U \ {w}) := hU.sdiff isClosed_singleton
      rw [hPO.frontier_eq] at hζ
      exact hζ.2
    rw [hU.frontier_eq]
    refine ⟨hcl', fun hζU => hnU ⟨hζU, ?_⟩⟩
    simpa using hζw

/-- **Existence of the Green function.** On a bounded open set with the exterior disc property,
with pole `w ∈ U`, there is a function `G` harmonic on `U \ {w}`, whose sum with `log ‖z - w‖`
extends harmonically across `w`, vanishing at the boundary of `U`, and positive elsewhere on
`U`. -/
theorem exists_greenFunction (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hext : ∀ ζ ∈ frontier U, ∃ (c : ℂ) (R : ℝ), 0 < R ∧ closedBall c R ∩ closure U = {ζ})
    {w : ℂ} (hw : w ∈ U) :
    ∃ G : ℂ → ℝ, HarmonicOnNhd (fun z => G z + Real.log ‖z - w‖) U ∧
      (∀ ζ ∈ frontier U, Tendsto G (𝓝[U] ζ) (𝓝 0)) ∧
      (∀ z ∈ U, z ≠ w → 0 ≤ G z) := by
  have hwU : w ∉ frontier U := by rw [hU.frontier_eq]; exact fun h => h.2 hw
  have hgcont : ContinuousOn (fun ζ => Real.log ‖ζ - w‖) (frontier U) := by
    refine ContinuousOn.log (by fun_prop) fun ζ hζ => ?_
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h => hwU (h ▸ hζ))
  obtain ⟨h, hharm, hbd⟩ := exists_harmonicOnNhd_tendsto_of_exteriorDisc hU hUb hext hgcont
  set G : ℂ → ℝ := fun z => h z - Real.log ‖z - w‖ with hG_def
  have hharmG : HarmonicOnNhd (fun z => G z + Real.log ‖z - w‖) U := by
    have hev : (fun z => G z + Real.log ‖z - w‖) = h := by funext z; rw [hG_def]; ring
    rw [hev]; exact hharm
  -- vanishing at the boundary of `U`
  have hGvanish : ∀ ζ ∈ frontier U, Tendsto G (𝓝[U] ζ) (𝓝 0) := by
    intro ζ hζ
    have h1 : Tendsto h (𝓝[U] ζ) (𝓝 (Real.log ‖ζ - w‖)) := hbd ζ hζ
    have hζw : ζ - w ≠ 0 := sub_ne_zero.mpr fun h => hwU (h ▸ hζ)
    have h2 : Tendsto (fun z : ℂ => Real.log ‖z - w‖) (𝓝[U] ζ) (𝓝 (Real.log ‖ζ - w‖)) :=
      (((continuous_norm.comp (continuous_id.sub continuous_const)).tendsto ζ).log
        (norm_ne_zero_iff.mpr hζw)).mono_left nhdsWithin_le_nhds
    have := h1.sub h2
    simpa [hG_def] using this
  refine ⟨G, hharmG, hGvanish, ?_⟩
  -- positivity via the maximum principle for `-G` on the punctured domain
  intro z₀ hz₀U hz₀w
  have hPO : IsOpen (U \ {w}) := hU.sdiff isClosed_singleton
  have hPb : Bornology.IsBounded (U \ {w}) := hUb.subset sdiff_subset
  have hne : ∀ z ∈ U \ {w}, z - w ≠ 0 := fun z hz => sub_ne_zero.mpr hz.2
  have hharmMinus : HarmonicOnNhd (fun z => -G z) (U \ {w}) := by
    intro z hz
    have h1 : HarmonicAt (fun v => Real.log ‖(fun v => v - w) v‖) z :=
      (analyticAt_id.sub analyticAt_const).harmonicAt_log_norm (hne z hz)
    have h2 : HarmonicAt h z := hharm z hz.1
    have hev : (fun z => -G z) =ᶠ[𝓝 z]
        (fun v => Real.log ‖(fun v => v - w) v‖) - h := by
      filter_upwards with v
      simp only [Pi.sub_apply, hG_def]
      ring
    rw [harmonicAt_congr_nhds hev]
    exact h1.sub h2
  have hsubMinus : SubharmonicOn (fun z => -G z) (U \ {w}) := hharmMinus.subharmonicOn hPO
  have hbdP : ∀ ζ ∈ frontier (U \ {w}), ∀ ε > 0, ∀ᶠ z in 𝓝[U \ {w}] ζ, -G z ≤ 0 + ε := by
    intro ζ hζ ε hε
    rcases mem_frontier_or_eq_of_mem_frontier_diff_singleton hU hζ with hζU | hζw
    · have h1 : Tendsto G (𝓝[U \ {w}] ζ) (𝓝 0) :=
        (hGvanish ζ hζU).mono_left (nhdsWithin_mono ζ sdiff_subset)
      have h2 := Metric.tendsto_nhds.mp h1 ε hε
      filter_upwards [h2] with z hz
      rw [Real.dist_eq, sub_zero] at hz
      have := abs_lt.mp hz
      linarith [this.1]
    · rw [hζw]
      have hcont : ContinuousAt h w := (hharm w hw).1.continuousAt
      have h1 : ∀ᶠ z in 𝓝 w, h z > h w - 1 := hcont.eventually (lt_mem_nhds (by linarith))
      have hcontnorm : Continuous (fun z : ℂ => ‖z - w‖) := by fun_prop
      have h2 : Tendsto (fun z : ℂ => ‖z - w‖) (𝓝[U \ {w}] w) (𝓝[>] (0 : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · simpa using (hcontnorm.tendsto w).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with z hz
          exact norm_pos_iff.mpr (sub_ne_zero.mpr hz.2)
      have h3 : Tendsto (fun z : ℂ => Real.log ‖z - w‖) (𝓝[U \ {w}] w) atBot :=
        Real.tendsto_log_nhdsGT_zero.comp h2
      have h4 : ∀ᶠ z in 𝓝[U \ {w}] w, Real.log ‖z - w‖ < -ε + h w - 1 :=
        h3.eventually (eventually_lt_atBot _)
      filter_upwards [h4, h1.filter_mono nhdsWithin_le_nhds] with z hz4 hz1
      rw [hG_def]
      simp only
      linarith
  have hmax := hsubMinus.le_of_frontier hPO hPb hbdP
  have hz₀mem : z₀ ∈ U \ {w} := ⟨hz₀U, hz₀w⟩
  have := hmax z₀ hz₀mem
  linarith

end Complex

end
