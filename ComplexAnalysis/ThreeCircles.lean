/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Perron

/-!
# Hadamard's three-circle theorem

For `f` holomorphic and nonvanishing on a punctured disc `0 < ‖z‖ < R`, the maximum modulus
`M(r) = max_{‖z‖=r} ‖f z‖` satisfies `M(r) ≤ M(r₁) ^ t * M(r₂) ^ (1 - t)` for `r₁ ≤ r ≤ r₂ < R`
and `t = (log r₂ - log r) / (log r₂ - log r₁)`, i.e. `log M(r)` is a convex function of `log r`.

The proof compares the harmonic function `φ z = log ‖f z‖ - a log ‖z‖`, for `a` chosen so that
the affine boundary values match on the two circles `‖z‖ = r₁` and `‖z‖ = r₂`, to the constant
`C` they share there, using the maximum principle for subharmonic functions on the bounded open
annulus `r₁ < ‖z‖ < r₂` (`SubharmonicOn.le_of_frontier` from `Perron.lean`). No branch of
`log f` needs to exist globally on the (not simply connected) annulus, since only `log ‖f‖`,
not `log f` itself, is used.

## Main results

* `Complex.norm_le_rpow_mul_rpow_of_nonvanishing`: **Hadamard's three-circle theorem**.

## References

* B. Simon, *Basic Complex Analysis*, Section 5.2.
* R. Remmert, *Theory of Complex Functions*, Chapter 9, Section 3.4.
-/

public noncomputable section

open Set Metric Filter InnerProductSpace
open scoped Topology

namespace Complex

variable {f : ℂ → ℂ} {R : ℝ}

/-- A point of the frontier of the open annulus `r₁ < ‖z‖ < r₂` lies on one of the two
bounding circles. -/
theorem mem_sphere_or_sphere_of_mem_frontier_annulus {r₁ r₂ : ℝ} {ζ : ℂ}
    (hζ : ζ ∈ frontier (ball (0 : ℂ) r₂ \ closedBall 0 r₁)) :
    ‖ζ‖ = r₁ ∨ ‖ζ‖ = r₂ := by
  set A : Set ℂ := ball (0 : ℂ) r₂ \ closedBall 0 r₁ with hA_def
  have hAopen : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hζcl : ζ ∈ closure A := frontier_subset_closure hζ
  have hζnA : ζ ∉ A := by rw [hAopen.frontier_eq] at hζ; exact hζ.2
  have h1 : r₁ ≤ ‖ζ‖ := by
    have hsub : A ⊆ {z : ℂ | r₁ ≤ ‖z‖} := fun z hz =>
      not_lt.mp fun h => hz.2 (mem_closedBall_zero_iff.mpr h.le)
    exact closure_minimal hsub (isClosed_le continuous_const continuous_norm) hζcl
  have h2 : ‖ζ‖ ≤ r₂ := by
    have hsub : A ⊆ {z : ℂ | ‖z‖ ≤ r₂} := fun z hz => (mem_ball_zero_iff.mp hz.1).le
    exact closure_minimal hsub (isClosed_le continuous_norm continuous_const) hζcl
  rcases eq_or_lt_of_le h1 with h1' | h1'
  · exact Or.inl h1'.symm
  · rcases eq_or_lt_of_le h2 with h2' | h2'
    · exact Or.inr h2'
    · exact absurd (⟨mem_ball_zero_iff.mpr h2', fun h => (not_lt.mpr
        (mem_closedBall_zero_iff.mp h)) h1'⟩ : ζ ∈ A) hζnA

/-- **Hadamard's three-circle theorem.** For `f` holomorphic and nonvanishing on the punctured
disc `0 < ‖z‖ < R`, the maximum modulus on the circle of radius `r` is bounded by the weighted
geometric mean of the maximum moduli on the circles of radii `r₁ ≤ r ≤ r₂ < R`. -/
theorem norm_le_rpow_mul_rpow_of_nonvanishing (hf : DifferentiableOn ℂ f (ball 0 R \ {0}))
    (hfne : ∀ z ∈ ball (0 : ℂ) R \ {0}, f z ≠ 0)
    {r₁ r₂ r : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ < R) (hrr₁ : r₁ ≤ r) (hrr₂ : r ≤ r₂)
    {M₁ M₂ : ℝ} (hM₁pos : 0 < M₁) (hM₂pos : 0 < M₂)
    (hM₁ : ∀ z ∈ sphere (0 : ℂ) r₁, ‖f z‖ ≤ M₁) (hM₂ : ∀ z ∈ sphere (0 : ℂ) r₂, ‖f z‖ ≤ M₂) :
    ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤
      M₁ ^ ((Real.log r₂ - Real.log r) / (Real.log r₂ - Real.log r₁)) *
        M₂ ^ ((Real.log r - Real.log r₁) / (Real.log r₂ - Real.log r₁)) := by
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have hlogr₁₂ : Real.log r₁ < Real.log r₂ := Real.log_lt_log hr₁ hr₁₂
  have hlogne : Real.log r₂ - Real.log r₁ ≠ 0 := by linarith
  set a : ℝ := (Real.log M₂ - Real.log M₁) / (Real.log r₂ - Real.log r₁) with ha_def
  set C : ℝ := Real.log M₁ - a * Real.log r₁ with hC_def
  have hCeq2 : C = Real.log M₂ - a * Real.log r₂ := by rw [hC_def, ha_def]; field_simp; ring
  -- membership of a frontier point of the annulus in the punctured disc `ball 0 R \ {0}`
  have hζmem : ∀ ζ : ℂ, ζ ∈ frontier (ball (0 : ℂ) r₂ \ closedBall 0 r₁) →
      ζ ∈ ball (0 : ℂ) R \ {0} := by
    intro ζ hζ
    rcases mem_sphere_or_sphere_of_mem_frontier_annulus hζ with h | h
    · refine ⟨mem_ball_zero_iff.mpr ?_, fun h0 => ?_⟩
      · rw [h]; linarith
      · rw [h0, norm_zero] at h; exact absurd h.symm hr₁.ne'
    · refine ⟨mem_ball_zero_iff.mpr ?_, fun h0 => ?_⟩
      · rw [h]; exact hr₂R
      · rw [h0, norm_zero] at h; exact absurd h.symm hr₂.ne'
  -- `φ` is harmonic on the punctured disc
  set φ : ℂ → ℝ := fun z => Real.log ‖f z‖ - a * Real.log ‖z‖ with hφ_def
  have hU : IsOpen (ball (0 : ℂ) R \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hφharm : HarmonicOnNhd φ (ball 0 R \ {0}) := by
    intro z hz
    have h1 : HarmonicAt (Real.log ‖f ·‖) z :=
      (hf.analyticOnNhd hU z hz).harmonicAt_log_norm (hfne z hz)
    have h2 : HarmonicAt (Real.log ‖(id : ℂ → ℂ) ·‖) z :=
      analyticAt_id.harmonicAt_log_norm hz.2
    have hfun_eq : (a • fun x : ℂ => Real.log ‖(id : ℂ → ℂ) x‖) =
        fun w : ℂ => a * Real.log ‖(id : ℂ → ℂ) w‖ := by
      funext w; simp [smul_eq_mul]
    have h2' : HarmonicAt (fun w => a * Real.log ‖(id : ℂ → ℂ) w‖) z :=
      hfun_eq ▸ h2.const_smul (c := a)
    exact h1.sub h2'
  have hφsub : SubharmonicOn φ (ball 0 R \ {0}) := hφharm.subharmonicOn hU
  -- the open annulus and its boundedness
  set A : Set ℂ := ball (0 : ℂ) r₂ \ closedBall 0 r₁ with hA_def
  have hAopen : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAb : Bornology.IsBounded A := isBounded_ball.subset Set.sdiff_subset
  have hAU : A ⊆ ball 0 R \ {0} := by
    intro z hz
    refine ⟨mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hz.1).trans hr₂R), fun h0 => ?_⟩
    exact hz.2 (h0 ▸ mem_closedBall_self hr₁.le)
  have hφsubA : SubharmonicOn φ A := hφsub.mono hAU
  -- the boundary bound `φ ≤ C` on both circles
  have hbdval : ∀ ζ ∈ frontier A, φ ζ ≤ C := by
    intro ζ hζ
    have hζU : ζ ∈ ball 0 R \ {0} := hζmem ζ hζ
    rcases mem_sphere_or_sphere_of_mem_frontier_annulus hζ with h | h
    · have hfζpos : 0 < ‖f ζ‖ := norm_pos_iff.mpr (hfne ζ hζU)
      have hle : Real.log ‖f ζ‖ ≤ Real.log M₁ :=
        Real.log_le_log hfζpos (hM₁ ζ (mem_sphere_zero_iff_norm.mpr h))
      rw [hφ_def, hC_def]
      simp only [h]
      linarith
    · have hfζpos : 0 < ‖f ζ‖ := norm_pos_iff.mpr (hfne ζ hζU)
      have hle : Real.log ‖f ζ‖ ≤ Real.log M₂ :=
        Real.log_le_log hfζpos (hM₂ ζ (mem_sphere_zero_iff_norm.mpr h))
      rw [hφ_def, hCeq2]
      simp only [h]
      linarith
  have hbd : ∀ ζ ∈ frontier A, ∀ ε > 0, ∀ᶠ z in 𝓝[A] ζ, φ z ≤ C + ε := by
    intro ζ hζ ε hε
    have hval := hbdval ζ hζ
    have hζU : ζ ∈ ball 0 R \ {0} := hζmem ζ hζ
    have hcont : ContinuousAt φ ζ := (hφharm ζ hζU).1.continuousAt
    filter_upwards [nhdsWithin_le_nhds
      (hcont.eventually (gt_mem_nhds (show φ ζ < C + ε by linarith)))] with z hz
    linarith
  -- apply the maximum principle
  have hmax := hφsubA.le_of_frontier hAopen hAb hbd
  intro z hz
  rcases hrr₁.eq_or_lt with heq1 | hlt1
  · rw [← heq1]
    have hzr1 : z ∈ sphere (0 : ℂ) r₁ := heq1 ▸ hz
    have ht1 : (Real.log r₂ - Real.log r₁) / (Real.log r₂ - Real.log r₁) = 1 := div_self hlogne
    have ht0 : (Real.log r₁ - Real.log r₁) / (Real.log r₂ - Real.log r₁) = 0 := by simp
    rw [ht1, ht0, Real.rpow_one, Real.rpow_zero, mul_one]
    exact hM₁ z hzr1
  rcases hrr₂.eq_or_lt with heq2 | hlt2
  · rw [heq2]
    have hzr2 : z ∈ sphere (0 : ℂ) r₂ := heq2 ▸ hz
    have ht1 : (Real.log r₂ - Real.log r₂) / (Real.log r₂ - Real.log r₁) = 0 := by simp
    have ht0 : (Real.log r₂ - Real.log r₁) / (Real.log r₂ - Real.log r₁) = 1 := div_self hlogne
    rw [ht1, ht0, Real.rpow_zero, Real.rpow_one, one_mul]
    exact hM₂ z hzr2
  -- the strict interior of the annulus
  have hzr : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
  have hzA : z ∈ A := ⟨mem_ball_zero_iff.mpr (by rw [hzr]; exact hlt2),
    fun h => by rw [mem_closedBall_zero_iff, hzr] at h; linarith⟩
  have hzU : z ∈ ball 0 R \ {0} := hAU hzA
  have hfzpos : 0 < ‖f z‖ := norm_pos_iff.mpr (hfne z hzU)
  have hφz : φ z ≤ C := hmax z hzA
  simp only [hφ_def] at hφz
  rw [hzr] at hφz
  have hlogfz : Real.log ‖f z‖ ≤ Real.log M₁ + a * (Real.log r - Real.log r₁) := by
    rw [hC_def] at hφz; linarith
  -- exponentiate and rewrite in terms of `t = (log r₂ - log r) / (log r₂ - log r₁)`
  have hexp : ‖f z‖ ≤ Real.exp (Real.log M₁ + a * (Real.log r - Real.log r₁)) := by
    rw [← Real.exp_log hfzpos]; exact Real.exp_le_exp.mpr hlogfz
  refine hexp.trans_eq ?_
  rw [Real.rpow_def_of_pos hM₁pos, Real.rpow_def_of_pos hM₂pos, ← Real.exp_add]
  congr 1
  rw [ha_def]
  field_simp
  ring

end Complex

end
