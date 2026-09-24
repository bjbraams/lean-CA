/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Cycle.Residue
public import ComplexAnalysis.Integral.CirclePath

/-!
# The residue at infinity

The residue at infinity of `f` is `- residue (fun w => w⁻¹ ^ 2 • f w⁻¹) 0`. The change of
variables `z = w⁻¹` identifies the circle integral of `f` over `‖z‖ = R` with the circle
integral of `w⁻¹ ^ 2 • f w⁻¹` over `‖w‖ = R⁻¹`, so that for `f` holomorphic outside a disc the
integral over a large circle is `-2πi` times the residue at infinity. Combined with the residue
theorem for cycles this gives the **total residue theorem**: for a function holomorphic off a
finite set, the residues at the finite singularities and at infinity sum to zero.

## Main definitions

* `Complex.residueAtInfty f`.

## Main results

* `Complex.circleIntegral_eq_circleIntegral_inv`: the change of variables `z = w⁻¹`.
* `Complex.circleIntegral_eq_neg_residueAtInfty`: large circle integrals.
* `Complex.sum_residue_add_residueAtInfty`: the total residue theorem.

## References

* B. Simon, *Basic Complex Analysis*, Section 3.8 (residue at infinity).
* T. W. Gamelin, *Complex Analysis*, Section VII.3.
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open scoped Topology Real

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Inversion of a point of a circle around the origin. -/
theorem inv_circleMap_zero (R θ : ℝ) : (circleMap 0 R θ)⁻¹ = circleMap 0 R⁻¹ (-θ) := by
  simp only [circleMap, zero_add, mul_inv, ← exp_neg, ofReal_neg, neg_mul, ofReal_inv]

/-- **Change of variables `z = w⁻¹` in circle integrals.** -/
theorem circleIntegral_eq_circleIntegral_inv (f : ℂ → F) {R : ℝ} (hR : 0 < R) :
    (∮ z in C(0, R), f z) = ∮ w in C(0, R⁻¹), (w⁻¹) ^ 2 • f w⁻¹ := by
  set g : ℝ → F := fun θ => (circleMap 0 R θ * I) • f (circleMap 0 R θ) with hg_def
  have hint : ∀ φ : ℝ, deriv (circleMap 0 R⁻¹) φ •
      (((circleMap 0 R⁻¹ φ)⁻¹) ^ 2 • f (circleMap 0 R⁻¹ φ)⁻¹) = g (-φ) := by
    intro φ
    rw [deriv_circleMap, inv_circleMap_zero, inv_inv, smul_smul, hg_def]
    dsimp only
    congr 1
    have h1 : circleMap 0 R⁻¹ φ * circleMap 0 R (-φ) = 1 := by
      have h2 : circleMap 0 R (-φ) = (circleMap 0 R⁻¹ φ)⁻¹ := by
        rw [inv_circleMap_zero, inv_inv]
      rw [h2, mul_inv_cancel₀]
      exact circleMap_ne_center (inv_pos.mpr hR).ne'
    linear_combination (circleMap 0 R (-φ) * I) * h1
  have hper : Periodic g (2 * π) := fun θ => by
    simp only [hg_def, periodic_circleMap 0 R θ]
  rw [circleIntegral, circleIntegral]
  simp only [hint]
  rw [intervalIntegral.integral_comp_neg, neg_zero]
  have := hper.intervalIntegral_add_eq (-(2 * π)) 0
  simp only [neg_add_cancel, zero_add] at this
  rw [this]
  simp only [hg_def, deriv_circleMap]

/-- The residue at infinity, `- residue (fun w => w⁻¹ ^ 2 • f w⁻¹) 0`. -/
def residueAtInfty (f : ℂ → F) : F := -residue (fun w => (w⁻¹) ^ 2 • f w⁻¹) 0

/-- The integral over a large circle is `-2πi` times the residue at infinity. -/
theorem circleIntegral_eq_neg_residueAtInfty {f : ℂ → F} {R₀ R : ℝ} (hR₀ : 0 ≤ R₀) (hR : R₀ < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R₀)ᶜ) :
    (∮ z in C(0, R), f z) = -((2 * π * I : ℂ) • residueAtInfty f) := by
  have hRpos : 0 < R := lt_of_le_of_lt hR₀ hR
  rw [circleIntegral_eq_circleIntegral_inv f hRpos, residueAtInfty, smul_neg, neg_neg]
  have hg : AnalyticOnNhd ℂ (fun w => (w⁻¹) ^ 2 • f w⁻¹) (closedBall 0 R⁻¹ \ {0}) := by
    intro w hw
    have hw0 : w ≠ 0 := hw.2
    have hwinv : w⁻¹ ∈ (closedBall 0 R₀)ᶜ := by
      rw [mem_compl_iff, mem_closedBall_zero_iff, norm_inv, not_le]
      have hw1 : ‖w‖ ≤ R⁻¹ := mem_closedBall_zero_iff.mp hw.1
      have hw2 : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      exact hR.trans_le ((le_inv_comm₀ hRpos hw2).mpr hw1)
    have hinv : AnalyticAt ℂ (fun w : ℂ => w⁻¹) w := analyticAt_id.inv hw0
    exact (hinv.pow 2).smul ((hf _ hwinv).comp hinv)
  rw [residue_eq_circleIntegral (inv_pos.mpr hRpos) hg, smul_smul,
    mul_inv_cancel₀ two_pi_I_ne_zero, one_smul]

variable [CompleteSpace F]

/-- **The total residue theorem.** For a function holomorphic outside a finite set, the residues
at the finite singularities and the residue at infinity sum to zero. -/
theorem sum_residue_add_residueAtInfty {f : ℂ → F} (S : Finset ℂ)
    (hf : DifferentiableOn ℂ f (↑S : Set ℂ)ᶜ) :
    ∑ a ∈ S, residue f a + residueAtInfty f = 0 := by
  obtain ⟨R₀, hR₀⟩ := S.finite_toSet.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 0 + 1 with hR_def
  have hR0 : 0 ≤ max R₀ 0 := le_max_right _ _
  have hRpos : 0 < R := by positivity
  have hSR : ∀ a ∈ S, a ∈ ball 0 R := fun a ha => by
    have := mem_closedBall_zero_iff.mp (hR₀ (Finset.mem_coe.mpr ha))
    rw [mem_ball_zero_iff]
    linarith [le_max_left R₀ 0]
  have hopen : IsOpen (↑S : Set ℂ)ᶜ := S.finite_toSet.isClosed.isOpen_compl
  have hfan : AnalyticOnNhd ℂ f (↑S : Set ℂ)ᶜ := hf.analyticOnNhd hopen
  -- the cycle consisting of one large circle
  set γ : Loop := Loop.ofPath (Path.circle 0 R) with hγ_def
  set Γ : Cycle := Cycle.replicate 1 γ with hΓ_def
  have hΓ : Γ.IsC1 := Cycle.replicate_isC1 1 (Path.contDiffOn_circle 0 R)
  have hrange : Γ.range ⊆ sphere 0 R := by
    refine (Cycle.replicate_range_subset 1 γ).trans ?_
    rw [hγ_def]
    change Set.range (Path.circle 0 R) ⊆ sphere 0 R
    rw [Path.range_circle, abs_of_pos hRpos]
  have hΓU : Γ.range ⊆ univ \ (↑S : Set ℂ) := by
    intro z hz
    refine ⟨mem_univ z, fun hzS => ?_⟩
    have h1 := mem_sphere_zero_iff_norm.mp (hrange hz)
    have h2 := mem_ball_zero_iff.mp (hSR z (Finset.mem_coe.mp hzS))
    linarith
  have hres := Γ.integral_eq_sum_index_smul_residue isOpen_univ S hΓ hΓU
    (fun w hw => absurd (mem_univ w) hw) (by rw [← Set.compl_eq_univ_sdiff]; exact hf)
  have hleft : Γ.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) =
      ∮ z in C(0, R), f z := by
    rw [hΓ_def, Cycle.replicate_integral, one_smul, hγ_def]
    exact curveIntegral_circle f 0 R
  have hindex : ∀ a ∈ S, Γ.index a = 1 := fun a ha => by
    rw [hΓ_def, Cycle.replicate_index, hγ_def]
    change ((1 : ℕ) : ℂ) * curveIndex (Path.circle 0 R) a = 1
    rw [curveIndex_circle_of_mem_ball (hSR a ha), mul_one, Nat.cast_one]
  have hinfty : (∮ z in C(0, R), f z) = -((2 * π * I : ℂ) • residueAtInfty f) := by
    refine circleIntegral_eq_neg_residueAtInfty hR0 (by linarith) (hfan.mono ?_)
    intro z hz
    rw [mem_compl_iff, mem_closedBall_zero_iff, not_le] at hz
    intro hzS
    have := mem_closedBall_zero_iff.mp (hR₀ hzS)
    linarith [le_max_left R₀ 0]
  rw [hleft, hinfty, Finset.sum_congr rfl fun a ha => by rw [hindex a ha, mul_one],
    ← Finset.smul_sum] at hres
  have : (2 * π * I : ℂ) • (∑ a ∈ S, residue f a + residueAtInfty f) = 0 := by
    rw [smul_add, ← hres]
    simp
  exact (smul_eq_zero.mp this).resolve_left two_pi_I_ne_zero

end Complex

end
