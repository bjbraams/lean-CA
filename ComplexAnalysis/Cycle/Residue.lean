/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Cycle.Cauchy
public import ComplexAnalysis.Residue.LogDeriv
public import ComplexAnalysis.Integral.CirclePath

/-!
# The residue theorem for cycles

For a `C¹` cycle `Γ` in an open set `U` whose index vanishes outside `U`, and a Banach-valued
function holomorphic on `U` minus a finite set `S` of isolated singularities avoided by the
cycle, the integral of the function over the cycle is `2πi` times the sum over `S` of the index
times the residue. The singularities may be essential: only holomorphy on punctured
neighborhoods is used, through the circle-integral characterization of the residue.

The proof is by induction on the finite set of singularities. A singularity `a` is removed by
subtracting `index a` copies of a small circle around it; the new cycle is homologous to zero
in `U \ {a}`, and the circle contributes the residue.

## Main results

* `Complex.Cycle.integral_eq_sum_index_smul_residue`: the residue theorem for cycles.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Theorem V.2.2.
-/

public noncomputable section

open Set MeasureTheory Metric Filter ContinuousLinearMap
open scoped unitInterval Topology

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace Cycle

variable (Γ : Cycle)

/-- **The residue theorem for cycles.** For a `C¹` cycle in an open set `U` whose index
vanishes outside `U`, avoiding a finite set `S` of isolated singularities of a Banach-valued
function holomorphic on `U \ S`, the integral over the cycle is `2πi` times the sum of the
indices times the residues.

Related rectangular simple-pole formulas are formalized in PNT+ and in Mathlib PR #39232 (source
author Jeremy Tan). See `CREDITS.md`. -/
theorem integral_eq_sum_index_smul_residue {U : Set ℂ} (hU : IsOpen U) (S : Finset ℂ)
    (hΓ : Γ.IsC1) (hΓU : Γ.range ⊆ U \ S) (hind : ∀ w, w ∉ U → Γ.index w = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f (U \ S)) :
    Γ.integral (fun w => toSpanSingleton ℂ (f w)) =
      ∑ a ∈ S, (2 * (Real.pi : ℂ) * Complex.I * Γ.index a) • residue f a := by
  classical
  induction S using Finset.induction_on generalizing U Γ with
  | empty =>
    simp only [Finset.coe_empty, Set.sdiff_empty] at hΓU hf
    rw [Finset.sum_empty]
    exact Γ.integral_eq_zero hU hΓ hΓU hind hf
  | insert a S ha ih =>
    have hSclosed : IsClosed (S : Set ℂ) := (Finset.finite_toSet S).isClosed
    by_cases haU : a ∈ U
    · have hset : (U \ {a}) \ (S : Set ℂ) = U \ ((insert a S : Finset ℂ) : Set ℂ) := by
        rw [Finset.coe_insert, Set.sdiff_sdiff, Set.insert_eq]
      have hU' : IsOpen (U \ {a}) := hU.sdiff isClosed_singleton
      have haΓ : a ∉ Γ.range := fun h =>
        (hΓU h).2 (Finset.mem_coe.mpr (Finset.mem_insert_self a S))
      have haS : a ∉ (S : Set ℂ) := fun h => ha (Finset.mem_coe.mp h)
      obtain ⟨n, hn⟩ := Γ.exists_int_index hΓ haΓ
      have hV : IsOpen (U \ ((insert a S : Finset ℂ) : Set ℂ)) :=
        hU.sdiff (Finset.finite_toSet _).isClosed
      have hfa : ∀ᶠ z in 𝓝[≠] a, AnalyticAt ℂ f z := by
        have hmem : U \ (S : Set ℂ) ∈ 𝓝 a := (hU.sdiff hSclosed).mem_nhds ⟨haU, haS⟩
        filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with z hzUS hza
        have hzV : z ∈ U \ ((insert a S : Finset ℂ) : Set ℂ) := by
          refine ⟨hzUS.1, fun h => ?_⟩
          rcases Finset.mem_insert.mp (Finset.mem_coe.mp h) with h | h
          · exact hza (Set.mem_singleton_iff.mpr h)
          · exact hzUS.2 (Finset.mem_coe.mpr h)
        exact (hf.analyticOnNhd hV) z hzV
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
        (hU.inter (Γ.isOpen_compl_range.inter hSclosed.isOpen_compl)) a ⟨haU, haΓ, haS⟩
      obtain ⟨r, ⟨_, hres⟩, hr0, hrε⟩ :=
        ((eventually_circleIntegral_eq_residue hfa).and (Ioo_mem_nhdsGT hε)).exists
      have hcb : closedBall a r ⊆ U ∩ (Γ.rangeᶜ ∩ (S : Set ℂ)ᶜ) :=
        (closedBall_subset_ball hrε).trans hball
      set C : Loop := Loop.ofPath (Path.circle a r) with hC_def
      have hCrange : Set.range C.2 = sphere a r := by
        change Set.range (Path.circle a r) = sphere a r
        rw [Path.range_circle, abs_of_pos hr0]
      have hC1 : ContDiffOn ℝ 1 C.2.extend I := Path.contDiffOn_circle a r
      set Γ₁ := Γ.append (zsmulLoop (-n) C) with hΓ₁_def
      have hΓ₁ : Γ₁.IsC1 := append_isC1 hΓ (zsmulLoop_isC1 _ hC1)
      have hΓ₁U : Γ₁.range ⊆ (U \ {a}) \ (S : Set ℂ) := by
        rw [append_range, hset]
        refine union_subset hΓU ?_
        refine (zsmulLoop_range_subset _ _).trans ?_
        rw [hCrange]
        intro z hz
        have hz' := hcb (sphere_subset_closedBall hz)
        refine ⟨hz'.1, fun hmem => ?_⟩
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hmem) with h | h
        · exact hr0.ne (by simpa [h] using mem_sphere.mp hz)
        · exact hz'.2.2 (Finset.mem_coe.mpr h)
      have hΓ₁ind : ∀ w, w ∉ U \ {a} → Γ₁.index w = 0 := by
        intro w hw
        rw [append_index, zsmulLoop_index]
        by_cases hwU : w ∈ U
        · have hwa : w = a := by
            by_contra h
            exact hw ⟨hwU, h⟩
          rw [hwa, hn]
          change (n : ℂ) + (-n : ℤ) * curveIndex (Path.circle a r) a = 0
          rw [curveIndex_circle_of_mem_ball (mem_ball_self hr0)]
          push_cast
          ring
        · rw [hind w hwU]
          change (0 : ℂ) + (-n : ℤ) * curveIndex (Path.circle a r) w = 0
          rw [curveIndex_circle_of_notMem_closedBall hr0.le (fun h => hwU (hcb h).1)]
          ring
      have hf' : DifferentiableOn ℂ f ((U \ {a}) \ (S : Set ℂ)) := by rwa [hset]
      have hih := ih (U := U \ {a}) (Γ := Γ₁) hU' hΓ₁ hΓ₁U hΓ₁ind hf'
      have hidx : ∀ b ∈ S, Γ₁.index b = Γ.index b := by
        intro b hb
        rw [append_index, zsmulLoop_index]
        change Γ.index b + (-n : ℤ) * curveIndex (Path.circle a r) b = Γ.index b
        rw [curveIndex_circle_of_notMem_closedBall hr0.le
          (fun h => (hcb h).2.2 (Finset.mem_coe.mpr hb))]
        ring
      rw [append_integral, zsmulLoop_integral,
        Finset.sum_congr rfl (fun b hb => by rw [hidx b hb])] at hih
      have hcirc : curveIntegral (fun w => toSpanSingleton ℂ (f w)) C.2 =
          (2 * Real.pi * Complex.I : ℂ) • residue f a := by
        change curveIntegral _ (Path.circle a r) = _
        rw [curveIntegral_circle, ← hres, smul_smul, mul_inv_cancel₀ two_pi_I_ne_zero,
          one_smul]
      rw [hcirc] at hih
      have hcast : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) • residue f a =
          n • ((2 * Real.pi * Complex.I : ℂ) • residue f a) := by
        rw [mul_comm, mul_smul, Int.cast_smul_eq_zsmul]
      rw [Finset.sum_insert ha, hn, hcast, ← hih, neg_zsmul]
      abel
    · have hset : U \ ((insert a S : Finset ℂ) : Set ℂ) = U \ (S : Set ℂ) := by
        rw [Finset.coe_insert, Set.insert_eq, ← Set.sdiff_sdiff, Set.sdiff_singleton_eq_self haU]
      rw [hset] at hΓU hf
      rw [Finset.sum_insert ha, hind a haU, mul_zero, zero_smul, zero_add]
      exact ih Γ hU hΓ hΓU hind hf

end Cycle

end Complex

end
