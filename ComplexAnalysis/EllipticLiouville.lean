/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.Complex.Liouville

/-!
# Liouville's first theorem for elliptic functions

**Liouville's first theorem**: an entire function doubly periodic with respect to a lattice
(a `PeriodPair`) is constant.

The proof shows such a function is bounded on all of `ℂ`: it is bounded on the compact closed
fundamental parallelogram spanned by the two periods (continuity and compactness), and every
point of `ℂ` is congruent modulo the lattice to a point of that parallelogram (writing `z` in
the `ℝ`-basis of `ℂ` given by the periods and subtracting integer multiples of the periods to
bring the coordinates into `[0, 1)`). The classical Liouville theorem for bounded entire
functions (`Complex.liouville_theorem_aux`) then gives constancy.

## Main results

* `Complex.elliptic_bounded_of_periodic`: a continuous doubly periodic function on `ℂ` is
  bounded.
* `Complex.elliptic_constant_of_entire`: **Liouville's first theorem**, a doubly periodic
  entire function is constant.

## References

* E. M. Stein and R. Shakarchi, *Complex Analysis*, Chapter 9, Theorem 1.1.
* R. Remmert, *Theory of Complex Functions*, Chapter 9, Section 1.
-/

public noncomputable section

open Set Filter

namespace Complex

/-- A continuous function on `ℂ`, periodic with respect to both periods of a `PeriodPair`, is
bounded. -/
theorem elliptic_bounded_of_periodic {L : PeriodPair} {f : ℂ → ℂ} (hf : Continuous f)
    (hper1 : Function.Periodic f L.ω₁) (hper2 : Function.Periodic f L.ω₂) :
    Bornology.IsBounded (Set.range f) := by
  set P : Set ℂ := (fun p : ℝ × ℝ => p.1 • L.ω₁ + p.2 • L.ω₂) '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    with hP_def
  have hPcompact : IsCompact P := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨M, hM⟩ := hPcompact.exists_bound_of_continuousOn hf.continuousOn
  rw [isBounded_iff_forall_norm_le]
  refine ⟨M, ?_⟩
  rintro _ ⟨z, rfl⟩
  set x : ℝ := L.basis.repr z 0 with hx_def
  set y : ℝ := L.basis.repr z 1 with hy_def
  set t1 : ℤ := ⌊x⌋ with ht1_def
  set t2 : ℤ := ⌊y⌋ with ht2_def
  have hz : z = x • L.ω₁ + y • L.ω₂ := by
    have hrepr := L.basis.sum_repr z
    rw [Fin.sum_univ_two] at hrepr
    simpa [PeriodPair.basis_zero, PeriodPair.basis_one] using hrepr.symm
  have heq : f z = f ((x - t1) • L.ω₁ + (y - t2) • L.ω₂) := by
    have hstep1 : f (z - (t2 : ℤ) • L.ω₂) = f z := hper2.sub_zsmul_eq t2
    have hstep2 : f (z - (t2 : ℤ) • L.ω₂ - (t1 : ℤ) • L.ω₁) = f (z - (t2 : ℤ) • L.ω₂) :=
      hper1.sub_zsmul_eq t1
    rw [← hstep1, ← hstep2]
    congr 1
    rw [hz]
    module
  rw [heq]
  refine hM _ ⟨⟨x - t1, y - t2⟩,
    ⟨⟨sub_nonneg.mpr (Int.floor_le x), by linarith [Int.lt_floor_add_one x]⟩,
      ⟨sub_nonneg.mpr (Int.floor_le y), by linarith [Int.lt_floor_add_one y]⟩⟩, rfl⟩

/-- **Liouville's first theorem for elliptic functions.** An entire function doubly periodic
with respect to a lattice is constant. -/
theorem elliptic_constant_of_entire {L : PeriodPair} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hper1 : Function.Periodic f L.ω₁) (hper2 : Function.Periodic f L.ω₂) :
    ∃ c, ∀ z, f z = c :=
  ⟨f 0, fun z => liouville_theorem_aux hf
    (elliptic_bounded_of_periodic hf.continuous hper1 hper2) z 0⟩

end Complex

end
