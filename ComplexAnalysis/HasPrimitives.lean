/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Calculus.MeanValue
public import Topology.LocallyConstantGluing

/-!
# Primitives on simply connected open domains

Local primitives glue on a simply connected open subset of the complex plane because their
pairwise differences are locally constant. Consequently, every holomorphic function with
values in a complex Banach space has a primitive on such a domain. We use Mathlib's
`Complex.IsExactOn`, and also give normalization and uniqueness statements.

## Main results

* `Complex.IsExactOn.of_isSimplyConnected`: Local primitives on disks glue to a primitive on a
  simply connected open domain. Completeness of the target is not needed once local primitives
  are given.
* `DifferentiableOn.isExactOn_of_isSimplyConnected`: A holomorphic Banach-valued function has a
  primitive on every simply connected open domain.
* `DifferentiableOn.exists_primitive_of_isSimplyConnected`: A holomorphic Banach-valued function
  has a primitive with any prescribed base-point value.
* `Complex.isExactOn_iff_differentiableOn_of_isSimplyConnected`: On a simply connected open
  domain, holomorphy is equivalent to having a primitive.
* `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected`: Morera's rectangle condition and
  continuity give a global primitive on a simply connected open domain. Rectangle conservativity
  alone does not supply global exactness on domains with holes.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

open Set Filter Metric
open scoped Topology

public noncomputable section

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {U : Set ℂ} {f : ℂ → F}

/-- Local primitives on disks glue to a primitive on a simply connected open domain.
Completeness of the target is not needed once local primitives are given.

Related primitive constructions: Vincent Beffara's Curvint and Junyan Xu's Mathlib PR #26950;
the latter's primitive API was unfinished at review. See `CREDITS.md`. -/
theorem IsExactOn.of_isSimplyConnected (hU : IsOpen U) (hUc : IsSimplyConnected U)
    (hf : ∀ z ∈ U, ∃ r > 0, IsExactOn f (ball z r)) : IsExactOn f U := by
  classical
  let := hUc.simplyConnectedSpace
  let := hU.locallyPathConnectedSpace
  choose r hr P hP using fun z : U => hf z z.property
  let V : U → Set U := fun z => (Subtype.val : U → ℂ) ⁻¹' ball z (r z)
  have hV : ∀ z, IsOpen (V z) := fun z => isOpen_ball.preimage continuous_subtype_val
  have hcover : ∀ z : U, ∃ i, z ∈ V i := fun z => ⟨z, mem_ball_self (hr z)⟩
  have hdiff : ∀ i j x : U, x ∈ V i ∩ V j →
      ∀ᶠ y : U in 𝓝 x, P i y - P j y = P i x - P j x := by
    intro i j x hx
    have hderiv : ∀ y ∈ ball (i : ℂ) (r i) ∩ ball (j : ℂ) (r j),
        HasDerivAt (fun w => P i w - P j w) 0 y := by
      intro y hy
      change HasDerivAt (P i - P j) 0 y
      simpa only [sub_self] using (hP i y hy.1).sub (hP j y hy.2)
    filter_upwards [((hV i).inter (hV j)).mem_nhds hx] with y hy
    exact (isOpen_ball.inter isOpen_ball).is_const_of_deriv_eq_zero
      ((convex_ball (i : ℂ) (r i)).inter (convex_ball (j : ℂ) (r j))).isPreconnected
      (fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hderiv w hw).deriv) hy hx
  obtain ⟨z₀, hz₀⟩ := hUc.nonempty
  obtain ⟨Q, _, hQ⟩ := exists_locally_eq_add_of_locally_constant_sub
    V hV hcover (fun i z => P i z) hdiff ⟨z₀, hz₀⟩ (0 : F)
  let R : ℂ → F := fun z => if hz : z ∈ U then Q ⟨z, hz⟩ else 0
  refine ⟨R, fun z hz => ?_⟩
  let x : U := ⟨z, hz⟩
  have hlocal := hQ x x (mem_ball_self (hr x))
  apply (((hP x z (mem_ball_self (hr x))).sub_const (P x z)).const_add (Q x)).congr_of_eventuallyEq
  rw [← hU.isOpenEmbedding_subtypeVal.map_nhds_eq x]
  change ∀ᶠ y : U in 𝓝 x, R y = Q x + (P x y - P x z)
  filter_upwards [hlocal] with y hy
  simpa only [R, dite_eq_left y.property] using hy

/-- Primitives are unique up to an additive constant on a connected open domain. -/
theorem IsExactOn.eq_add_const {P Q : ℂ → F} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hP : ∀ z ∈ U, HasDerivAt P (f z) z) (hQ : ∀ z ∈ U, HasDerivAt Q (f z) z) :
    ∃ c : F, EqOn P (fun z => Q z + c) U :=
  hU.exists_eq_add_of_deriv_eq hUc
    (fun z hz => (hP z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hQ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hP z hz).deriv.trans (hQ z hz).deriv.symm)

/-- Two primitives agreeing at one point agree throughout a connected open domain. -/
theorem IsExactOn.eqOn_of_eq {P Q : ℂ → F} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hP : ∀ z ∈ U, HasDerivAt P (f z) z) (hQ : ∀ z ∈ U, HasDerivAt Q (f z) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (heq : P z₀ = Q z₀) : EqOn P Q U :=
  hU.eqOn_of_deriv_eq hUc
    (fun z hz => (hP z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hQ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hP z hz).deriv.trans (hQ z hz).deriv.symm) hz₀ heq

end Complex

/-- A holomorphic Banach-valued function has a primitive on every simply connected open domain. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    (hU : IsOpen U) (hUc : IsSimplyConnected U) : Complex.IsExactOn f U := by
  apply Complex.IsExactOn.of_isSimplyConnected hU hUc
  intro z hz
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU z hz
  exact ⟨r, hr, (hf.mono hsub).isExactOn_ball⟩

/-- A holomorphic Banach-valued function has a primitive with any prescribed base-point value.

Related primitive constructions: Vincent Beffara's Curvint and Junyan Xu's Mathlib PR #26950;
the latter's primitive API was unfinished at review. See `CREDITS.md`. -/
theorem DifferentiableOn.exists_primitive_of_isSimplyConnected
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    (hU : IsOpen U) (hUc : IsSimplyConnected U) (z₀ : ℂ) (v : F) :
    ∃ P : ℂ → F, P z₀ = v ∧ ∀ z ∈ U, HasDerivAt P (f z) z :=
  (hf.isExactOn_of_isSimplyConnected hU hUc).with_val_at z₀ v

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {U : Set ℂ} {f : ℂ → F}

/-- On a simply connected open domain, holomorphy is equivalent to having a primitive. -/
theorem isExactOn_iff_differentiableOn_of_isSimplyConnected
    (hU : IsOpen U) (hUc : IsSimplyConnected U) :
    IsExactOn f U ↔ DifferentiableOn ℂ f U :=
  ⟨fun hf => hf.differentiableOn hU, fun hf => hf.isExactOn_of_isSimplyConnected hU hUc⟩

/-- Morera's rectangle condition and continuity give a global primitive on a simply connected
open domain. Rectangle conservativity alone does not supply global exactness on domains with holes.
-/
theorem IsConservativeOn.isExactOn_of_isSimplyConnected
    (hf : IsConservativeOn f U) (hc : ContinuousOn f U)
    (hU : IsOpen U) (hUc : IsSimplyConnected U) : IsExactOn f U :=
  ((isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp ⟨hf,
      hc⟩).isExactOn_of_isSimplyConnected
    hU hUc

end Complex
