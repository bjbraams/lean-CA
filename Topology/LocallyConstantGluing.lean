/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Gluing functions with locally constant differences

On a simply connected, locally path connected space, functions on an open cover whose
pairwise differences are locally constant admit a global function with the same local
increments. The values form an arbitrary additive commutative group; no topology on
that group is assumed. The proof equips the group with the discrete topology and uses
the covering bundle defined by the differences as transition functions.

## Main results

* `exists_locally_eq_add_of_locally_constant_sub`: Functions whose differences are locally
  constant on overlaps glue, up to local additive constants, on a simply connected space. The
  global function can have any prescribed value at a chosen base point.

## References

* `Mathlib.Topology.Homotopy.Lifting`: formal background used by this module.
* `Mathlib.Topology.FiberBundle.Basic`: formal background used by this module.
-/

open Set Filter Bundle
open scoped Topology

public noncomputable section

/-- Functions whose differences are locally constant on overlaps glue, up to local additive
constants, on a simply connected space. The global function can have any prescribed value
at a chosen base point.

Related covering-space constructions appear in Vincent Beffara's Curvint and Junyan Xu's Mathlib
PR #26950. See `CREDITS.md`. -/
theorem exists_locally_eq_add_of_locally_constant_sub
    {X A ι : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] [AddCommGroup A]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (p : ι → X → A)
    (hp : ∀ i j x, x ∈ U i ∩ U j →
      ∀ᶠ y in 𝓝 x, p i y - p j y = p i x - p j x)
    (x₀ : X) (a₀ : A) :
    ∃ P : X → A, P x₀ = a₀ ∧ ∀ i x, x ∈ U i →
      ∀ᶠ y in 𝓝 x, P y = P x + (p i y - p i x) := by
  classical
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let Z : FiberBundleCore ι X A :=
    { baseSet := U
      isOpen_baseSet := hU
      indexAt := fun x => (hcover x).choose
      mem_baseSet_at := fun x => (hcover x).choose_spec
      coordChange := fun i j x v => v + (p i x - p j x)
      coordChange_self := by intros; simp
      continuousOn_coordChange := by
        intro i j q hq
        apply ContinuousAt.continuousWithinAt
        apply (continuousAt_const (y := q.2 + (p i q.1 - p j q.1))).congr
        have he := continuous_fst.continuousAt.eventually (hp i j q.1 hq.1)
        have hv : ∀ᶠ r : X × A in 𝓝 q, r.2 = q.2 :=
          continuous_snd.continuousAt.eventually ((isOpen_discrete {q.2}).mem_nhds rfl)
        filter_upwards [he, hv] with r hr hv
        simp only [hv, hr]
      coordChange_comp := by intros; abel }
  have hcov : IsCoveringMap Z.proj := FiberBundle.isCoveringMap (F := A)
  let e₀ : Z.TotalSpace := ⟨x₀, a₀ - p (Z.indexAt x₀) x₀⟩
  obtain ⟨s, ⟨hs₀, hs⟩, _⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x₀ e₀ rfl
  have hsx (x : X) : (s x).proj = x := congrFun hs x
  let v : X → A := fun x => (s x).2
  let P : X → A := fun x => v x + p (Z.indexAt x) x
  have hlocal (i : ι) (x : X) :
      P x = ((Z.localTriv i) (s x)).2 + p i x := by
    change v x + p (Z.indexAt x) x =
      (v x + (p (Z.indexAt (s x).proj) (s x).proj - p i (s x).proj)) + p i x
    rw [hsx]
    abel
  refine ⟨P, ?_, ?_⟩
  · change v x₀ + p (Z.indexAt x₀) x₀ = a₀
    dsimp only [v]
    rw [hs₀]
    exact sub_add_cancel _ _
  · intro i x hx
    have hmem : s x ∈ (Z.localTriv i).source := by
      apply (Z.localTriv i).mem_source.mpr
      change (s x).proj ∈ U i
      rwa [hsx]
    have hc : ContinuousAt (fun y => ((Z.localTriv i) (s y)).2) x :=
      ((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hmem).snd.comp s.continuous.continuousAt
    have he : ∀ᶠ y in 𝓝 x, ((Z.localTriv i) (s y)).2 = ((Z.localTriv i) (s x)).2 :=
      hc.eventually ((isOpen_discrete {((Z.localTriv i) (s x)).2}).mem_nhds rfl)
    filter_upwards [he] with y hy
    rw [hlocal i y, hlocal i x, hy]
    abel
