/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Gluing functions with locally constant quotients or differences

Group-valued functions on an open cover whose quotients are locally constant on overlaps
admit a unique normalized global function with locally constant quotients by the local
functions. Existence uses simple connectedness and local path connectedness; uniqueness
only needs preconnectedness. No topology on the value group is required.

The additive version is `existsUnique_isLocallyConstant_sub`. Neither group is required
to be commutative. The `_on` versions accept functions defined only on individual cover
members. The original local-increment formulation for commutative additive groups is retained
as a corollary.

The proof uses the covering bundle defined by the quotients as transition functions.
Related covering-space constructions occur in Vincent Beffara's
[Curvint](https://github.com/vbeffara/Curvint) and Junyan Xu's
[Mathlib PR #26950](https://github.com/leanprover-community/mathlib4/pull/26950).
-/

public noncomputable section

open Set Filter Bundle
open scoped Topology

/-- On an open subset, local constancy of the restriction is equivalent to eventual
constancy in the ambient neighborhoods of its points. -/
theorem IsOpen.isLocallyConstant_domRestrict_iff {X A : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) {f : X → A} :
    IsLocallyConstant (U.domRestrict f) ↔ ∀ x ∈ U, ∀ᶠ y in 𝓝 x, f y = f x := by
  rw [IsLocallyConstant.iff_eventually_eq]
  constructor
  · intro h x hx
    rw [← hU.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, hx⟩]
    exact h ⟨x, hx⟩
  · intro h x
    exact continuous_subtype_val.continuousAt.eventually (h x x.property)

/-- On a preconnected space, functions with locally constant quotients by the same local
functions agree everywhere if they agree at one point. -/
@[to_additive /-- On a preconnected space, functions with locally constant differences from
the same local functions agree everywhere if they agree at one point. -/]
theorem eq_of_isLocallyConstant_div_on_cover
    {X A ι : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Group A]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (p : ι → X → A) {P Q : X → A}
    (hP : ∀ i, IsLocallyConstant (fun x : U i ↦ P x / p i x))
    (hQ : ∀ i, IsLocallyConstant (fun x : U i ↦ Q x / p i x))
    {x₀ : X} (h₀ : P x₀ = Q x₀) : P = Q := by
  have hloc : IsLocallyConstant (fun x ↦ P x / Q x) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    obtain ⟨i, hi⟩ := hcover x
    have hp := ((hU i).isLocallyConstant_domRestrict_iff (f := fun x ↦ P x / p i x)).mp (hP i) x hi
    have hq := ((hU i).isLocallyConstant_domRestrict_iff (f := fun x ↦ Q x / p i x)).mp (hQ i) x hi
    filter_upwards [hp, hq] with y hyP hyQ
    calc
      P y / Q y = (P y / p i y) / (Q y / p i y) := by
        simp [div_eq_mul_inv, mul_assoc]
      _ = (P x / p i x) / (Q x / p i x) := by rw [hyP, hyQ]
      _ = P x / Q x := by simp [div_eq_mul_inv, mul_assoc]
  funext x
  have he := hloc.apply_eq_of_preconnectedSpace x x₀
  simpa only [h₀, div_self', div_eq_one] using he

/-- Functions with locally constant quotients on overlaps of an open cover of a simply
connected, locally path connected space have a unique normalized global representative. -/
@[to_additive /-- Functions with locally constant differences on overlaps of an open cover of
a simply connected, locally path connected space have a unique normalized global representative. -/]
theorem existsUnique_isLocallyConstant_div
    {X A ι : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] [Group A]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (p : ι → X → A)
    (hp : ∀ i j, IsLocallyConstant (fun x : ↥(U i ∩ U j) ↦ p i x / p j x))
    (x₀ : X) (a₀ : A) :
    ∃! P : X → A, P x₀ = a₀ ∧ ∀ i, IsLocallyConstant (fun x : U i ↦ P x / p i x) := by
  classical
  have hp' (i j : ι) (x : X) (hx : x ∈ U i ∩ U j) :
      ∀ᶠ y in 𝓝 x, p i y / p j y = p i x / p j x :=
    (((hU i).inter (hU j)).isLocallyConstant_domRestrict_iff
      (f := fun x ↦ p i x / p j x)).mp (hp i j) x hx
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let Z : FiberBundleCore ι X A :=
    { baseSet := U
      isOpen_baseSet := hU
      indexAt := fun x ↦ (hcover x).choose
      mem_baseSet_at := fun x ↦ (hcover x).choose_spec
      coordChange := fun i j x v ↦ v * (p i x / p j x)
      coordChange_self := by intros; simp
      continuousOn_coordChange := by
        intro i j q hq
        apply ContinuousAt.continuousWithinAt
        apply (continuousAt_const (y := q.2 * (p i q.1 / p j q.1))).congr
        have he := continuous_fst.continuousAt.eventually (hp' i j q.1 hq.1)
        have hv : ∀ᶠ r : X × A in 𝓝 q, r.2 = q.2 :=
          continuous_snd.continuousAt.eventually ((isOpen_discrete {q.2}).mem_nhds rfl)
        filter_upwards [he, hv] with r hr hv
        simp only [hv, hr]
      coordChange_comp := by intros; simp [div_eq_mul_inv, mul_assoc] }
  have hcov : IsCoveringMap Z.proj := FiberBundle.isCoveringMap (F := A)
  let e₀ : Z.TotalSpace := ⟨x₀, a₀ / p (Z.indexAt x₀) x₀⟩
  obtain ⟨s, ⟨hs₀, hs⟩, _⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x₀ e₀ rfl
  have hsx (x : X) : (s x).proj = x := congrFun hs x
  let v : X → A := fun x ↦ (s x).2
  let P : X → A := fun x ↦ v x * p (Z.indexAt x) x
  have hlocal (i : ι) (x : X) : P x = ((Z.localTriv i) (s x)).2 * p i x := by
    change v x * p (Z.indexAt x) x =
      (v x * (p (Z.indexAt (s x).proj) (s x).proj / p i (s x).proj)) * p i x
    rw [hsx]
    simp [div_eq_mul_inv, mul_assoc]
  have hP₀ : P x₀ = a₀ := by
    change v x₀ * p (Z.indexAt x₀) x₀ = a₀
    dsimp only [v]
    rw [hs₀]
    exact div_mul_cancel _ _
  have hP (i : ι) : IsLocallyConstant (fun x : U i ↦ P x / p i x) := by
    apply ((hU i).isLocallyConstant_domRestrict_iff (f := fun x ↦ P x / p i x)).mpr
    intro x hx
    have hmem : s x ∈ (Z.localTriv i).source := by
      apply (Z.localTriv i).mem_source.mpr
      change (s x).proj ∈ U i
      rwa [hsx]
    have hc : ContinuousAt (fun y ↦ ((Z.localTriv i) (s y)).2) x :=
      ((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hmem).snd.comp s.continuous.continuousAt
    have he : ∀ᶠ y in 𝓝 x, ((Z.localTriv i) (s y)).2 = ((Z.localTriv i) (s x)).2 :=
      hc.eventually ((isOpen_discrete {((Z.localTriv i) (s x)).2}).mem_nhds rfl)
    filter_upwards [he] with y hy
    simp only [hlocal i y, hlocal i x, mul_div_cancel_right, hy]
  refine ⟨P, ⟨hP₀, hP⟩, ?_⟩
  intro Q hQ
  exact eq_of_isLocallyConstant_div_on_cover U hU hcover p hQ.2 hP (hQ.1.trans hP₀.symm)

/-- Local functions defined only on the cover members glue uniquely, after normalization,
when their quotients on overlaps are locally constant. -/
@[to_additive /-- Local functions defined only on the cover members glue uniquely, after
normalization, when their differences on overlaps are locally constant. -/]
theorem existsUnique_isLocallyConstant_div_on
    {X A ι : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] [Group A]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (p : ∀ i, U i → A)
    (hp : ∀ i j, IsLocallyConstant (fun x : ↥(U i ∩ U j) ↦
      p i ⟨x, x.property.1⟩ / p j ⟨x, x.property.2⟩)) (x₀ : X) (a₀ : A) :
    ∃! P : X → A, P x₀ = a₀ ∧ ∀ i, IsLocallyConstant (fun x : U i ↦ P x / p i x) := by
  classical
  let q (i : ι) (x : X) : A := if hx : x ∈ U i then p i ⟨x, hx⟩ else 1
  have hq (i : ι) (x : U i) : q i x = p i x := dite_eq_left x.property
  have hquot (i j : ι) : IsLocallyConstant (fun x : ↥(U i ∩ U j) ↦ q i x / q j x) := by
    convert hp i j using 1
    funext x
    simp only [q, dite_eq_left x.property.1, dite_eq_left x.property.2]
  simpa only [hq] using existsUnique_isLocallyConstant_div U hU hcover q hquot x₀ a₀

/-- Functions with locally constant differences on overlaps glue with prescribed local
increments and any prescribed value at a base point. -/
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
  obtain ⟨P, ⟨hP₀, hP⟩, _⟩ := existsUnique_isLocallyConstant_sub U hU hcover p
    (fun i j ↦ ((hU i).inter (hU j)).isLocallyConstant_domRestrict_iff.mpr (hp i j)) x₀ a₀
  refine ⟨P, hP₀, fun i x hx ↦ ?_⟩
  filter_upwards [((hU i).isLocallyConstant_domRestrict_iff
    (f := fun x ↦ P x - p i x)).mp (hP i) x hx] with y hy
  calc
    P y = (P y - p i y) + p i y := (sub_add_cancel _ _).symm
    _ = (P x - p i x) + p i y := by rw [hy]
    _ = P x + (p i y - p i x) := by abel

end
