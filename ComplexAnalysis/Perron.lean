/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.HarmonicLimit

/-!
# Perron's method

For a bounded open set `U` and bounded boundary data `g` on its frontier, the Perron family
consists of the continuous subharmonic functions `v` on `U` whose upper limit at every boundary
point `ζ` is at most `g ζ`. The Perron function is the pointwise supremum of the family.
**Perron's theorem** states that it is harmonic on `U`.

The ingredients are the maximum principle on bounded open sets in upper-limit form, the
Poisson modification of a continuous subharmonic function on a closed disc inside `U` (which
stays in the family, increases the function, and is harmonic on the disc), and Harnack's
principle for the monotone sequences of modifications.

## Main definitions

* `Complex.IsPerronMember U g v`, `Complex.perronFunction U g`.

## Main results

* `Complex.SubharmonicOn.le_of_frontier`: the maximum principle on bounded open sets.
* `Complex.subharmonicOn_poissonExtension`, `Complex.IsPerronMember.poissonExtension`: the
  Poisson modification.
* `Complex.harmonicOnNhd_perronFunction`: **Perron's theorem**.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Section X.4 (Theorem 4.9?) and
  *Volume II*, Section 19.7.
* T. W. Gamelin, *Complex Analysis*, Section XV.4.
* L. V. Ahlfors, *Complex Analysis*, Section 6.4.
-/

@[expose] public noncomputable section

open Set Metric Filter Function InnerProductSpace Real
open scoped Topology

namespace Complex

/-! ### The maximum principle on bounded open sets -/

/-- If `v` is subharmonic on the bounded open set `U`, with upper limits at most `M` at the
boundary, and `v` exceeds `M` somewhere in `U`, then `v` attains its maximum over `U` at a point
of `U`: extended by `M` on the frontier, `v` is upper semicontinuous on the compact closure. -/
private theorem SubharmonicOn.exists_isMaxOn_of_frontier {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {v : ℂ → ℝ} (hv : SubharmonicOn v U) {M : ℝ}
    (hbd : ∀ ζ ∈ frontier U, ∀ ε > 0, ∀ᶠ z in 𝓝[U] ζ, v z ≤ M + ε) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hz₀v : M < v z₀) : ∃ z₁ ∈ U, ∀ z ∈ U, v z ≤ v z₁ := by
  classical
  have hclos : closure U = U ∪ frontier U := closure_eq_self_union_frontier U
  have hfrU : ∀ ζ ∈ frontier U, ζ ∉ U := fun ζ hζ ↦ by
    rw [hU.frontier_eq] at hζ
    exact hζ.2
  -- the extension by `M` to the boundary
  set w : ℂ → ℝ := fun z ↦ if z ∈ U then v z else M
  have hwU : ∀ z ∈ U, w z = v z := fun z hz ↦ by simp [w, hz]
  have hwF : ∀ z ∈ frontier U, w z = M := fun z hz ↦ by simp [w, hfrU z hz]
  have hcomp : IsCompact (closure U) := hUb.isCompact_closure
  have husc : UpperSemicontinuousOn w (closure U) := by
    intro z hz y hy
    rw [hclos] at hz
    rcases hz with hzU | hzF
    · rw [hwU z hzU] at hy
      have h1 := hv.1 z hzU y hy
      rw [hU.nhdsWithin_eq hzU] at h1
      refine eventually_nhdsWithin_of_eventually_nhds ?_
      filter_upwards [h1, hU.mem_nhds hzU] with z' h1' hz'U
      rwa [hwU z' hz'U]
    · rw [hwF z hzF] at hy
      rw [hclos, nhdsWithin_union]
      refine eventually_sup.mpr ⟨?_, ?_⟩
      · filter_upwards [hbd z hzF ((y - M) / 2) (by linarith), self_mem_nhdsWithin]
          with z' hz' hz'U
        rw [hwU z' hz'U]
        linarith
      · filter_upwards [self_mem_nhdsWithin] with z' hz'
        rw [hwF z' hz']
        linarith
  obtain ⟨z₁, hz₁, hmax⟩ := husc.exists_isMaxOn ⟨z₀, subset_closure hz₀⟩ hcomp
  have hz₁U : z₁ ∈ U := by
    by_contra h
    have := hmax (subset_closure hz₀)
    simp only [mem_ofPred_eq, hwU z₀ hz₀, hwF z₁ ((hclos ▸ hz₁).resolve_left h)] at this
    linarith
  refine ⟨z₁, hz₁U, fun z hz ↦ ?_⟩
  have := hmax (subset_closure hz)
  simpa only [mem_ofPred_eq, hwU z hz, hwU z₁ hz₁U] using this

/-- **Maximum principle on bounded open sets.** If `v` is subharmonic on the bounded open set
`U` and its upper limit at every boundary point is at most `M`, then `v ≤ M` on `U`. -/
theorem SubharmonicOn.le_of_frontier {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {v : ℂ → ℝ} (hv : SubharmonicOn v U) {M : ℝ}
    (hbd : ∀ ζ ∈ frontier U, ∀ ε > 0, ∀ᶠ z in 𝓝[U] ζ, v z ≤ M + ε) : ∀ z ∈ U, v z ≤ M := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z₀, hz₀, hz₀v⟩ := hcon
  obtain ⟨z₁, hz₁U, hvle⟩ := hv.exists_isMaxOn_of_frontier hU hUb hbd hz₀ hz₀v
  set S : ℝ := v z₁
  have hSM : M < S := hz₀v.trans_le (hvle z₀ hz₀)
  -- the set where the maximum is attained is open and relatively closed
  set A : Set ℂ := {z | z ∈ U ∧ v z = S}
  have hAsub : A ⊆ U := fun z hz ↦ hz.1
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzU, hzS⟩
    filter_upwards [hv.eventually_eq_of_isMaxOn hU hzU fun y hy ↦ hzS ▸ hvle y hy,
      hU.mem_nhds hzU] with y hy hyU
    exact ⟨hyU, by rw [hy, hzS]⟩
  have hAcl : closure A ∩ U ⊆ A := by
    rintro z ⟨hzA, hzU⟩
    refine ⟨hzU, (hvle z hzU).eq_of_not_lt fun hlt ↦ ?_⟩
    have : (𝓝[A] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzA
    have h2 : ∀ᶠ y in 𝓝[A] z, v y < S := nhdsWithin_mono z hAsub (hv.1 z hzU S hlt)
    obtain ⟨y, hy, hyA⟩ := (h2.and self_mem_nhdsWithin).exists
    exact lt_irrefl _ (hyA.2 ▸ hy)
  -- the frontier of `A` is nonempty and lies in the frontier of `U`
  obtain ⟨ζ, hζ⟩ : (frontier A).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rcases isClopen_iff.mp (isClopen_iff_frontier_eq_empty.mpr h) with hA | hA
    · have hne : A.Nonempty := ⟨z₁, hz₁U, rfl⟩
      rw [hA] at hne
      exact Set.not_nonempty_empty hne
    · exact NormedSpace.unbounded_univ ℝ ℂ (hA ▸ hUb.subset hAsub)
  have hζcl : ζ ∈ closure A := frontier_subset_closure hζ
  have hζU : ζ ∉ U := fun h ↦ ((hAopen.frontier_eq ▸ hζ).2) (hAcl ⟨hζcl, h⟩)
  have hζF : ζ ∈ frontier U := by
    rw [hU.frontier_eq]
    exact ⟨closure_mono hAsub hζcl, hζU⟩
  have : (𝓝[A] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hζcl
  have h2 : ∀ᶠ y in 𝓝[A] ζ, v y ≤ M + (S - M) / 2 :=
    nhdsWithin_mono ζ hAsub (hbd ζ hζF ((S - M) / 2) (by linarith))
  obtain ⟨y, hy, hyA⟩ := (h2.and self_mem_nhdsWithin).exists
  rw [hyA.2] at hy
  linarith

/-! ### The Poisson modification -/

variable {U : Set ℂ} {c : ℂ} {R : ℝ} {v : ℂ → ℝ}

/-- The Poisson modification dominates the function. -/
theorem le_poissonExtension (hR : 0 < R) (hcl : closedBall c R ⊆ U) (hv : SubharmonicOn v U)
    (hvc : ContinuousOn v U) : ∀ z ∈ U, v z ≤ poissonExtension c R v z := by
  intro z hz
  by_cases hzb : z ∈ ball c R
  · have hP := harmonicContOnCl_poissonExtension hR (hvc.mono (sphere_subset_closedBall.trans hcl))
    have hd : SubharmonicOn (fun w ↦ v w + (-poissonExtension c R v) w) (ball c R) :=
      (hv.mono (ball_subset_closedBall.trans hcl)).add
        (hP.harmonicOnNhd.neg.subharmonicOn isOpen_ball)
    have husc : UpperSemicontinuousOn (fun w ↦ v w + (-poissonExtension c R v) w)
        (closedBall c R) :=
      ((hvc.mono hcl).add hP.continuousOn_ball.neg).upperSemicontinuousOn
    have hsph : ∀ w ∈ sphere c R, v w + (-poissonExtension c R v) w ≤ 0 := fun w hw ↦ by
      simp only [Pi.neg_apply, poissonExtension_of_notMem (sphere_notMem_ball hw)]
      linarith
    have := hd.le_of_le_sphere hR husc hsph z (ball_subset_closedBall hzb)
    simp only [Pi.neg_apply] at this
    linarith
  · rw [poissonExtension_of_notMem hzb]

/-- The Poisson modification of a continuous subharmonic function is subharmonic. -/
theorem subharmonicOn_poissonExtension (hR : 0 < R) (hU : IsOpen U) (hcl : closedBall c R ⊆ U)
    (hv : SubharmonicOn v U) (hvc : ContinuousOn v U) :
    SubharmonicOn (poissonExtension c R v) U := by
  have hPc : ContinuousOn (poissonExtension c R v) U := continuousOn_poissonExtension hR hcl hvc
  refine ⟨hPc.upperSemicontinuousOn, fun a ha ↦ ?_⟩
  have hge := le_poissonExtension hR hcl hv hvc
  by_cases hab : a ∈ ball c R
  · exact ((harmonicOnNhd_poissonExtension hR (hvc.mono
      (sphere_subset_closedBall.trans hcl))).subharmonicOn isOpen_ball).hasSubmeanAt hab
  · obtain ⟨ρ, hρ, hsub⟩ := (hv.hasSubmeanAt ha).exists_forall_lt
    obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.mp hU a ha
    refine hasSubmeanAt_of_forall_lt (lt_min hρ hρ') fun r hr hrρ ↦ ?_
    have hsph : sphere a r ⊆ U := fun w hw ↦ hball (by
      rw [mem_ball, mem_sphere.mp hw]
      exact hrρ.trans_le (min_le_right _ _))
    have hPint : CircleIntegrable (poissonExtension c R v) a r :=
      (hPc.mono hsph).circleIntegrable hr.le
    obtain ⟨hvint, hvavg⟩ := hsub r hr (hrρ.trans_le (min_le_left _ _))
    refine ⟨hPint, ?_⟩
    rw [poissonExtension_of_notMem hab]
    refine hvavg.trans (circleAverage_mono hvint hPint fun w hw ↦ ?_)
    rw [abs_of_pos hr] at hw
    exact hge w (hsph hw)

/-! ### The Perron family -/

/-- Membership in the Perron family for the boundary data `g` on the open set `U`: continuous
subharmonic functions on `U` whose upper limit at every boundary point `ζ` is at most `g ζ`. -/
structure IsPerronMember (U : Set ℂ) (g : ℂ → ℝ) (v : ℂ → ℝ) : Prop where
  /-- Subharmonic on `U`. -/
  subharmonicOn : SubharmonicOn v U
  /-- Continuous on `U`. -/
  continuousOn : ContinuousOn v U
  /-- The upper limit at each boundary point is at most the boundary value. -/
  boundary : ∀ ζ ∈ frontier U, ∀ ε > 0, ∀ᶠ z in 𝓝[U] ζ, v z ≤ g ζ + ε

/-- The Perron function: the pointwise supremum of the Perron family. -/
def perronFunction (U : Set ℂ) (g : ℂ → ℝ) (z : ℂ) : ℝ :=
  ⨆ v : {v : ℂ → ℝ // IsPerronMember U g v}, v.1 z

variable {g : ℂ → ℝ}

/-- A constant bounded above by the boundary data belongs to the Perron family. -/
theorem isPerronMember_const {m : ℝ} (hm : ∀ ζ ∈ frontier U, m ≤ g ζ) :
    IsPerronMember U g fun _ ↦ m :=
  ⟨subharmonicOn_const m U, continuousOn_const, fun ζ hζ ε hε ↦
    Eventually.of_forall fun _ ↦ by linarith [hm ζ hζ]⟩

/-- The pointwise maximum of two members of the Perron family is again a member. -/
theorem IsPerronMember.sup {v₁ v₂ : ℂ → ℝ} (h₁ : IsPerronMember U g v₁)
    (h₂ : IsPerronMember U g v₂) : IsPerronMember U g fun z ↦ max (v₁ z) (v₂ z) :=
  ⟨h₁.subharmonicOn.sup h₂.subharmonicOn, ContinuousOn.sup h₁.continuousOn h₂.continuousOn,
    fun ζ hζ ε hε ↦ by
      filter_upwards [h₁.boundary ζ hζ ε hε, h₂.boundary ζ hζ ε hε] with z hz₁ hz₂
      exact max_le hz₁ hz₂⟩

/-- Members of the Perron family are bounded by any bound for the boundary data. -/
theorem IsPerronMember.le (hU : IsOpen U) (hUb : Bornology.IsBounded U) {M : ℝ}
    (hgM : ∀ ζ ∈ frontier U, g ζ ≤ M) (hv : IsPerronMember U g v) : ∀ z ∈ U, v z ≤ M :=
  hv.subharmonicOn.le_of_frontier hU hUb fun ζ hζ ε hε ↦ by
    filter_upwards [hv.boundary ζ hζ ε hε] with z hz
    linarith [hgM ζ hζ]

/-- The Poisson modification of a member on a closed disc inside `U` is a member. -/
theorem IsPerronMember.poissonExtension (hU : IsOpen U) (hR : 0 < R) (hcl : closedBall c R ⊆ U)
    (hv : IsPerronMember U g v) : IsPerronMember U g (poissonExtension c R v) := by
  refine ⟨subharmonicOn_poissonExtension hR hU hcl hv.subharmonicOn hv.continuousOn,
    continuousOn_poissonExtension hR hcl hv.continuousOn, fun ζ hζ ε hε ↦ ?_⟩
  have hζU : ζ ∉ U := by
    rw [hU.frontier_eq] at hζ
    exact hζ.2
  have hζc : ζ ∉ closedBall c R := fun h ↦ hζU (hcl h)
  have hev : ∀ᶠ z in 𝓝[U] ζ, z ∉ ball c R :=
    nhdsWithin_le_nhds (by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hζc] with z hz
      exact fun h ↦ hz (ball_subset_closedBall h))
  filter_upwards [hv.boundary ζ hζ ε hε, hev] with z hz hzb
  rw [poissonExtension_of_notMem hzb]
  exact hz

/-- On a bounded open domain with boundary data bounded above, the values of the Perron family are
bounded above at every interior point. -/
theorem bddAbove_range_perron (hU : IsOpen U) (hUb : Bornology.IsBounded U) {M : ℝ}
    (hgM : ∀ ζ ∈ frontier U, g ζ ≤ M) {z : ℂ} (hz : z ∈ U) :
    BddAbove (range fun v : {v : ℂ → ℝ // IsPerronMember U g v} ↦ v.1 z) :=
  ⟨M, by
    rintro _ ⟨v, rfl⟩
    exact v.2.le hU hUb hgM z hz⟩

/-- On a bounded open domain with boundary data bounded above, each Perron-family member lies below
the Perron function. -/
theorem IsPerronMember.le_perronFunction (hU : IsOpen U) (hUb : Bornology.IsBounded U) {M : ℝ}
    (hgM : ∀ ζ ∈ frontier U, g ζ ≤ M) (hv : IsPerronMember U g v) {z : ℂ} (hz : z ∈ U) :
    v z ≤ perronFunction U g z :=
  le_ciSup (bddAbove_range_perron hU hUb hgM hz) ⟨v, hv⟩

/-- For boundary data bounded above and below on a bounded open domain, the Perron function is
bounded above by the same upper bound. -/
theorem perronFunction_le (hU : IsOpen U) (hUb : Bornology.IsBounded U) {M : ℝ}
    (hgM : ∀ ζ ∈ frontier U, g ζ ≤ M) {m : ℝ} (hm : ∀ ζ ∈ frontier U, m ≤ g ζ) {z : ℂ}
    (hz : z ∈ U) : perronFunction U g z ≤ M := by
  have : Nonempty {v : ℂ → ℝ // IsPerronMember U g v} := ⟨⟨_, isPerronMember_const hm⟩⟩
  exact ciSup_le fun v ↦ v.2.le hU hUb hgM z hz

/-- A sequence of members whose values at a point tend to the Perron function. -/
theorem exists_seq_isPerronMember_tendsto (hU : IsOpen U) (hUb : Bornology.IsBounded U) {M : ℝ}
    (hgM : ∀ ζ ∈ frontier U, g ζ ≤ M) {m : ℝ} (hm : ∀ ζ ∈ frontier U, m ≤ g ζ) {z : ℂ}
    (hz : z ∈ U) : ∃ v : ℕ → ℂ → ℝ, (∀ n, IsPerronMember U g (v n)) ∧
      Tendsto (fun n ↦ v n z) atTop (𝓝 (perronFunction U g z)) := by
  have hne : (range fun v : {v : ℂ → ℝ // IsPerronMember U g v} ↦ v.1 z).Nonempty :=
    ⟨_, ⟨⟨_, isPerronMember_const hm⟩, rfl⟩⟩
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hne (bddAbove_range_perron hU hUb hgM hz)
  have huS' : ∀ n, ∃ v : {v : ℂ → ℝ // IsPerronMember U g v}, v.1 z = u n := fun n ↦ huS n
  choose v hvu using huS'
  refine ⟨fun n ↦ (v n).1, fun n ↦ (v n).2, ?_⟩
  simp only [hvu]
  exact hu

/-- The running maximum of a sequence of functions. -/
def runningMax (v : ℕ → ℂ → ℝ) : ℕ → ℂ → ℝ
  | 0 => v 0
  | n + 1 => fun z ↦ max (runningMax v n z) (v (n + 1) z)

/-- Each term of a sequence is bounded above by its running maximum. -/
theorem le_runningMax (v : ℕ → ℂ → ℝ) (n : ℕ) (z : ℂ) : v n z ≤ runningMax v n z := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

/-- The running maximum of a sequence of functions is pointwise monotone in its index. -/
theorem runningMax_mono (v : ℕ → ℂ → ℝ) (z : ℂ) : Monotone fun n ↦ runningMax v n z :=
  monotone_nat_of_le_succ fun _ ↦ le_max_left _ _

/-- A pointwise upper bound for every term is also an upper bound for each running maximum. -/
theorem runningMax_le {v : ℕ → ℂ → ℝ} {u : ℂ → ℝ} {z : ℂ} (h : ∀ n, v n z ≤ u z) (n : ℕ) :
    runningMax v n z ≤ u z := by
  induction n with
  | zero => exact h 0
  | succ n ih => exact max_le ih (h (n + 1))

/-- Every running maximum of a sequence of Perron-family members remains in the Perron family. -/
theorem IsPerronMember.runningMax {v : ℕ → ℂ → ℝ} (hv : ∀ n, IsPerronMember U g (v n)) (n : ℕ) :
    IsPerronMember U g (runningMax v n) := by
  induction n with
  | zero => exact hv 0
  | succ n ih => exact ih.sup (hv (n + 1))

/-- A harmonic member equals its own Poisson modification on the disc. -/
theorem poissonExtension_eq_of_harmonicOnNhd (hR : 0 < R) (hcl : closedBall c R ⊆ U)
    (hvc : ContinuousOn v U) (hvh : HarmonicOnNhd v (ball c R)) :
    ∀ z ∈ ball c R, poissonExtension c R v z = v z := by
  have hvs : ContinuousOn v (sphere c R) := hvc.mono (sphere_subset_closedBall.trans hcl)
  have h1 : HarmonicContOnCl (poissonExtension c R v) (ball c R) :=
    harmonicContOnCl_poissonExtension hR hvs
  have h2 : HarmonicContOnCl v (ball c R) :=
    HarmonicContOnCl.mk_ball hvh (hvc.mono hcl)
  have heq : EqOn (poissonExtension c R v) v (sphere c R) := fun w hw ↦
    poissonExtension_of_notMem (sphere_notMem_ball hw)
  exact fun z hz ↦ eqOn_of_harmonicContOnCl_of_eqOn_sphere hR h1 h2 heq
    (ball_subset_closedBall hz)

/-- **Perron's theorem.** For a bounded open set and bounded boundary data, the Perron function
is harmonic. -/
theorem harmonicOnNhd_perronFunction (hU : IsOpen U) (hUb : Bornology.IsBounded U) {m M : ℝ}
    (hm : ∀ ζ ∈ frontier U, m ≤ g ζ) (hgM : ∀ ζ ∈ frontier U, g ζ ≤ M) :
    HarmonicOnNhd (perronFunction U g) U := by
  classical
  set u := perronFunction U g
  have hmem_le : ∀ {w : ℂ → ℝ}, IsPerronMember U g w → ∀ z ∈ U, w z ≤ u z :=
    fun hw z hz ↦ hw.le_perronFunction hU hUb hgM hz
  intro a ha
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU a ha
  set r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hcl : closedBall a r ⊆ U := (closedBall_subset_ball (half_lt_self hR)).trans hRU
  have hball : ball a r ⊆ U := ball_subset_closedBall.trans hcl
  have hconn : IsPreconnected (ball a r) := (convex_ball a r).isPreconnected
  -- the general step: from a sequence of members, a harmonic limit on the disc below `u`
  have hstep : ∀ v : ℕ → ℂ → ℝ, (∀ n, IsPerronMember U g (v n)) →
      ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball a r) ∧ (∀ z ∈ ball a r, h z ≤ u z) ∧
        (∀ n, ∀ z ∈ ball a r, v n z ≤ h z) ∧
        (∀ n, IsPerronMember U g (poissonExtension a r (runningMax v n))) ∧
        (∀ z ∈ ball a r, Tendsto (fun n ↦ poissonExtension a r (runningMax v n) z) atTop
          (𝓝 (h z))) := by
    intro v hv
    set w : ℕ → ℂ → ℝ := fun n ↦ poissonExtension a r (runningMax v n)
    have hwmem : ∀ n, IsPerronMember U g (w n) := fun n ↦
      (IsPerronMember.runningMax hv n).poissonExtension hU hr hcl
    have hwharm : ∀ n, HarmonicOnNhd (w n) (ball a r) := fun n ↦
      harmonicOnNhd_poissonExtension hr
        ((IsPerronMember.runningMax hv n).continuousOn.mono (sphere_subset_closedBall.trans hcl))
    have hwmono : ∀ z ∈ ball a r, Monotone fun n ↦ w n z := fun z hz ↦
      monotone_nat_of_le_succ fun n ↦ poissonExtension_mono hr hcl
        (IsPerronMember.runningMax hv n).continuousOn
        (IsPerronMember.runningMax hv (n + 1)).continuousOn
        (fun y _ ↦ runningMax_mono v y (Nat.le_succ n)) z (hball hz)
    have hwle : ∀ n, ∀ z ∈ U, w n z ≤ u z := fun n ↦ hmem_le (hwmem n)
    have hvw : ∀ n, ∀ z ∈ U, v n z ≤ w n z := fun n z hz ↦
      (le_runningMax v n z).trans (le_poissonExtension hr hcl
        (IsPerronMember.runningMax hv n).subharmonicOn
        (IsPerronMember.runningMax hv n).continuousOn z hz)
    have hbdd : BddAbove (range fun n ↦ w n a) :=
      ⟨u a, by rintro _ ⟨n, rfl⟩; exact hwle n a ha⟩
    obtain ⟨h, hh, hlim⟩ := exists_harmonicOnNhd_tendstoLocallyUniformlyOn_of_monotone isOpen_ball
      hconn hwharm hwmono (mem_ball_self hr) hbdd
    refine ⟨h, hh, fun z hz ↦ ?_, fun n z hz ↦ ?_, hwmem, fun z hz ↦ hlim.tendsto_at hz⟩
    · exact le_of_tendsto' (hlim.tendsto_at hz) fun n ↦ hwle n z (hball hz)
    · exact (hvw n z (hball hz)).trans (Monotone.ge_of_tendsto (hwmono z hz) (hlim.tendsto_at hz) n)
  -- first sequence: values at `a`
  obtain ⟨v, hv, hva⟩ := exists_seq_isPerronMember_tendsto hU hUb hgM hm ha
  obtain ⟨h, hh, hhu, hvh, hwmem, hwlim⟩ := hstep v hv
  have hha : h a = u a := by
    refine le_antisymm (hhu a (mem_ball_self hr)) ?_
    exact le_of_tendsto' hva fun n ↦ hvh n a (mem_ball_self hr)
  -- `h = u` on the disc
  have hhu' : ∀ z₁ ∈ ball a r, h z₁ = u z₁ := by
    intro z₁ hz₁
    refine le_antisymm (hhu z₁ hz₁) ?_
    obtain ⟨v', hv', hv'z⟩ := exists_seq_isPerronMember_tendsto hU hUb hgM hm (hball hz₁)
    set v'' : ℕ → ℂ → ℝ := fun n z ↦ max (v' n z) (poissonExtension a r (runningMax v n) z)
      with hv''_def
    have hv'' : ∀ n, IsPerronMember U g (v'' n) := fun n ↦ (hv' n).sup (hwmem n)
    obtain ⟨h', hh', hh'u, hv''h', -, -⟩ := hstep v'' hv''
    -- `h ≤ h'` on the disc
    have hhh' : ∀ z ∈ ball a r, h z ≤ h' z := fun z hz ↦
      le_of_tendsto' (hwlim z hz) fun n ↦
        (le_max_right _ _).trans (hv''h' n z hz)
    have hh'a : h' a = u a :=
      le_antisymm (hh'u a (mem_ball_self hr)) (hha ▸ hhh' a (mem_ball_self hr))
    -- the difference `h - h'` is subharmonic, nonpositive, and vanishes at `a`
    have hd : SubharmonicOn (fun z ↦ h z + (-h') z) (ball a r) :=
      (hh.subharmonicOn isOpen_ball).add (hh'.neg.subharmonicOn isOpen_ball)
    have hdmax : ∀ z ∈ ball a r, h z + (-h') z ≤ h a + (-h') a := fun z hz ↦ by
      simp only [Pi.neg_apply]
      linarith [hhh' z hz, hha, hh'a]
    have := hd.eqOn_const_of_isMaxOn isOpen_ball hconn (mem_ball_self hr) hdmax z₁ hz₁
    simp only [Pi.neg_apply] at this
    have hz₁eq : h z₁ = h' z₁ := by linarith [hha, hh'a]
    rw [hz₁eq]
    exact le_of_tendsto' hv'z fun n ↦ (le_max_left _ _).trans (hv''h' n z₁ hz₁)
  have hev : u =ᶠ[𝓝 a] h := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    exact (hhu' z hz).symm
  exact (harmonicAt_congr_nhds hev).mpr (hh a (mem_ball_self hr))

end Complex

end
