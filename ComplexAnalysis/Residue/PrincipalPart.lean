/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Residue
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Order.Filter.Finite

/-!
# Finite principal parts of meromorphic germs

A meromorphic germ is the sum of a finite principal part and an analytic germ, on a
punctured neighborhood. The construction repeatedly divides by the coordinate difference
and uses analytic divided slopes. Finite principal parts have normalized circle integral
equal to their residue on any enclosing circle.

## Main results

* `Complex.analyticAt_principalPart`: A finite principal part is analytic away from its center.
* `MeromorphicAt.exists_principalPart`: A meromorphic germ splits into a finite principal part
  and an analytic remainder. The equality is on a punctured neighborhood, so the assigned center
  value is immaterial.
* `Complex.residue_finset_sum`: Residues commute with a finite sum of isolated holomorphic
  germs.
* `Complex.two_pi_I_inv_smul_circleIntegral_sub_zpow_smul_const`: A constant higher-pole kernel
  has normalized circle integral equal to its residue when its pole is inside the circle.
* `Complex.two_pi_I_inv_smul_circleIntegral_principalPart`: The normalized integral of a finite
  principal part over an enclosing circle is its residue.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A finite principal part at `c`, with coefficients ordered from exponent `-1` downward. -/
@[expose] def principalPart {n : ℕ} (c : ℂ) (a : Fin n → F) (z : ℂ) : F :=
  ∑ i, (z - c) ^ (-(i.val + 1 : ℤ)) • a i

omit [CompleteSpace F] in
/-- A finite principal part is analytic away from its center. -/
theorem analyticAt_principalPart {n : ℕ} {c z : ℂ} (a : Fin n → F) (hz : z ≠ c) :
    AnalyticAt ℂ (principalPart c a) z :=
  Finset.analyticAt_fun_sum _ (fun _ _ ↦
    ((analyticAt_id.sub analyticAt_const).zpow (sub_ne_zero.mpr hz)).smul analyticAt_const)

omit [CompleteSpace F] in
/-- A finite principal part is meromorphic at every point. -/
theorem meromorphicAt_principalPart {n : ℕ} (c : ℂ) (a : Fin n → F) (z : ℂ) :
    MeromorphicAt (principalPart c a) z :=
  MeromorphicAt.fun_sum (fun _ _ ↦
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow _).smul
      analyticAt_const.meromorphicAt)

/-- An analytic germ has an analytic divided slope at its center. -/
theorem _root_.AnalyticAt.dslope {f : ℂ → F} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    AnalyticAt ℂ (dslope f c) c := by
  obtain ⟨r, hr, ha⟩ := hf.exists_ball_analyticOnNhd
  exact ((differentiableOn_dslope (ball_mem_nhds c hr)).mpr ha.differentiableOn).analyticAt
    (ball_mem_nhds c hr)

/-- A meromorphic germ splits into a finite principal part and an analytic remainder.
The equality is on a punctured neighborhood, so the assigned center value is immaterial. -/
theorem _root_.MeromorphicAt.exists_principalPart {f : ℂ → F} {c : ℂ}
    (hf : MeromorphicAt f c) :
    ∃ (n : ℕ) (a : Fin n → F) (g : ℂ → F), AnalyticAt ℂ g c ∧
      f =ᶠ[𝓝[≠] c] (fun z ↦ principalPart c a z + g z) := by
  obtain ⟨m, hm⟩ := hf
  induction m generalizing f with
  | zero =>
      refine ⟨0, Fin.elim0, f, ?_, ?_⟩
      · simpa using hm
      · exact Filter.Eventually.of_forall (fun z ↦ by simp [principalPart])
  | succ m ih =>
      have hg : AnalyticAt ℂ (fun z ↦ (z - c) ^ m • ((z - c) • f z)) c := by
        simpa only [smul_smul, ← pow_succ] using hm
      obtain ⟨n, a, g, hga, he⟩ := ih hg
      refine ⟨n + 1, Fin.cons (g c) a, dslope g c, hga.dslope, ?_⟩
      filter_upwards [he, self_mem_nhdsWithin] with z hz hzc
      have hne : z - c ≠ 0 := sub_ne_zero.mpr hzc
      have hsum : (z - c)⁻¹ • principalPart c a z =
          ∑ i : Fin n, (z - c) ^ (-((i.val + 1 : ℕ) + 1 : ℤ)) • a i := by
        rw [principalPart, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul, ← zpow_neg_one, ← zpow_add₀ hne]
        congr 2
        omega
      have he' : f z = (z - c)⁻¹ • principalPart c a z + (z - c)⁻¹ • g z := by
        rw [← smul_add, ← hz, inv_smul_smul₀ hne]
      rw [he', hsum, principalPart, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ,
        Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_add, zpow_neg_one]
      have hds : (z - c)⁻¹ • g z = (z - c)⁻¹ • g c + dslope g c z := by
        rw [dslope_of_ne g hzc, slope_def_module, smul_sub]
        abel
      rw [hds]
      abel

omit [CompleteSpace F] in
/-- Residues commute with a finite sum of isolated holomorphic germs. -/
theorem residue_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → F} {c : ℂ}
    (hf : ∀ i ∈ s, ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ (f i) z) :
    residue (fun z ↦ ∑ i ∈ s, f i z) c = ∑ i ∈ s, residue (f i) c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      apply residue_eq_of_eventually_eq
      filter_upwards with r
      simp [circleIntegral]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have hrest : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ (fun z ↦ ∑ j ∈ s, f j z) z := by
        filter_upwards [(Filter.eventually_all_finset _).mpr (fun j hj ↦
          hf j (Finset.mem_insert_of_mem hj))] with z hz
        exact Finset.analyticAt_fun_sum _ hz
      rw [residue_add (hf i (Finset.mem_insert_self i s)) hrest,
        ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))]

/-- A constant higher-pole kernel has normalized circle integral equal to its residue
when its pole is inside the circle. -/
theorem two_pi_I_inv_smul_circleIntegral_sub_zpow_smul_const
    {c w : ℂ} {R : ℝ} (hR : 0 < R) (hw : w ∈ ball c R) (n : ℕ) (v : F) :
    (2 * Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, R), (z - w) ^ (-(n + 1 : ℤ)) • v) =
      residue (fun z ↦ (z - w) ^ (-(n + 1 : ℤ)) • v) w := by
  rw [residue_sub_zpow_smul analyticAt_const]
  rw [(differentiableOn_const v).diffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_smul
    hR n hw, smul_smul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]

/-- The normalized integral of a finite principal part over an enclosing circle is its residue. -/
theorem two_pi_I_inv_smul_circleIntegral_principalPart {n : ℕ} {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hw : w ∈ ball c R) (a : Fin n → F) :
    (2 * Real.pi * I : ℂ)⁻¹ • (∮ z in C(c, R), principalPart w a z) =
      residue (principalPart w a) w := by
  have hint (i : Fin n) : CircleIntegrable
      (fun z ↦ (z - w) ^ (-(i.val + 1 : ℤ)) • a i) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply ContinuousOn.smul _ continuousOn_const
    apply (continuousOn_id.sub continuousOn_const).zpow₀
    intro z hz
    refine Or.inl (sub_ne_zero.mpr fun (he : z = w) ↦ (ne_of_lt (mem_ball.mp hw)) ?_)
    rw [← he]
    simpa [Complex.dist_eq] using hz
  unfold principalPart
  rw [residue_finset_sum _ (fun i _ ↦ ?_),
    circleIntegral.integral_fun_sum (fun i _ ↦ hint i), Finset.smul_sum]
  · exact Finset.sum_congr rfl (fun i _ ↦
      two_pi_I_inv_smul_circleIntegral_sub_zpow_smul_const hR hw i.val (a i))
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact ((analyticAt_id.sub analyticAt_const).zpow (sub_ne_zero.mpr hz)).smul analyticAt_const

end Complex
