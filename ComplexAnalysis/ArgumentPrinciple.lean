/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.Residue.LogDeriv
public import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# The argument principle on disks

The integral of a logarithmic derivative counts the divisor inside a circle. Mathlib's
finite divisor factorization separates the zeros and poles from a nonvanishing analytic
factor. The statement uses meromorphic orders and is insensitive to the assigned values
at isolated removable singularities.

## Main results

* `Complex.logDeriv_congr_codiscreteWithin_of_preperfect`: Logarithmic derivatives of
  meromorphic functions agreeing off a discrete subset of a preperfect set agree off a discrete
  subset of that set, including its boundary.
* `Complex.circleIntegral_logDeriv_eq_sum_divisor`: The argument principle for a meromorphic
  function on a closed disk. The boundary has order zero, and the function is nowhere the zero
  meromorphic germ. The sum is finite because a divisor has finite support on a compact set.
* `Complex.two_pi_I_inv_mul_circleIntegral_logDeriv`: The normalized argument-principle integral
  is the integer degree of the divisor.
* `Complex.two_pi_I_inv_mul_circleIntegral_logDeriv_of_analyticOnNhd`: The argument principle
  for a holomorphic function with no boundary zeros. The integer divisor degree counts interior
  zeros with their analytic multiplicities.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Set Filter Metric Function MeromorphicOn
open scoped Topology

namespace Complex

/-- Logarithmic derivatives of meromorphic functions agreeing off a discrete subset of a
preperfect set agree off a discrete subset of that set, including its boundary. -/
theorem logDeriv_congr_codiscreteWithin_of_preperfect {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : Preperfect U)
    (he : f =ᶠ[codiscreteWithin U] g) :
    logDeriv f =ᶠ[codiscreteWithin U] logDeriv g := by
  apply eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mpr
  intro z hz
  exact (logDeriv_congr_nhdsNE
    ((hf z hz).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (hg z hz) hz hU he)).mono (fun _ h _ ↦ h)

/-- The argument principle for a meromorphic function on a closed disk. The boundary has
order zero, and the function is nowhere the zero meromorphic germ. The sum is finite
because a divisor has finite support on a compact set. -/
theorem circleIntegral_logDeriv_eq_sum_divisor {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : MeromorphicOn f (closedBall c R))
    (hne : ∀ z ∈ closedBall c R, meromorphicOrderAt f z ≠ ⊤)
    (hb : ∀ z ∈ sphere c R, meromorphicOrderAt f z = 0) :
    (∮ z in C(c, R), logDeriv f z) =
      (2 * Real.pi * I) * ∑ᶠ z, (divisor f (closedBall c R) z : ℂ) := by
  let D := divisor f (closedBall c R)
  have hD : D.support.Finite := D.finiteSupport (isCompact_closedBall c R)
  let s := hD.toFinset
  let φ : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  have hφ : MeromorphicOn φ (closedBall c R) :=
    (FactorizedRational.meromorphicNFOn D _).meromorphicOn
  obtain ⟨g, hg, hgn, he⟩ := hf.extract_zeros_poles (fun z ↦ hne z z.property) hD
  have hfg : f =ᶠ[codiscreteWithin (closedBall c R)] (φ * g) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using he
  have hperfect : Preperfect (closedBall c R) := by
    simpa [closure_ball c hR.ne'] using (isOpen_ball (x := c) (ε := R)).perfect_closure.acc
  have hlog := logDeriv_congr_codiscreteWithin_of_preperfect hf
    (hφ.mul hg.meromorphicOn) hperfect hfg
  have hφne : ∀ z ∈ closedBall c R, meromorphicOrderAt φ z ≠ ⊤ :=
    fun z _ ↦ FactorizedRational.meromorphicOrderAt_ne_top D
  have hgne : ∀ z ∈ closedBall c R, meromorphicOrderAt g z ≠ ⊤ := by
    intro z hz
    rw [(hg z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hgn ⟨z, hz⟩)]
    exact WithTop.zero_ne_top
  have hprod := hφ.logDeriv_mul_eventuallyEq hg.meromorphicOn hφne hgne
  have hrat : logDeriv φ =ᶠ[codiscreteWithin (closedBall c R)]
      (fun z ↦ ∑ i ∈ s, (D i : ℂ) * (z - i)⁻¹) := by
    have heq := MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq
      (U := closedBall c R) (F := fun i : ℂ ↦ fun z ↦ z - i) hD
      (fun i z _ ↦ (analyticAt_id.sub analyticAt_const).meromorphicAt)
      (fun i z _ ↦ by
        rw [(show AnalyticAt ℂ (fun w : ℂ ↦ w - i) z by fun_prop).meromorphicOrderAt_eq]
        by_cases hi : z = i
        · subst z; simp
        · simp [analyticOrderAt_id_sub_const_of_ne hi])
    filter_upwards [heq] with z hz
    rw [hz, finsum_eq_sum_of_support_subset _ (s := s)]
    · apply Finset.sum_congr rfl
      intro i _
      simp [logDeriv_apply, zsmul_eq_mul]
    · intro i hi
      change i ∈ s
      apply hD.mem_toFinset.mpr
      intro hzero
      exact hi (by simp [hzero])
  have hinside : ∀ i ∈ s, i ∈ ball c R := by
    intro i hi
    have hiD : i ∈ D.support := hD.mem_toFinset.mp hi
    have hiK := D.supportWithinDomain hiD
    rcases lt_or_eq_of_le (mem_closedBall.mp hiK) with hlt | heq
    · exact hlt
    · have hz := hb i heq
      have : D i = 0 := by simp [D, divisor_apply hf hiK, hz]
      exact False.elim (hiD this)
  have hint : ∀ i ∈ s, CircleIntegrable (fun z ↦ (D i : ℂ) * (z - i)⁻¹) c R := by
    intro i hi
    apply ContinuousOn.circleIntegrable hR.le
    apply continuousOn_const.mul
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz
    apply sub_ne_zero.mpr
    intro hzi
    change z = i at hzi
    subst z
    exact (ne_of_lt (hinside i hi)) hz
  have hlg : AnalyticOnNhd ℂ (logDeriv g) (closedBall c R) :=
    fun z hz ↦ (hg z hz).logDeriv (hgn ⟨z, hz⟩)
  have heint : (∮ z in C(c, R), logDeriv f z) =
      ∮ z in C(c, R), (∑ i ∈ s, (D i : ℂ) * (z - i)⁻¹) + logDeriv g z := by
    apply circleIntegral.circleIntegral_congr_codiscreteWithin _ hR.ne'
    have heall : logDeriv f =ᶠ[codiscreteWithin (closedBall c R)]
        (fun z ↦ (∑ i ∈ s, (D i : ℂ) * (z - i)⁻¹) + logDeriv g z) := by
      filter_upwards [hlog, hprod, hrat] with z hz hp hr
      exact hz.trans (hp.trans (congrArg (· + logDeriv g z) hr))
    exact heall.filter_mono (Filter.codiscreteWithin_mono (by
      simpa [abs_of_pos hR] using (sphere_subset_closedBall : sphere c R ⊆ closedBall c R)))
  rw [heint, circleIntegral.integral_add (CircleIntegrable.fun_sum s hint)
      (hlg.continuousOn.mono sphere_subset_closedBall |>.circleIntegrable hR.le),
    (hlg.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero
      hR.le, add_zero, circleIntegral.integral_fun_sum hint]
  simp_rw [circleIntegral.integral_const_mul]
  have hi : (∑ i ∈ s, (D i : ℂ) * ∮ z in C(c, R), (z - i)⁻¹) =
      ∑ i ∈ s, (D i : ℂ) * (2 * Real.pi * I) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [circleIntegral.integral_sub_inv_of_mem_ball (hinside i hi)]
  rw [hi]
  rw [← Finset.sum_mul, mul_comm]
  congr 1
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simpa [s, mem_support] using hi

/-- The normalized argument-principle integral is the integer degree of the divisor. -/
theorem two_pi_I_inv_mul_circleIntegral_logDeriv {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : MeromorphicOn f (closedBall c R))
    (hne : ∀ z ∈ closedBall c R, meromorphicOrderAt f z ≠ ⊤)
    (hb : ∀ z ∈ sphere c R, meromorphicOrderAt f z = 0) :
    (2 * Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv f z) =
      ((∑ᶠ z, divisor f (closedBall c R) z : ℤ) : ℂ) := by
  rw [circleIntegral_logDeriv_eq_sum_divisor hR hf hne hb, ← mul_assoc,
    inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  exact ((Int.castAddHom ℂ).map_finsum
    ((divisor f (closedBall c R)).finiteSupport (isCompact_closedBall c R))).symm

/-- The argument principle for a holomorphic function with no boundary zeros. The integer
divisor degree counts interior zeros with their analytic multiplicities.

A counterpart using analytic multiplicities appears in Yury Kudryashov's Mathlib PR #33505. See
`CREDITS.md`. -/
theorem two_pi_I_inv_mul_circleIntegral_logDeriv_of_analyticOnNhd
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hb : ∀ z ∈ sphere c R, f z ≠ 0) :
    (2 * Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv f z) =
      ((∑ᶠ z, divisor f (closedBall c R) z : ℤ) : ℂ) := by
  have horder : ∀ z ∈ sphere c R, meromorphicOrderAt f z = 0 := fun z hz ↦
    (hf z (sphere_subset_closedBall hz)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (hb z hz)
  have hw : c + (R : ℂ) ∈ sphere c R := by
    simp [abs_of_pos hR]
  apply two_pi_I_inv_mul_circleIntegral_logDeriv hR hf.meromorphicOn _ horder
  intro z hz
  apply hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_closedBall c R).isPreconnected (sphere_subset_closedBall hw) hz
  rw [horder _ hw]
  exact WithTop.zero_ne_top

end Complex
