/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Field.GeomSum

/-!
# Pole pushing for Runge's theorem

Uniform approximability on a compact set `K` by the elements of a subalgebra `A` of functions
is preserved by sums, products and uniform limits. The simple pole `(a - z)⁻¹` is approximable
whenever `(a' - z)⁻¹` is, for `a'` close to `a` relative to the distance from `a` to `K`
(geometric series), and hence for all `a` in a connected open set disjoint from `K` as soon as
it holds for one point of that set (pole pushing, Conway VIII.1.6, Simon 4.7). Poles far away
from `K` are approximable by polynomials.

## Main definitions

* `Complex.UniformApproxOn K S h`: `h` is a uniform limit on `K` of elements of `S`.

## Main results

* `Complex.UniformApproxOn.mul`, `Complex.UniformApproxOn.finsetSum`, ...: closure properties.
* `Complex.UniformApproxOn.inv_sub_of_close`: moving a pole by a geometric series.
* `Complex.UniformApproxOn.inv_sub_of_isPreconnected`: pole pushing within a connected open
  set disjoint from `K`.
* `Complex.UniformApproxOn.inv_sub_of_norm_gt`: poles far from `K` and polynomials.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped Topology

namespace Complex

/-- `h` is uniformly approximable on `K` by elements of the set `S` of functions. -/
def UniformApproxOn (K : Set ℂ) (S : Set (ℂ → ℂ)) (h : ℂ → ℂ) : Prop :=
  ∀ ε > 0, ∃ r ∈ S, ∀ z ∈ K, ‖h z - r z‖ ≤ ε

namespace UniformApproxOn

variable {K : Set ℂ} {S : Set (ℂ → ℂ)}

/-- Every member of the approximating set is uniformly approximable by that set. -/
theorem of_mem {h : ℂ → ℂ} (hh : h ∈ S) : UniformApproxOn K S h :=
  fun ε hε => ⟨h, hh, fun z _ => by simp [hε.le]⟩

/-- Uniform approximability is closed under uniform limits on `K`. -/
theorem of_forall_exists {h : ℂ → ℂ}
    (H : ∀ ε > 0, ∃ h' : ℂ → ℂ, UniformApproxOn K S h' ∧ ∀ z ∈ K, ‖h z - h' z‖ ≤ ε) :
    UniformApproxOn K S h := by
  intro ε hε
  obtain ⟨h', hh', hclose⟩ := H (ε / 2) (by positivity)
  obtain ⟨r, hr, hr'⟩ := hh' (ε / 2) (by positivity)
  refine ⟨r, hr, fun z hz => ?_⟩
  calc ‖h z - r z‖ = ‖(h z - h' z) + (h' z - r z)‖ := by congr 1; ring
    _ ≤ ‖h z - h' z‖ + ‖h' z - r z‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hclose z hz) (hr' z hz)
    _ = ε := by ring

/-- An approximable function is bounded on `K` when the approximants are continuous on `K`. -/
theorem exists_bound (hK : IsCompact K) (hS : ∀ r ∈ S, ContinuousOn r K) {h : ℂ → ℂ}
    (hh : UniformApproxOn K S h) : ∃ M, 0 ≤ M ∧ ∀ z ∈ K, ‖h z‖ ≤ M := by
  obtain ⟨r, hr, hr'⟩ := hh 1 one_pos
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hS r hr)
  refine ⟨max C 0 + 1, by positivity, fun z hz => ?_⟩
  calc ‖h z‖ = ‖(h z - r z) + r z‖ := by congr 1; ring
    _ ≤ ‖h z - r z‖ + ‖r z‖ := norm_add_le _ _
    _ ≤ 1 + max C 0 := add_le_add (hr' z hz) ((hC z hz).trans (le_max_left _ _))
    _ = max C 0 + 1 := by ring

section Subalgebra

variable (A : Subalgebra ℂ (ℂ → ℂ))

/-- Uniform approximability by a subalgebra is preserved by addition. -/
theorem add {h₁ h₂ : ℂ → ℂ} (h1 : UniformApproxOn K A h₁) (h2 : UniformApproxOn K A h₂) :
    UniformApproxOn K A (h₁ + h₂) := by
  intro ε hε
  obtain ⟨r₁, hr₁, e₁⟩ := h1 (ε / 2) (by positivity)
  obtain ⟨r₂, hr₂, e₂⟩ := h2 (ε / 2) (by positivity)
  refine ⟨r₁ + r₂, A.add_mem hr₁ hr₂, fun z hz => ?_⟩
  calc ‖(h₁ + h₂) z - (r₁ + r₂) z‖ = ‖(h₁ z - r₁ z) + (h₂ z - r₂ z)‖ := by
        simp only [Pi.add_apply]; congr 1; ring
    _ ≤ ‖h₁ z - r₁ z‖ + ‖h₂ z - r₂ z‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (e₁ z hz) (e₂ z hz)
    _ = ε := by ring

/-- Uniform approximability by a complex subalgebra is preserved by complex scalar multiplication. -/
theorem smul (c : ℂ) {h : ℂ → ℂ} (hh : UniformApproxOn K A h) :
    UniformApproxOn K A (c • h) := by
  intro ε hε
  obtain ⟨r, hr, e⟩ := hh (ε / (‖c‖ + 1)) (by positivity)
  refine ⟨c • r, A.smul_mem hr c, fun z hz => ?_⟩
  simp only [Pi.smul_apply, ← smul_sub, norm_smul]
  calc ‖c‖ * ‖h z - r z‖ ≤ ‖c‖ * (ε / (‖c‖ + 1)) := by gcongr; exact e z hz
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg c]

/-- On a compact set, uniform approximability by a subalgebra of continuous functions is preserved
by multiplication. -/
theorem mul (hK : IsCompact K) (hA : ∀ r ∈ A, ContinuousOn r K) {h₁ h₂ : ℂ → ℂ}
    (h1 : UniformApproxOn K A h₁) (h2 : UniformApproxOn K A h₂) :
    UniformApproxOn K A (h₁ * h₂) := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_bound hK hA h1
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_bound hK hA h2
  intro ε hε
  set δ : ℝ := min 1 (ε / (M₁ + M₂ + 2)) with hδ_def
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  obtain ⟨r₁, hr₁, e₁⟩ := h1 δ hδ
  obtain ⟨r₂, hr₂, e₂⟩ := h2 δ hδ
  refine ⟨r₁ * r₂, A.mul_mem hr₁ hr₂, fun z hz => ?_⟩
  have hr₂b : ‖r₂ z‖ ≤ M₂ + 1 := by
    calc ‖r₂ z‖ = ‖h₂ z - (h₂ z - r₂ z)‖ := by congr 1; ring
      _ ≤ ‖h₂ z‖ + ‖h₂ z - r₂ z‖ := norm_sub_le _ _
      _ ≤ M₂ + 1 := add_le_add (hM₂ z hz) ((e₂ z hz).trans (min_le_left _ _))
  have hδ1 : δ ≤ ε / (M₁ + M₂ + 2) := min_le_right _ _
  calc ‖(h₁ * h₂) z - (r₁ * r₂) z‖
      = ‖h₁ z * (h₂ z - r₂ z) + (h₁ z - r₁ z) * r₂ z‖ := by
        simp only [Pi.mul_apply]; congr 1; ring
    _ ≤ ‖h₁ z * (h₂ z - r₂ z)‖ + ‖(h₁ z - r₁ z) * r₂ z‖ := norm_add_le _ _
    _ = ‖h₁ z‖ * ‖h₂ z - r₂ z‖ + ‖h₁ z - r₁ z‖ * ‖r₂ z‖ := by rw [norm_mul, norm_mul]
    _ ≤ M₁ * δ + δ * (M₂ + 1) :=
        add_le_add (mul_le_mul (hM₁ z hz) (e₂ z hz) (norm_nonneg _) hM₁0)
          (mul_le_mul (e₁ z hz) hr₂b (norm_nonneg _) hδ.le)
    _ = δ * (M₁ + M₂ + 1) := by ring
    _ ≤ ε / (M₁ + M₂ + 2) * (M₁ + M₂ + 2) :=
        mul_le_mul hδ1 (by linarith) (by positivity) (by positivity)
    _ = ε := div_mul_cancel₀ _ (by positivity)

/-- On a compact set, uniform approximability by a subalgebra of continuous functions is preserved
by natural powers. -/
theorem pow (hK : IsCompact K) (hA : ∀ r ∈ A, ContinuousOn r K) {h : ℂ → ℂ}
    (hh : UniformApproxOn K A h) (n : ℕ) : UniformApproxOn K A (h ^ n) := by
  induction n with
  | zero => simpa using of_mem (S := (A : Set (ℂ → ℂ))) A.one_mem
  | succ n ih => rw [pow_succ]; exact mul A hK hA ih hh

/-- Uniform approximability by a subalgebra is preserved by finite sums. -/
theorem finsetSum {ι : Type*} (s : Finset ι) {h : ι → ℂ → ℂ}
    (hh : ∀ i ∈ s, UniformApproxOn K A (h i)) :
    UniformApproxOn K A (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using of_mem (S := (A : Set (ℂ → ℂ))) A.zero_mem
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact add A (hh a (Finset.mem_insert_self a s))
      (ih fun i hi => hh i (Finset.mem_insert_of_mem hi))

/-- **Moving a pole by a geometric series.** If `(a - z)⁻¹` is approximable and `a'` is closer
to `a` than a fixed fraction `q < 1` of the distance from `a` to every point of `K`, then
`(a' - z)⁻¹` is approximable. -/
theorem inv_sub_of_close (hK : IsCompact K) (hA : ∀ r ∈ A, ContinuousOn r K) {a a' : ℂ}
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) (hclose : ∀ z ∈ K, ‖a - a'‖ ≤ q * ‖a - z‖)
    {d : ℝ} (hd : 0 < d) (hdist : ∀ z ∈ K, d ≤ ‖a - z‖)
    (ha : UniformApproxOn K A (fun z => (a - z)⁻¹)) :
    UniformApproxOn K A (fun z => (a' - z)⁻¹) := by
  apply of_forall_exists
  intro ε hε
  have h1q : 0 < 1 - q := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ε * ((1 - q) * d)) hq
  refine ⟨fun z => ∑ k ∈ Finset.range N, (a - a') ^ k * ((a - z)⁻¹) ^ (k + 1), ?_,
    fun z hz => ?_⟩
  · have heq : (fun z => ∑ k ∈ Finset.range N, (a - a') ^ k * ((a - z)⁻¹) ^ (k + 1)) =
        ∑ k ∈ Finset.range N, (a - a') ^ k • (fun z => (a - z)⁻¹) ^ (k + 1) := by
      ext z
      simp [Finset.sum_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
    rw [heq]
    exact finsetSum A _ fun k _ => smul A _ (pow A hK hA ha _)
  · have hdz := hdist z hz
    have hz0 : a - z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hdz
      linarith
    set t : ℂ := (a - a') / (a - z) with ht_def
    have ht : ‖t‖ ≤ q := by
      rw [ht_def, norm_div]
      exact div_le_of_le_mul₀ (norm_nonneg _) hq0 (hclose z hz)
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, norm_one] at ht
      linarith
    have h1t : 1 - q ≤ ‖1 - t‖ := by
      have := norm_sub_norm_le (1 : ℂ) t
      rw [norm_one] at this
      linarith
    have h1t0 : (1 : ℂ) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
    have hid : (a' - z)⁻¹ - ∑ k ∈ Finset.range N, (a - a') ^ k * ((a - z)⁻¹) ^ (k + 1) =
        (a - z)⁻¹ * (t ^ N / (1 - t)) := by
      have hsum : ∑ k ∈ Finset.range N, (a - a') ^ k * ((a - z)⁻¹) ^ (k + 1) =
          (a - z)⁻¹ * ∑ k ∈ Finset.range N, t ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ht_def, div_pow, pow_succ, div_eq_mul_inv, ← inv_pow]
        ring
      have ha'z : a' - z = (a - z) * (1 - t) := by
        rw [ht_def]
        field_simp
        ring
      rw [hsum, geom_sum_eq ht1, ha'z, mul_inv]
      field_simp
      ring
    rw [hid, norm_mul, norm_inv, norm_div, norm_pow]
    calc ‖a - z‖⁻¹ * (‖t‖ ^ N / ‖1 - t‖) ≤ d⁻¹ * (q ^ N / (1 - q)) := by
          gcongr
      _ ≤ ε := by
          rw [inv_mul_eq_div, div_div, div_le_iff₀ (by positivity)]
          linarith

/-- **Pole pushing.** If `W` is a preconnected set disjoint from `K` and `(a₀ - z)⁻¹` is
approximable for one point `a₀ ∈ W`, then `(a - z)⁻¹` is approximable for every `a ∈ W`. -/
theorem inv_sub_of_isPreconnected (hK : IsCompact K) (hA : ∀ r ∈ A, ContinuousOn r K)
    {W : Set ℂ} (hWc : IsPreconnected W) (hWK : Disjoint W K)
    {a₀ : ℂ} (ha₀ : a₀ ∈ W) (h₀ : UniformApproxOn K A (fun z => (a₀ - z)⁻¹))
    {a : ℂ} (ha : a ∈ W) : UniformApproxOn K A (fun z => (a - z)⁻¹) := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · intro ε _
    exact ⟨0, A.zero_mem, fun z hz => by simp [hKe] at hz⟩
  have hinf : ∀ b, b ∉ K → 0 < infDist b K := fun b hb =>
    (hK.isClosed.notMem_iff_infDist_pos hKne).mp hb
  have hinf_le : ∀ b, ∀ z ∈ K, infDist b K ≤ ‖b - z‖ := fun b z hz => by
    rw [← dist_eq_norm]
    exact infDist_le_dist_of_mem hz
  set T₀ : Set ℂ := {b | b ∉ K ∧ UniformApproxOn K A (fun z => (b - z)⁻¹)} with hT₀_def
  have hopen : IsOpen T₀ := by
    rw [Metric.isOpen_iff]
    rintro b ⟨hbK, hb⟩
    have hd := hinf b hbK
    refine ⟨infDist b K / 2, by positivity, fun b' hb' => ?_⟩
    rw [mem_ball, dist_eq_norm] at hb'
    have hb'K : b' ∉ K := fun h => by
      have := hinf_le b b' h
      rw [norm_sub_rev] at this
      linarith
    refine ⟨hb'K, inv_sub_of_close A hK hA (q := 1 / 2) (by norm_num) (by norm_num)
      (fun z hz => ?_) hd (hinf_le b) hb⟩
    have := hinf_le b z hz
    rw [norm_sub_rev]
    linarith
  set V : Set ℂ := ⋃ b ∈ W \ T₀, ball b (infDist b K / 4) with hV_def
  have hVo : IsOpen V := isOpen_biUnion fun b _ => isOpen_ball
  have hdisj : Disjoint T₀ V := by
    rw [Set.disjoint_left]
    rintro b' ⟨hb'K, hb'⟩ hb'V
    obtain ⟨b, ⟨hbW, hbT⟩, hb'b⟩ := mem_iUnion₂.mp hb'V
    apply hbT
    have hbK : b ∉ K := fun h => hWK.notMem_of_mem_left hbW h
    have hd := hinf b hbK
    rw [mem_ball, dist_eq_norm] at hb'b
    have hfar : ∀ z ∈ K, 3 * infDist b K / 4 ≤ ‖b' - z‖ := fun z hz => by
      have h1 := hinf_le b z hz
      have h2 := norm_sub_le_norm_sub_add_norm_sub b b' z
      have h3 : ‖b - b'‖ = ‖b' - b‖ := norm_sub_rev _ _
      linarith
    refine ⟨hbK, inv_sub_of_close A hK hA (q := 1 / 3) (by norm_num) (by norm_num)
      (fun z hz => ?_) (d := 3 * infDist b K / 4) (by positivity) hfar hb'⟩
    have := hfar z hz
    linarith
  have hcover : W ⊆ T₀ ∪ V := fun b hb => by
    by_cases hbT : b ∈ T₀
    · exact Or.inl hbT
    · refine Or.inr (mem_iUnion₂.mpr ⟨b, ⟨hb, hbT⟩, mem_ball_self ?_⟩)
      have := hinf b fun h => hWK.notMem_of_mem_left hb h
      positivity
  have hsub := hWc.subset_left_of_subset_union hopen hVo hdisj hcover
    ⟨a₀, ha₀, hWK.notMem_of_mem_left ha₀, h₀⟩
  exact (hsub ha).2

/-- **Poles far from `K` are approximable by polynomials.** If `K ⊆ closedBall 0 R` and
`R < ‖a‖`, then `(a - z)⁻¹` is approximable by the subalgebra generated by the identity. -/
theorem inv_sub_of_norm_gt (hK : IsCompact K) (hA : ∀ r ∈ A, ContinuousOn r K)
    (hid : (fun z : ℂ => z) ∈ A) {R : ℝ} (hR : 0 ≤ R) (hKR : K ⊆ closedBall 0 R)
    {a : ℂ} (ha : R < ‖a‖) : UniformApproxOn K A (fun z => (a - z)⁻¹) := by
  apply of_forall_exists
  intro ε hε
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    linarith
  set q : ℝ := R / ‖a‖ with hq_def
  have hq0 : 0 ≤ q := by positivity
  have hq : q < 1 := (div_lt_one (hR.trans_lt ha)).mpr ha
  have h1q : 0 < 1 - q := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ε * ((1 - q) * ‖a‖)) hq
  refine ⟨fun z => ∑ k ∈ Finset.range N, (a⁻¹) ^ (k + 1) * z ^ k, ?_, fun z hz => ?_⟩
  · have heq : (fun z => ∑ k ∈ Finset.range N, (a⁻¹) ^ (k + 1) * z ^ k) =
        ∑ k ∈ Finset.range N, (a⁻¹) ^ (k + 1) • (fun z : ℂ => z) ^ k := by
      ext z
      simp [Finset.sum_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul]
    rw [heq]
    exact finsetSum A _ fun k _ => smul A _ (pow A hK hA (of_mem hid) _)
  · have hzR : ‖z‖ ≤ R := by simpa using hKR hz
    set t : ℂ := z / a with ht_def
    have ht : ‖t‖ ≤ q := by
      rw [ht_def, norm_div]
      exact div_le_div_of_nonneg_right hzR (norm_nonneg _)
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, norm_one] at ht
      linarith
    have h1t : 1 - q ≤ ‖1 - t‖ := by
      have := norm_sub_norm_le (1 : ℂ) t
      rw [norm_one] at this
      linarith
    have h1t0 : (1 : ℂ) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
    have hid' : (a - z)⁻¹ - ∑ k ∈ Finset.range N, (a⁻¹) ^ (k + 1) * z ^ k =
        a⁻¹ * (t ^ N / (1 - t)) := by
      have hsum : ∑ k ∈ Finset.range N, (a⁻¹) ^ (k + 1) * z ^ k =
          a⁻¹ * ∑ k ∈ Finset.range N, t ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ht_def, div_pow, pow_succ, div_eq_mul_inv, ← inv_pow]
        ring
      have haz : a - z = a * (1 - t) := by
        rw [ht_def]
        field_simp
      rw [hsum, geom_sum_eq ht1, haz, mul_inv]
      field_simp
      ring
    rw [hid', norm_mul, norm_inv, norm_div, norm_pow]
    calc ‖a‖⁻¹ * (‖t‖ ^ N / ‖1 - t‖) ≤ ‖a‖⁻¹ * (q ^ N / (1 - q)) := by
          gcongr
      _ ≤ ε := by
          rw [inv_mul_eq_div, div_div, div_le_iff₀ (by positivity)]
          linarith

end Subalgebra

end UniformApproxOn

/-- Every element of the subalgebra generated by functions continuous on `K` is continuous
on `K`. -/
theorem continuousOn_of_mem_adjoin {K : Set ℂ} {G : Set (ℂ → ℂ)}
    (hG : ∀ g ∈ G, ContinuousOn g K) {r : ℂ → ℂ} (hr : r ∈ Algebra.adjoin ℂ G) :
    ContinuousOn r K := by
  induction hr using Algebra.adjoin_induction with
  | mem g hg => exact hG g hg
  | algebraMap c => exact continuousOn_const
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

end Complex

end
