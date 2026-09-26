/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Smooth concatenation of paths

A chain of `n` paths `γ i` from `x i` to `x (i + 1)` is concatenated into a single path from
`x 0` to `x n` by traversing the `i`-th path on the parameter interval `[i / n, (i + 1) / n]`
with the reparametrization `t ↦ smoothTransition (n * t - i)`. The gluing function
`Real.smoothTransition` is smooth and has all derivatives zero at `0` and `1`, so the
concatenation is `C¹` whenever every piece is, even when consecutive pieces meet at a corner.
In particular a closed piecewise-`C¹` curve, such as the boundary of a polygon, becomes a single
closed `C¹` curve.

Reparametrization does not change curve integrals: the curve integral of a one-form over the
concatenation is the sum of its integrals over the pieces.

## Main definitions

* `Path.smoothConcatFun x γ`: the concatenated parametrization `ℝ → E`.
* `Path.smoothConcat x γ`: the concatenation as a path from `x 0` to `x n`.

## Main results

* `Path.smoothConcatFun_eq`: on `[k / n, (k + 1) / n]` the concatenation traverses the `k`-th
  path.
* `Path.contDiffOn_smoothConcat_extend`: the concatenation of `C¹` paths is `C¹` (and of `Cᵐ`
  paths is `Cᵐ`).
* `Path.smoothConcat_extend`: the extension of the concatenation to `ℝ` is `smoothConcatFun`.
* `Path.range_smoothConcat_subset`: the concatenation stays in the union of the pieces.
* `Path.curveIntegral_smoothConcat`: the curve integral over the concatenation is the sum of the
  curve integrals over the pieces.
-/

@[expose] public noncomputable section

open Set MeasureTheory Real
open scoped unitInterval

namespace Path

variable {E : Type*} [NormedAddCommGroup E] {n : ℕ} {x : ℕ → E}

/-- The smooth concatenation of a chain of paths `γ i` from `x i` to `x (i + 1)`, `i < n`: the
`i`-th path is traversed on `[i / n, (i + 1) / n]`, reparametrized by
`t ↦ smoothTransition (n * t - i)`. -/
def smoothConcatFun (x : ℕ → E) (γ : (i : Fin n) → Path (x i) (x (i + 1))) (t : ℝ) : E :=
  x 0 + ∑ i : Fin n, ((γ i).extend (smoothTransition (n * t - i)) - x i)

variable (γ : (i : Fin n) → Path (x i) (x (i + 1)))

/-- The value of the `i`-th summand of `smoothConcatFun` on the parameter interval of the
`k`-th piece. -/
private theorem smoothConcat_summand_eq {k : ℕ} {t : ℝ} (ht : t ∈ Icc (k / n : ℝ) ((k + 1) / n))
    (i : Fin n) :
    (γ i).extend (smoothTransition (n * t - i)) - x i =
      if (i : ℕ) < k then x (i + 1) - x i
      else if (i : ℕ) = k then (γ i).extend (smoothTransition (n * t - i)) - x i else 0 := by
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    exact_mod_cast this
  have h1 : (k : ℝ) ≤ n * t := by
    have := ht.1
    rw [div_le_iff₀' hn] at this
    linarith
  have h2 : n * t ≤ k + 1 := by
    have := ht.2
    rw [le_div_iff₀' hn] at this
    linarith
  split_ifs with hik hik'
  · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
    rw [smoothTransition.one_of_one_le (by linarith), Path.extend_one]
  · rfl
  · have : (k : ℝ) + 1 ≤ i := by exact_mod_cast (by omega : k + 1 ≤ (i : ℕ))
    rw [smoothTransition.zero_of_nonpos (by linarith), Path.extend_zero, sub_self]

/-- On the parameter interval `[k / n, (k + 1) / n]` the concatenation traverses the `k`-th
path. -/
theorem smoothConcatFun_eq (k : Fin n) {t : ℝ} (ht : t ∈ Icc (k / n : ℝ) ((k + 1) / n)) :
    smoothConcatFun x γ t = (γ k).extend (smoothTransition (n * t - k)) := by
  classical
  rw [smoothConcatFun, Finset.sum_congr rfl fun i _ => smoothConcat_summand_eq γ ht i,
    Finset.sum_ite, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilt : (Finset.univ.filter fun i : Fin n => ¬ (i : ℕ) < k).filter
      (fun i : Fin n => (i : ℕ) = k) = {k} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact Fin.ext h
    · rintro rfl
      exact ⟨lt_irrefl _, rfl⟩
  rw [hfilt, Finset.sum_singleton]
  have htel : ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), (x (i + 1) - x i) =
      x k - x 0 := by
    rw [← Finset.sum_range_sub x k]
    refine Finset.sum_nbij (fun i => (i : ℕ)) (fun i hi => ?_) (fun i _ j _ h => Fin.ext h)
      (fun j hj => ?_) (fun _ _ => rfl)
    · simpa using hi
    · have hj : j < k := Finset.mem_range.mp hj
      exact ⟨⟨j, hj.trans k.isLt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
  rw [htel]
  abel

/-- The concatenation starts at `x 0`. -/
theorem smoothConcatFun_zero : smoothConcatFun x γ 0 = x 0 := by
  simp only [smoothConcatFun, mul_zero, zero_sub]
  rw [Finset.sum_eq_zero fun i _ => by
    rw [smoothTransition.zero_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg _)), Path.extend_zero,
      sub_self], add_zero]

/-- The concatenation ends at `x n`. -/
theorem smoothConcatFun_one : smoothConcatFun x γ 1 = x n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [smoothConcatFun]
  have hk : n - 1 < n := Nat.sub_lt hn one_pos
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne'), Nat.cast_one, sub_add_cancel]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [smoothConcatFun_eq γ ⟨n - 1, hk⟩ (t := 1) ⟨by
      rw [div_le_one hn']; exact_mod_cast Nat.sub_le n 1,
      by simp only [hcast, div_self hn'.ne', le_refl]⟩]
  rw [mul_one, show (n : ℝ) - (n - 1 : ℕ) = 1 by rw [← hcast]; ring, smoothTransition.one,
    Path.extend_one]
  congr 1
  change n - 1 + 1 = n
  omega

/-- Before the start of the parameter interval, the concatenation stays at `x 0`. -/
theorem smoothConcatFun_of_nonpos {t : ℝ} (ht : t ≤ 0) : smoothConcatFun x γ t = x 0 := by
  rw [← smoothConcatFun_zero γ]
  refine congrArg (x 0 + ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  rw [smoothTransition.zero_of_nonpos (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]),
    smoothTransition.zero_of_nonpos (by simp)]

/-- After the end of the parameter interval, the concatenation stays at `x n`. -/
theorem smoothConcatFun_of_one_le {t : ℝ} (ht : 1 ≤ t) : smoothConcatFun x γ t = x n := by
  rw [← smoothConcatFun_one γ]
  refine congrArg (x 0 + ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  rw [smoothTransition.one_of_one_le (by nlinarith), smoothTransition.one_of_one_le (by linarith)]

/-- The concatenation is continuous. -/
theorem continuous_smoothConcatFun : Continuous (smoothConcatFun x γ) :=
  continuous_const.add <| continuous_finsetSum _ fun i _ =>
    ((γ i).continuous_extend.comp (smoothTransition.continuous.comp
      ((continuous_const.mul continuous_id).sub continuous_const))).sub continuous_const

/-- The smooth concatenation of a chain of paths `γ i` from `x i` to `x (i + 1)`, `i < n`, as a
path from `x 0` to `x n`. -/
def smoothConcat : Path (x 0) (x n) where
  toFun t := smoothConcatFun x γ t
  continuous_toFun := (continuous_smoothConcatFun γ).comp continuous_subtype_val
  source' := smoothConcatFun_zero γ
  target' := smoothConcatFun_one γ

/-- On the unit interval, the extension of the concatenation is `smoothConcatFun`. -/
theorem smoothConcat_extend_eqOn : EqOn (smoothConcat γ).extend (smoothConcatFun x γ) I :=
  fun t ht => by rw [Path.extend_apply _ ht]; rfl

/-- The extension of the concatenation to `ℝ` is `smoothConcatFun`, which is already constant
outside the unit interval. -/
theorem smoothConcat_extend : ((smoothConcat γ).extend : ℝ → E) = smoothConcatFun x γ := by
  funext t
  rcases le_total t 0 with h0 | h0
  · rw [Path.extend_of_le_zero _ h0, smoothConcatFun_of_nonpos γ h0]
  rcases le_total 1 t with h1 | h1
  · rw [Path.extend_of_one_le _ h1, smoothConcatFun_of_one_le γ h1]
  · exact smoothConcat_extend_eqOn γ ⟨h0, h1⟩

/-- Every point of the concatenation lies on one of the pieces, when there is at least one. -/
theorem range_smoothConcat_subset (hn : 0 < n) : range (smoothConcat γ) ⊆ ⋃ i, range (γ i) := by
  rintro _ ⟨⟨t, ht⟩, rfl⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set k : ℕ := min ⌊n * t⌋₊ (n - 1)
  have hk : k < n := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hn one_pos)
  have hmem : t ∈ Icc (k / n : ℝ) ((k + 1) / n) := by
    constructor
    · rw [div_le_iff₀' hn']
      exact (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le (by nlinarith [ht.1]))
    · rw [le_div_iff₀' hn']
      rcases le_total ⌊n * t⌋₊ (n - 1) with h | h
      · rw [show k = ⌊n * t⌋₊ from min_eq_left h]
        exact (Nat.lt_floor_add_one _).le
      · rw [show k = n - 1 from min_eq_right h, Nat.cast_sub (by omega), Nat.cast_one,
          sub_add_cancel]
        nlinarith [ht.2]
  refine mem_iUnion.mpr ⟨⟨k, hk⟩, ?_⟩
  change smoothConcatFun x γ t ∈ _
  rw [smoothConcatFun_eq γ ⟨k, hk⟩ hmem]
  exact ⟨_, rfl⟩

section ContDiff

variable [NormedSpace ℝ E]

/-- The concatenation of `Cᵐ` paths is `Cᵐ` on the whole real line. -/
theorem contDiff_smoothConcatFun {m : ℕ∞} (hγ : ∀ i, ContDiffOn ℝ m (γ i).extend I) :
    ContDiff ℝ m (smoothConcatFun x γ) :=
  contDiff_const.add <| ContDiff.sum fun i _ =>
    ((hγ i).comp_contDiff (smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const))
      fun _ => ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩).sub contDiff_const

/-- The concatenation of `Cᵐ` paths is a `Cᵐ` path. -/
theorem contDiffOn_smoothConcat_extend {m : ℕ∞} (hγ : ∀ i, ContDiffOn ℝ m (γ i).extend I) :
    ContDiffOn ℝ m (smoothConcat γ).extend I :=
  (contDiff_smoothConcatFun γ hγ).contDiffOn.congr (smoothConcat_extend_eqOn γ)

end ContDiff

section Integral

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On an interval `[a, b]`, a function that agrees with `h` on `(a, b)` has the same interval
integral as `h` over `[a, b]`. -/
private theorem intervalIntegral_eq_setIntegral_Icc_of_eqOn_Ioo [NormedSpace ℝ F]
    {f h : ℝ → F} {a b : ℝ} (hab : a ≤ b) (hfh : EqOn f h (Ioo a b)) :
    ∫ t in a..b, f t = ∫ t in Icc a b, h t := by
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo hfh

/-- The curve-integral integrand of the concatenation on the open parameter interval of the
`k`-th piece is the reparametrized integrand of that piece. -/
private theorem curveIntegralFun_smoothConcat_eq [NormedSpace ℝ F] (ω : E → E →L[𝕜] F)
    (hγ : ∀ i, DifferentiableOn ℝ (γ i).extend I) (k : Fin n) {t : ℝ}
    (ht : t ∈ Ioo (k / n : ℝ) ((k + 1) / n)) :
    curveIntegralFun ω (smoothConcat γ) t =
      (deriv smoothTransition (n * t - k) * n) •
        curveIntegralFun ω (γ k) (smoothTransition (n * t - k)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hkn : (k + 1 : ℝ) ≤ n := by exact_mod_cast k.isLt
  have h1 : 0 < n * t - k := by
    have := ht.1; rw [div_lt_iff₀' hn] at this; linarith
  have h2 : n * t - k < 1 := by
    have := ht.2; rw [lt_div_iff₀' hn] at this; linarith
  set φ : ℝ → ℝ := fun s => smoothTransition (n * s - k)
  have hφI : φ t ∈ Ioo (0 : ℝ) 1 :=
    ⟨smoothTransition.pos_of_pos h1, smoothTransition.lt_one_of_lt_one h2⟩
  have htI : t ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_le_of_lt (by positivity) ht.1, ht.2.trans_le ?_⟩
    rw [div_le_one hn]; exact hkn
  -- the derivative of the reparametrization
  have hφ : HasDerivAt φ (deriv smoothTransition (n * t - k) * n) t := by
    have hb : HasDerivAt (fun s : ℝ => n * s - k) n t := by
      simpa using ((hasDerivAt_id t).const_mul (n : ℝ)).sub_const (k : ℝ)
    exact (smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _ |>.hasDerivAt.comp t hb
  -- the derivative of the piece at the interior point `φ t`
  have hγk : HasDerivAt (γ k).extend (derivWithin (γ k).extend I (φ t)) (φ t) :=
    ((hγ k).differentiableAt (Icc_mem_nhds hφI.1 hφI.2)).hasDerivAt.congr_deriv
      (derivWithin_of_mem_nhds (Icc_mem_nhds hφI.1 hφI.2)).symm
  -- near `t`, the concatenation is the reparametrized piece
  have hev : (smoothConcat γ).extend =ᶠ[nhds t] (γ k).extend ∘ φ := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2, Ioo_mem_nhds htI.1 htI.2] with s hs hsI
    rw [smoothConcat_extend_eqOn γ (Ioo_subset_Icc_self hsI)]
    exact smoothConcatFun_eq γ k (Ioo_subset_Icc_self hs)
  have hd : HasDerivAt (smoothConcat γ).extend
      ((deriv smoothTransition (n * t - k) * n) • derivWithin (γ k).extend I (φ t)) t :=
    (hγk.scomp t hφ).congr_of_eventuallyEq hev
  rw [curveIntegralFun_def, curveIntegralFun_def,
    derivWithin_of_mem_nhds (Icc_mem_nhds htI.1 htI.2), hd.deriv,
    hev.eq_of_nhds, Function.comp_apply, ContinuousLinearMap.map_smul_of_tower]

/-- The integral over the parameter interval of the `k`-th piece is the curve integral over that
piece. -/
private theorem integral_piece_smoothConcat (ω : E → E →L[𝕜] F)
    (hγ : ∀ i, DifferentiableOn ℝ (γ i).extend I) (k : Fin n) :
    letI : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
    (∫ t in (k / n : ℝ)..((k + 1) / n), curveIntegralFun ω (smoothConcat γ) t) =
      curveIntegral ω (γ k) ∧
    (CurveIntegrable ω (γ k) →
      IntervalIntegrable (curveIntegralFun ω (smoothConcat γ)) volume (k / n : ℝ)
        ((k + 1) / n)) := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  have hn : (0 : ℝ) < n := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hab : (k / n : ℝ) ≤ (k + 1) / n := div_le_div_of_nonneg_right (by linarith) hn.le
  set φ : ℝ → ℝ := fun s => smoothTransition (n * s - k)
  set φ' : ℝ → ℝ := fun s => deriv smoothTransition (n * s - k) * n
  have hφc : ContinuousOn φ (Icc (k / n : ℝ) ((k + 1) / n)) :=
    (smoothTransition.continuous.comp ((continuous_const.mul continuous_id).sub
      continuous_const)).continuousOn
  have hφd : ∀ s ∈ Ioo (k / n : ℝ) ((k + 1) / n), HasDerivAt φ (φ' s) s := fun s _ => by
    have hb : HasDerivAt (fun s : ℝ => n * s - k) n s := by
      simpa using ((hasDerivAt_id s).const_mul (n : ℝ)).sub_const (k : ℝ)
    exact (smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _ |>.hasDerivAt.comp s hb
  have hφ' : ∀ s ∈ Ioo (k / n : ℝ) ((k + 1) / n), 0 ≤ φ' s := fun s _ =>
    mul_nonneg smoothTransition.monotone.deriv_nonneg hn.le
  have hφa : φ (k / n) = 0 := by
    simp only [φ, mul_div_cancel₀ _ hn.ne', sub_self, smoothTransition.zero]
  have hφb : φ ((k + 1) / n) = 1 := by
    simp only [φ, mul_div_cancel₀ _ hn.ne', add_sub_cancel_left, smoothTransition.one]
  have heq : EqOn (curveIntegralFun ω (smoothConcat γ))
      (fun s => φ' s • curveIntegralFun ω (γ k) (φ s)) (Ioo (k / n : ℝ) ((k + 1) / n)) :=
    fun s hs => curveIntegralFun_smoothConcat_eq γ ω hγ k hs
  refine ⟨?_, fun hint => ?_⟩
  · rw [intervalIntegral_eq_setIntegral_Icc_of_eqOn_Ioo hab heq,
      integral_Icc_deriv_smul_of_deriv_nonneg hφc hφd hφ' hab, hφa, hφb, curveIntegral_def,
      intervalIntegral_eq_setIntegral_Icc_of_eqOn_Ioo zero_le_one fun _ _ => rfl]
  · have hI : IntegrableOn (fun s => φ' s • curveIntegralFun ω (γ k) (φ s))
        (Icc (k / n : ℝ) ((k + 1) / n)) := by
      rw [integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg hφc hφd hφ' hab, hφa, hφb]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hint
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
    exact (hI.mono_set Ioo_subset_Icc_self).congr_fun heq.symm measurableSet_Ioo

omit [IsScalarTower ℝ 𝕜 E] in
/-- The concatenation of the empty chain is constant, so its curve-integral integrand vanishes. -/
private theorem curveIntegralFun_smoothConcat_of_zero (γ : (i : Fin 0) → Path (x i) (x (i + 1)))
    (ω : E → E →L[𝕜] F) : curveIntegralFun ω (smoothConcat γ) = 0 := by
  funext t
  have : ((smoothConcat γ).extend : ℝ → E) = fun _ => x 0 := by
    funext s
    simp [Path.extend, IccExtend, smoothConcat, smoothConcatFun]
  rw [curveIntegralFun_def, this]
  simp

/-- **Curve integrals over a smooth concatenation.** The curve integral of a one-form over the
smooth concatenation of differentiable, integrable paths is the sum of the curve integrals over
the pieces. -/
theorem curveIntegral_smoothConcat (ω : E → E →L[𝕜] F)
    (hγ : ∀ i, DifferentiableOn ℝ (γ i).extend I) (hint : ∀ i, CurveIntegrable ω (γ i)) :
    curveIntegral ω (smoothConcat γ) = ∑ i, curveIntegral ω (γ i) := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hconst := curveIntegralFun_smoothConcat_of_zero γ ω
    rw [curveIntegral_def, hconst]
    simp
  set a : ℕ → ℝ := fun k => k / n
  have hpiece := fun k : Fin n => integral_piece_smoothConcat γ ω hγ k
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := n)
    (f := curveIntegralFun ω (smoothConcat γ)) (μ := volume) fun k hk => by
      simpa [a, Nat.cast_add, Nat.cast_one] using (hpiece ⟨k, hk⟩).2 (hint ⟨k, hk⟩)
  simp only [a, Nat.cast_zero, zero_div, div_self (show (n : ℝ) ≠ 0 by positivity)] at hsum
  rw [curveIntegral_def, ← hsum, ← Fin.sum_univ_eq_sum_range
    (fun k => ∫ t in (k / n : ℝ)..((k + 1 : ℕ) / n), curveIntegralFun ω (smoothConcat γ) t)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simpa [Nat.cast_add, Nat.cast_one] using (hpiece k).1

/-- The smooth concatenation of differentiable, integrable paths is integrable. -/
theorem curveIntegrable_smoothConcat (ω : E → E →L[𝕜] F)
    (hγ : ∀ i, DifferentiableOn ℝ (γ i).extend I) (hint : ∀ i, CurveIntegrable ω (γ i)) :
    CurveIntegrable ω (smoothConcat γ) := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hconst := curveIntegralFun_smoothConcat_of_zero γ ω
    rw [CurveIntegrable, hconst]
    exact intervalIntegrable_const
  have h := IntervalIntegrable.trans_iterate (a := fun k : ℕ => (k / n : ℝ)) (n := n)
    (f := curveIntegralFun ω (smoothConcat γ)) (μ := volume) fun k hk => by
      simpa [Nat.cast_add, Nat.cast_one] using
        (integral_piece_smoothConcat γ ω hγ ⟨k, hk⟩).2 (hint ⟨k, hk⟩)
  change IntervalIntegrable _ volume 0 1
  simpa [div_self (show (n : ℝ) ≠ 0 by positivity)] using h

end Integral

end Path
