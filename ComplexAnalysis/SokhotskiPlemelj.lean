/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.PringsheimVivanti

/-!
# The Sokhotski–Plemelj jump relation

For a density `φ` on a circle `|w| = R`, the Cauchy-type integral
`Φ(z) = (2πi)⁻¹ ∮_{|w|=R} φ(w) / (w - z) dw`
is holomorphic off the circle, and classically its boundary values from inside and outside a
point `t` on the circle differ by the density itself: `Φ₊(t) - Φ₋(t) = φ(t)`.

This file proves this jump relation for densities `φ` given by an *absolutely summable* two-sided
Laurent series on the circle, i.e. `φ(w) = ∑ₖ c_k w^k` (`k : ℤ`) with `∑ₖ ‖c_k‖ R^k` summable.
Under this hypothesis the two one-sided Cauchy-type integrals are themselves given by explicit,
absolutely convergent power series in the nonnegative and (respectively) negative Laurent
coefficients of `φ`:

* `Complex.cauchyTypeInterior c z = ∑ₙ c_n z^n` (`n : ℕ`), agreeing with `Φ(z)` for `‖z‖ < R`;
* `Complex.cauchyTypeExterior c z = -∑ₙ c_{-(n+1)} z^{-(n+1)}` (`n : ℕ`), agreeing with `Φ(z)` for
  `‖z‖ > R`.

Since `c` is summable at radius `R` itself, both series converge absolutely at any point `t` of
the circle, giving natural continuations of `Φ` to the boundary from each side; their difference
recovers the two-sided Laurent series of `φ` there, which is `φ(t)`. This is the jump relation.

The proof identifies `c` with the Laurent coefficients of `φ` on the circle
(`Complex.circleLaurentCoeff_laurentBoundaryValue`, by term-by-term circle integration and the
elementary evaluation `∮ w^m dw = 2πi · [m = -1]` from `PringsheimVivanti`), then invokes the
project's Laurent expansion `hasSum_circleLaurentCoeff_nat` / `hasSum_circleLaurentCoeff_negSucc`
(`LaurentSeries.Basic`) to recognize the two power series as the actual Cauchy-type integral on
each side.

## Main results

* `Complex.cauchyTypeInterior_eq_circleIntegral`, `Complex.cauchyTypeExterior_eq_circleIntegral`:
  the one-sided power series agree with the Cauchy-type contour integral of `φ`.
* `Complex.cauchyTypeInterior_sub_cauchyTypeExterior`: **the Sokhotski–Plemelj jump relation**.

## References

* N. I. Muskhelishvili, *Singular Integral Equations*, Section 17.
* F. D. Gakhov, *Boundary Value Problems*, Chapter VIII, Section 7.
-/

public noncomputable section

open Set Metric Filter MeasureTheory Complex
open scoped Topology Real

namespace Complex

/-- Term-by-term circle integration of `w^e` against a one-sided series `∑ₖ d_k w^{g k}`
(`k : ℕ`, arbitrary integer exponents `g k`), justified by uniform convergence of the partial
sums on the circle (Weierstrass's `M`-test). -/
theorem circleIntegral_zpow_mul_tsum_zpow_eq (d : ℕ → ℂ) (g : ℕ → ℤ) (R : ℝ) (hR : 0 < R)
    (hd : Summable (fun k : ℕ => ‖d k‖ * R ^ (g k))) (e : ℤ) :
    (∮ w in C(0, R), w ^ e * ∑' k : ℕ, d k * w ^ (g k)) =
      ∑' k : ℕ, d k * ∮ w in C(0, R), w ^ (e + g k) := by
  set fk : ℕ → ℂ → ℂ := fun k w => w ^ e * (d k * w ^ (g k)) with hfk_def
  have hfcont : ∀ k, ContinuousOn (fk k) (sphere (0 : ℂ) R) := by
    intro k
    rw [hfk_def]
    apply ContinuousOn.mul
    · exact (continuousOn_zpow₀ e).mono (fun w hw => by
        rw [mem_sphere_zero_iff_norm] at hw
        rintro rfl
        simp at hw
        linarith)
    · exact continuousOn_const.mul ((continuousOn_zpow₀ (g k)).mono (fun w hw => by
        rw [mem_sphere_zero_iff_norm] at hw
        rintro rfl
        simp at hw
        linarith))
  have hbound : ∀ k w, ‖w‖ = R → ‖fk k w‖ = R ^ e * (‖d k‖ * R ^ (g k)) := by
    intro k w hw
    rw [hfk_def]
    dsimp only
    rw [norm_mul, norm_zpow, hw, norm_mul, norm_zpow, hw]
  have hsum2 : Summable (fun k => R ^ e * (‖d k‖ * R ^ (g k))) := hd.mul_left _
  have htu : TendstoUniformlyOn (fun N => fun w => ∑ k ∈ Finset.range N, fk k w)
      (fun w => ∑' k, fk k w) atTop (sphere (0 : ℂ) R) := by
    apply tendstoUniformlyOn_tsum_nat (f := fk) hsum2
    intro k w hw
    rw [mem_sphere_zero_iff_norm] at hw
    exact (hbound k w hw).le
  have hcont : ∀ᶠ N in atTop,
      ContinuousOn (fun w => ∑ k ∈ Finset.range N, fk k w) (sphere (0 : ℂ) R) := by
    filter_upwards with N
    exact continuousOn_finsetSum _ fun k _ => hfcont k
  have htend := TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn hR.le hcont htu
  have hgeq : (fun w => ∑' k, fk k w) = fun w => w ^ e * ∑' k, d k * w ^ (g k) := by
    funext w
    rw [hfk_def]
    dsimp only
    rw [tsum_mul_left]
  rw [hgeq] at htend
  have hrhs : ∀ N : ℕ, (∮ w in C(0, R), (∑ k ∈ Finset.range N, fk k w)) =
      ∑ k ∈ Finset.range N, ∮ w in C(0, R), fk k w :=
    fun N => circleIntegral_finsetSum (Finset.range N) fk 0 hR.le (fun k _ => hfcont k)
  simp only [hrhs] at htend
  have hnormbound : ∀ k, ‖∮ w in C(0, R), fk k w‖ ≤
      2 * Real.pi * R * (R ^ e * (‖d k‖ * R ^ (g k))) := by
    intro k
    have := circleIntegral.norm_integral_le_of_norm_le_const hR.le
      (f := fk k) (C := R ^ e * (‖d k‖ * R ^ (g k))) (fun w hw => (hbound k w (by
        rw [mem_sphere_zero_iff_norm] at hw; exact hw)).le)
    linarith
  have hcompsum : Summable (fun k => ‖∮ w in C(0, R), fk k w‖) := by
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) hnormbound
    exact hsum2.mul_left _
  have hsummable : Summable (fun k => ∮ w in C(0, R), fk k w) := hcompsum.of_norm
  have hlim1 := hsummable.hasSum.tendsto_sum_nat
  have heq := tendsto_nhds_unique hlim1 htend
  rw [← heq]
  refine tsum_congr fun k => ?_
  rw [hfk_def]
  dsimp only
  rw [show (fun w : ℂ => w ^ e * (d k * w ^ (g k))) =
      fun w => d k • (w ^ e * w ^ (g k)) by
    funext w; rw [smul_eq_mul]; ring]
  rw [circleIntegral.integral_smul]
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro w hw
  rw [mem_sphere_zero_iff_norm] at hw
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; linarith
  dsimp only
  rw [zpow_add₀ hw0]

/-- The one-sided series `∑ₖ d_k w^{g k}` is continuous on the circle, by the same uniform
convergence used for term-by-term integration. -/
theorem continuousOn_tsum_nat_zpow (d : ℕ → ℂ) (g : ℕ → ℤ) (R : ℝ) (hR : 0 < R)
    (hd : Summable (fun k : ℕ => ‖d k‖ * R ^ (g k))) :
    ContinuousOn (fun w => ∑' k : ℕ, d k * w ^ (g k)) (sphere (0 : ℂ) R) := by
  have hfcont : ∀ k, ContinuousOn (fun w => d k * w ^ (g k)) (sphere (0 : ℂ) R) := by
    intro k
    exact continuousOn_const.mul ((continuousOn_zpow₀ (g k)).mono (fun w hw => by
      rw [mem_sphere_zero_iff_norm] at hw
      rintro rfl
      simp at hw
      linarith))
  have hbound : ∀ k w, ‖w‖ = R → ‖d k * w ^ (g k)‖ ≤ ‖d k‖ * R ^ (g k) := by
    intro k w hw
    rw [norm_mul, norm_zpow, hw]
  have htu : TendstoUniformlyOn (fun N => fun w => ∑ k ∈ Finset.range N, d k * w ^ (g k))
      (fun w => ∑' k, d k * w ^ (g k)) atTop (sphere (0 : ℂ) R) := by
    apply tendstoUniformlyOn_tsum_nat (f := fun k w => d k * w ^ (g k)) hd
    intro k w hw
    rw [mem_sphere_zero_iff_norm] at hw
    exact hbound k w hw
  refine htu.continuousOn (Filter.Eventually.frequently ?_)
  filter_upwards with N
  exact continuousOn_finsetSum _ fun k _ => hfcont k

/-- **The boundary density.** The two-sided sum of the Laurent coefficients `c`, on (or off) the
circle of radius `R`: the density whose Cauchy-type integral is studied here. -/
def laurentBoundaryValue (c : ℤ → ℂ) (w : ℂ) : ℂ :=
  (∑' k : ℕ, c k * w ^ (k : ℤ)) + ∑' k : ℕ, c (Int.negSucc k) * w ^ (Int.negSucc k)

/-- **The interior Cauchy-type integral**, as an explicit power series in the nonnegative
Laurent coefficients of `c`. -/
def cauchyTypeInterior (c : ℤ → ℂ) (z : ℂ) : ℂ := ∑' k : ℕ, c k * z ^ (k : ℤ)

/-- **The exterior Cauchy-type integral**, as an explicit power series in the negative Laurent
coefficients of `c` (the sign matches the reversed kernel `(z - w)⁻¹`). -/
def cauchyTypeExterior (c : ℤ → ℂ) (z : ℂ) : ℂ :=
  -∑' k : ℕ, c (Int.negSucc k) * z ^ (Int.negSucc k)

section Summability

variable {c : ℤ → ℂ} {R : ℝ}

/-- The nonnegative part of an absolutely summable two-sided Laurent series is itself
absolutely summable at radius `R`. -/
theorem summable_norm_nat_of_summable_norm_int
    (hc : Summable (fun k : ℤ => ‖c k‖ * R ^ k)) :
    Summable (fun n : ℕ => ‖c n‖ * R ^ (n : ℤ)) :=
  hc.comp_injective Nat.cast_injective

/-- The negative part of an absolutely summable two-sided Laurent series is itself absolutely
summable at radius `R`. -/
theorem summable_norm_negSucc_of_summable_norm_int
    (hc : Summable (fun k : ℤ => ‖c k‖ * R ^ k)) :
    Summable (fun n : ℕ => ‖c (Int.negSucc n)‖ * R ^ (Int.negSucc n)) :=
  hc.comp_injective (fun a b h => by injection h)

end Summability

/-- The boundary density is continuous on its own circle. -/
theorem continuousOn_laurentBoundaryValue {c : ℤ → ℂ} {R : ℝ} (hR : 0 < R)
    (hc : Summable (fun k : ℤ => ‖c k‖ * R ^ k)) :
    ContinuousOn (laurentBoundaryValue c) (sphere (0 : ℂ) R) :=
  (continuousOn_tsum_nat_zpow (fun n => c n) Nat.cast R hR
      (summable_norm_nat_of_summable_norm_int hc)).add
    (continuousOn_tsum_nat_zpow (fun n => c (Int.negSucc n)) Int.negSucc R hR
      (summable_norm_negSucc_of_summable_norm_int hc))

/-- **The Laurent coefficients of the boundary density recover `c`.** Term-by-term circle
integration against each of the two one-sided series, followed by the elementary evaluation
`∮ w^m dw = 2πi · [m = -1]` (`Complex.circleIntegral_zpow_eq`), picks out exactly the coefficient
`c n` regardless of the sign of `n`. -/
theorem circleLaurentCoeff_laurentBoundaryValue {c : ℤ → ℂ} {R : ℝ} (hR : 0 < R)
    (hc : Summable (fun k : ℤ => ‖c k‖ * R ^ k)) (n : ℤ) :
    circleLaurentCoeff (laurentBoundaryValue c) R n = c n := by
  have hcpos := summable_norm_nat_of_summable_norm_int hc
  have hcneg := summable_norm_negSucc_of_summable_norm_int hc
  have hcont1 : ContinuousOn (fun w => ∑' k : ℕ, c k * w ^ (k : ℤ)) (sphere (0 : ℂ) R) :=
    continuousOn_tsum_nat_zpow (fun n => c n) Nat.cast R hR hcpos
  have hcont2 : ContinuousOn (fun w => ∑' k : ℕ, c (Int.negSucc k) * w ^ (Int.negSucc k))
      (sphere (0 : ℂ) R) :=
    continuousOn_tsum_nat_zpow (fun n => c (Int.negSucc n)) Int.negSucc R hR hcneg
  have hci1 : CircleIntegrable (fun w => (w : ℂ) ^ (-n - 1) *
      ∑' k : ℕ, c k * w ^ (k : ℤ)) 0 R :=
    (((continuousOn_zpow₀ (-n - 1)).mono (fun w hw => by
      rw [mem_sphere_zero_iff_norm] at hw; rintro rfl; simp at hw; linarith)).mul
      hcont1).circleIntegrable hR.le
  have hci2 : CircleIntegrable (fun w => (w : ℂ) ^ (-n - 1) *
      ∑' k : ℕ, c (Int.negSucc k) * w ^ (Int.negSucc k)) 0 R :=
    (((continuousOn_zpow₀ (-n - 1)).mono (fun w hw => by
      rw [mem_sphere_zero_iff_norm] at hw; rintro rfl; simp at hw; linarith)).mul
      hcont2).circleIntegrable hR.le
  unfold circleLaurentCoeff laurentBoundaryValue
  simp only [smul_eq_mul, mul_add]
  rw [circleIntegral.integral_add hci1 hci2,
    circleIntegral_zpow_mul_tsum_zpow_eq (fun k => c k) Nat.cast R hR hcpos (-n - 1),
    circleIntegral_zpow_mul_tsum_zpow_eq (fun k => c (Int.negSucc k)) Int.negSucc R hR hcneg
      (-n - 1)]
  by_cases hn : (0 : ℤ) ≤ n
  · have hk1 : (∑' k : ℕ, c k * ∮ w in C(0, R), w ^ (-n - 1 + (k : ℤ))) =
        c n.toNat * (2 * π * I) := by
      rw [tsum_eq_single n.toNat (fun k hk => by
        rw [circleIntegral_zpow_eq R hR]
        split_ifs with h
        · exfalso; exact hk (by omega)
        · rw [mul_zero])]
      rw [circleIntegral_zpow_eq R hR]
      split_ifs with h
      · rfl
      · exact absurd (by omega : -n - 1 + (n.toNat : ℤ) = -1) h
    have hk2 : (∑' k : ℕ, c (Int.negSucc k) *
        ∮ w in C(0, R), w ^ (-n - 1 + Int.negSucc k)) = 0 := by
      have hz : ∀ k : ℕ,
          c (Int.negSucc k) * ∮ w in C(0, R), w ^ (-n - 1 + Int.negSucc k) = 0 := fun k => by
        rw [circleIntegral_zpow_eq R hR]
        split_ifs with h
        · exact absurd h (by omega)
        · rw [mul_zero]
      rw [tsum_congr hz, tsum_zero]
    rw [hk1, hk2, add_zero, show n.toNat = n by omega]
    field_simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = Int.negSucc m := ⟨(-n - 1).toNat, by omega⟩
    have hk1 : (∑' k : ℕ, c k * ∮ w in C(0, R), w ^ (-Int.negSucc m - 1 + (k : ℤ))) = 0 := by
      have hz : ∀ k : ℕ,
          c k * ∮ w in C(0, R), w ^ (-Int.negSucc m - 1 + (k : ℤ)) = 0 := fun k => by
        rw [circleIntegral_zpow_eq R hR]
        split_ifs with h
        · exact absurd h (by omega)
        · rw [mul_zero]
      rw [tsum_congr hz, tsum_zero]
    have hk2 : (∑' k : ℕ, c (Int.negSucc k) *
        ∮ w in C(0, R), w ^ (-Int.negSucc m - 1 + Int.negSucc k)) =
        c (Int.negSucc m) * (2 * π * I) := by
      rw [tsum_eq_single m (fun k hk => by
        rw [circleIntegral_zpow_eq R hR]
        split_ifs with h
        · exact absurd h (by omega)
        · rw [mul_zero])]
      rw [circleIntegral_zpow_eq R hR]
      split_ifs with h
      · rfl
      · exact absurd (by omega : -Int.negSucc m - 1 + Int.negSucc m = -1) h
    rw [hk1, zero_add, hk2]
    field_simp

/-- The interior Cauchy-type power series agrees with the Cauchy-type contour integral of the
boundary density, for `z` strictly inside the circle. -/
theorem cauchyTypeInterior_eq_circleIntegral {c : ℤ → ℂ} {R : ℝ} (hR : 0 < R)
    (hc : Summable (fun k : ℤ => ‖c k‖ * R ^ k)) {z : ℂ} (hz : ‖z‖ < R) :
    cauchyTypeInterior c z =
      (2 * Real.pi * I : ℂ)⁻¹ * ∮ w in C(0, R), (w - z)⁻¹ * laurentBoundaryValue c w := by
  have hci : CircleIntegrable (laurentBoundaryValue c) 0 R :=
    (continuousOn_laurentBoundaryValue hR hc).circleIntegrable hR.le
  have h := hasSum_circleLaurentCoeff_nat (f := laurentBoundaryValue c) hci hz
  simp only [smul_eq_mul, circleLaurentCoeff_laurentBoundaryValue hR hc] at h
  rw [cauchyTypeInterior, ← h.tsum_eq]
  exact tsum_congr fun k => mul_comm _ _

/-- The exterior Cauchy-type power series agrees with the Cauchy-type contour integral of the
boundary density, for `z` strictly outside the circle. -/
theorem cauchyTypeExterior_eq_circleIntegral {c : ℤ → ℂ} {R : ℝ} (hR : 0 < R)
    (hc : Summable (fun k : ℤ => ‖c k‖ * R ^ k)) {z : ℂ} (hz : R < ‖z‖) :
    cauchyTypeExterior c z =
      (2 * Real.pi * I : ℂ)⁻¹ * ∮ w in C(0, R), (w - z)⁻¹ * laurentBoundaryValue c w := by
  have h := hasSum_circleLaurentCoeff_negSucc (f := laurentBoundaryValue c) hR.le
    (continuousOn_laurentBoundaryValue hR hc) hz
  simp only [smul_eq_mul, circleLaurentCoeff_laurentBoundaryValue hR hc] at h
  have hsum : (∑' n : ℕ, z ^ (Int.negSucc n) * c (Int.negSucc n)) =
      (2 * Real.pi * I : ℂ)⁻¹ * ∮ w in C(0, R), (z - w)⁻¹ * laurentBoundaryValue c w := h.tsum_eq
  have hflip : (∮ w in C(0, R), (z - w)⁻¹ * laurentBoundaryValue c w) =
      -(∮ w in C(0, R), (w - z)⁻¹ * laurentBoundaryValue c w) := by
    calc
      _ = ∮ w in C(0, R), -((w - z)⁻¹ * laurentBoundaryValue c w) := by
        congr 1; funext w; rw [← neg_sub w z, inv_neg, neg_mul]
      _ = _ := by simp only [circleIntegral, smul_neg, intervalIntegral.integral_neg]
  rw [cauchyTypeExterior,
    show (∑' k : ℕ, c (Int.negSucc k) * z ^ (Int.negSucc k)) =
      ∑' k : ℕ, z ^ (Int.negSucc k) * c (Int.negSucc k) from tsum_congr fun k => mul_comm _ _,
    hsum, hflip]
  ring

/-- **The Sokhotski–Plemelj jump relation.** The natural continuations to the boundary of the
interior and exterior Cauchy-type integrals — meaningful as such precisely when `c` is
absolutely summable at radius `R` and `‖t‖ = R`, by `cauchyTypeInterior_eq_circleIntegral` and
`cauchyTypeExterior_eq_circleIntegral` — differ by the boundary density itself. -/
theorem cauchyTypeInterior_sub_cauchyTypeExterior (c : ℤ → ℂ) (t : ℂ) :
    cauchyTypeInterior c t - cauchyTypeExterior c t = laurentBoundaryValue c t := by
  unfold cauchyTypeInterior cauchyTypeExterior laurentBoundaryValue
  ring

end Complex

end
