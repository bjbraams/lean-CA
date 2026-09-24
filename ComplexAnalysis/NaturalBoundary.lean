/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A natural boundary: the lacunary series `∑ z ^ (2 ^ n)`

The power series `∑ z ^ (2 ^ n)` converges on the unit disc to a holomorphic function
`Complex.lacunary`. Along the radius through a `2 ^ k`-th root of unity `ζ` the values
`lacunary (r * ζ)` have real part at least `N * r ^ (2 ^ (N + k)) - k` for every `N`, which
tends to infinity as `r → 1`. Since these roots of unity are dense in the circle, `lacunary` is
unbounded near every point of the unit circle: the circle is a **natural boundary**, and no
continuous extension across any boundary point exists.

## Main results

* `Complex.differentiableOn_lacunary`: holomorphy on the disc.
* `Complex.exists_norm_lacunary_gt`: unboundedness near every boundary point.
* `Complex.not_exists_continuousOn_extension_lacunary`: no continuous extension.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Exercise IX.1.
* L. V. Ahlfors, *Complex Analysis*, Chapter 8, Section 1.2.
-/

@[expose] public noncomputable section

open Set Metric Filter Function
open scoped Topology Real

namespace Complex

/-- The lacunary series `∑ z ^ (2 ^ n)`. -/
def lacunary (z : ℂ) : ℂ := ∑' n : ℕ, z ^ (2 ^ n)

/-- On the closed unit disc, the dyadic lacunary monomial is bounded in norm by the corresponding
ordinary geometric term. -/
theorem norm_pow_two_pow_le {z : ℂ} (hz : ‖z‖ ≤ 1) (n : ℕ) : ‖z ^ (2 ^ n)‖ ≤ ‖z‖ ^ n := by
  rw [norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) hz Nat.lt_two_pow_self.le

/-- The dyadic lacunary series is summable at every point of the open unit disc. -/
theorem summable_lacunary {z : ℂ} (hz : ‖z‖ < 1) : Summable fun n : ℕ => z ^ (2 ^ n) :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hz)
    (norm_pow_two_pow_le hz.le)

/-- The lacunary series is holomorphic on the unit disc. -/
theorem differentiableOn_lacunary : DifferentiableOn ℂ lacunary (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz
  set r : ℝ := (‖z‖ + 1) / 2 with hr_def
  have hr1 : r < 1 := by rw [hr_def]; linarith
  have hr0 : 0 ≤ r := by rw [hr_def]; linarith [norm_nonneg z]
  have hzr : z ∈ ball 0 r := by
    rw [mem_ball_zero_iff, hr_def]
    linarith
  have hF : ∀ n : ℕ, DifferentiableOn ℂ (fun w : ℂ => w ^ (2 ^ n)) (ball 0 r) := fun n => by
    fun_prop
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, w ^ (2 ^ n)) (ball 0 r) := by
    refine differentiableOn_tsum_of_summable_norm
      (summable_geometric_of_lt_one hr0 hr1) hF isOpen_ball fun n w hw => ?_
    rw [mem_ball_zero_iff] at hw
    calc ‖w ^ (2 ^ n)‖ ≤ ‖w‖ ^ n := norm_pow_two_pow_le (hw.le.trans hr1.le) n
      _ ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg _) hw.le n
  exact (hdiff.differentiableAt (isOpen_ball.mem_nhds hzr)).differentiableWithinAt

/-- Along the radius through a `2 ^ k`-th root of unity, the real part of the lacunary series
is at least `N * r ^ (2 ^ (N + k)) - k`. -/
theorem le_re_lacunary_mul_rootOfUnity {ζ : ℂ} {k : ℕ} (hζ : ζ ^ (2 ^ k) = 1) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    N * r ^ (2 ^ (N + k)) - k ≤ (lacunary (r * ζ)).re := by
  have hζ1 : ‖ζ‖ = 1 := by
    have := congrArg norm hζ
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by positivity)).mp this
  have hz : ‖(r : ℂ) * ζ‖ < 1 := by
    rw [norm_mul, hζ1, mul_one, norm_real, Real.norm_of_nonneg hr0]
    exact hr1
  have hsum := summable_lacunary hz
  -- split off the first `k` terms
  have hsplit := hsum.sum_add_tsum_nat_add k
  rw [lacunary, ← hsplit]
  -- the tail is real
  have htail : ∀ n : ℕ, ((r : ℂ) * ζ) ^ (2 ^ (n + k)) = ((r ^ (2 ^ (n + k)) : ℝ) : ℂ) := by
    intro n
    have hζn : ζ ^ (2 ^ (n + k)) = 1 := by rw [pow_add, mul_comm, pow_mul, hζ, one_pow]
    rw [mul_pow, hζn, mul_one, ofReal_pow]
  have hreal : ∑' n : ℕ, ((r : ℂ) * ζ) ^ (2 ^ (n + k)) =
      ((∑' n : ℕ, r ^ (2 ^ (n + k)) : ℝ) : ℂ) := by
    rw [ofReal_tsum]
    exact tsum_congr htail
  rw [add_re, hreal, ofReal_re]
  -- the head has real part at least `-k`
  have hhead : -(k : ℝ) ≤ (∑ n ∈ Finset.range k, ((r : ℂ) * ζ) ^ (2 ^ n)).re := by
    rw [re_sum]
    calc -(k : ℝ) = ∑ _n ∈ Finset.range k, (-1 : ℝ) := by simp
      _ ≤ ∑ n ∈ Finset.range k, (((r : ℂ) * ζ) ^ (2 ^ n)).re := by
          refine Finset.sum_le_sum fun n _ => ?_
          have h1 : |(((r : ℂ) * ζ) ^ (2 ^ n)).re| ≤ 1 := by
            refine (abs_re_le_norm _).trans ?_
            rw [norm_pow]
            exact pow_le_one₀ (norm_nonneg _) hz.le
          linarith [neg_abs_le (((r : ℂ) * ζ) ^ (2 ^ n)).re]
  -- the tail is at least `N * r ^ (2 ^ (N + k))`
  have htail_summable : Summable fun n : ℕ => r ^ (2 ^ (n + k)) := by
    have := (summable_geometric_of_lt_one hr0 hr1).comp_injective (add_left_injective k)
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) this
    exact pow_le_pow_of_le_one hr0 hr1.le Nat.lt_two_pow_self.le
  have hN : (N : ℝ) * r ^ (2 ^ (N + k)) ≤ ∑' n : ℕ, r ^ (2 ^ (n + k)) := by
    calc (N : ℝ) * r ^ (2 ^ (N + k)) = ∑ _n ∈ Finset.range N, r ^ (2 ^ (N + k)) := by simp
      _ ≤ ∑ n ∈ Finset.range N, r ^ (2 ^ (n + k)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          refine pow_le_pow_of_le_one hr0 hr1.le ?_
          exact Nat.pow_le_pow_right two_pos (by linarith [Finset.mem_range.mp hn])
      _ ≤ ∑' n : ℕ, r ^ (2 ^ (n + k)) :=
          htail_summable.sum_le_tsum _ (fun n _ => by positivity)
  linarith

/-- Every point of the unit circle is close to a `2 ^ k`-th root of unity. -/
theorem exists_pow_two_pow_eq_one_near {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (ζ : ℂ), ζ ^ (2 ^ k) = 1 ∧ ‖ζ - ζ₀‖ < ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε Real.two_pi_pos)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hk' : 2 * π / 2 ^ k < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [lt_div_iff₀ Real.two_pi_pos] at hk
    calc 2 * π = 2 * π * ((1 / 2) ^ k * 2 ^ k) := by
          rw [one_div, inv_pow, inv_mul_cancel₀ (by positivity), mul_one]
      _ = 2 * π * (1 / 2) ^ k * 2 ^ k := by ring
      _ < ε * 2 ^ k := by
          rw [mul_comm (2 * π) ((1 / 2 : ℝ) ^ k)]
          exact mul_lt_mul_of_pos_right hk (by positivity)
  set θ : ℝ := arg ζ₀ with hθ_def
  set m : ℤ := ⌊θ * 2 ^ k / (2 * π)⌋ with hm_def
  set φ : ℝ := 2 * π * m / 2 ^ k with hφ_def
  refine ⟨k, exp (φ * I), ?_, ?_⟩
  · rw [← exp_nat_mul, hφ_def]
    have : ((2 ^ k : ℕ) : ℂ) * (((2 * π * m / 2 ^ k : ℝ) : ℂ) * I) = m * (2 * π * I) := by
      push_cast
      field_simp
    rw [this, exp_int_mul_two_pi_mul_I]
  · have hζ₀' : ζ₀ = exp (θ * I) := by
      have := norm_mul_exp_arg_mul_I ζ₀
      rw [hζ₀, ofReal_one, one_mul] at this
      exact this.symm
    have hφθ : |φ - θ| < ε := by
      have h1 : θ * 2 ^ k / (2 * π) - 1 < m := Int.sub_one_lt_floor _
      have h2 : (m : ℝ) ≤ θ * 2 ^ k / (2 * π) := Int.floor_le _
      have hpos : (0 : ℝ) < 2 ^ k := by positivity
      rw [abs_lt]
      constructor
      · rw [hφ_def]
        have : φ - θ = (2 * π / 2 ^ k) * (m - θ * 2 ^ k / (2 * π)) := by
          rw [hφ_def]
          field_simp
        rw [← hφ_def, this]
        have h3 : -1 < (m : ℝ) - θ * 2 ^ k / (2 * π) := by linarith
        have h4 : 0 < 2 * π / 2 ^ k := by positivity
        nlinarith
      · rw [hφ_def]
        have : φ - θ = (2 * π / 2 ^ k) * (m - θ * 2 ^ k / (2 * π)) := by
          rw [hφ_def]
          field_simp
        rw [← hφ_def, this]
        have h3 : (m : ℝ) - θ * 2 ^ k / (2 * π) ≤ 0 := by linarith
        have h4 : 0 < 2 * π / 2 ^ k := by positivity
        nlinarith
    rw [hζ₀']
    have : exp (φ * I) - exp (θ * I) = exp (θ * I) * (exp (I * ((φ - θ : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← exp_add]
      congr 2
      push_cast
      ring
    rw [this, norm_mul, norm_exp_ofReal_mul_I, one_mul]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans_lt (by rwa [Real.norm_eq_abs])

/-- **The unit circle is a natural boundary.** The lacunary series is unbounded on every
neighborhood of every point of the unit circle. -/
theorem exists_norm_lacunary_gt {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) {ε : ℝ} (hε : 0 < ε) (M : ℝ) :
    ∃ z ∈ ball ζ₀ ε ∩ ball 0 1, M < ‖lacunary z‖ := by
  obtain ⟨k, ζ, hζ, hζζ₀⟩ := exists_pow_two_pow_eq_one_near hζ₀ (half_pos hε)
  have hζ1 : ‖ζ‖ = 1 := by
    have := congrArg norm hζ
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by positivity)).mp this
  set N : ℕ := ⌈2 * (M + k)⌉₊ + 1 with hN_def
  have hN : 2 * (M + k) < (N : ℝ) := by
    have h1 := Nat.le_ceil (2 * (M + k))
    have h2 : ((⌈2 * (M + k)⌉₊ + 1 : ℕ) : ℝ) = (⌈2 * (M + k)⌉₊ : ℝ) + 1 := by push_cast; ring
    rw [hN_def, h2]
    linarith
  -- a radius `r` close to `1` with `r ^ (2 ^ (N + k)) ≥ 1 / 2`
  obtain ⟨r, hr, hrpow⟩ : ∃ r ∈ Ioo (max 0 (1 - ε / 2)) 1, (1 / 2 : ℝ) ≤ r ^ (2 ^ (N + k)) := by
    have hcont : ContinuousAt (fun r : ℝ => r ^ (2 ^ (N + k))) 1 := (continuous_pow _).continuousAt
    have hev : ∀ᶠ r in 𝓝 (1 : ℝ), (1 / 2 : ℝ) ≤ r ^ (2 ^ (N + k)) := by
      have h1 : (1 / 2 : ℝ) < (1 : ℝ) ^ (2 ^ (N + k)) := by norm_num
      exact (hcont.eventually (lt_mem_nhds h1)).mono fun r hr => hr.le
    have hmax : max 0 (1 - ε / 2) < 1 := by
      rw [max_lt_iff]
      constructor <;> linarith
    have hIoo : Ioo (max 0 (1 - ε / 2)) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT hmax
    obtain ⟨r, hr1, hr2⟩ := Filter.nonempty_of_mem (inter_mem hIoo (nhdsWithin_le_nhds hev))
    exact ⟨r, hr1, hr2⟩
  have hr0 : 0 ≤ r := (le_max_left _ _).trans hr.1.le
  have hr1 : r < 1 := hr.2
  have hrε : 1 - r < ε / 2 := by linarith [(le_max_right 0 (1 - ε / 2)).trans_lt hr.1]
  refine ⟨(r : ℂ) * ζ, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    calc ‖(r : ℂ) * ζ - ζ₀‖ = ‖((r : ℂ) - 1) * ζ + (ζ - ζ₀)‖ := by ring_nf
      _ ≤ ‖((r : ℂ) - 1) * ζ‖ + ‖ζ - ζ₀‖ := norm_add_le _ _
      _ = (1 - r) + ‖ζ - ζ₀‖ := by
          rw [norm_mul, hζ1, mul_one, ← ofReal_one, ← ofReal_sub, norm_real,
            Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]
      _ < ε / 2 + ε / 2 := add_lt_add hrε hζζ₀
      _ = ε := by ring
  · rw [mem_ball_zero_iff, norm_mul, hζ1, mul_one, norm_real, Real.norm_of_nonneg hr0]
    exact hr1
  · have hre := le_re_lacunary_mul_rootOfUnity hζ hr0 hr1 N
    have h1 : (N : ℝ) * r ^ (2 ^ (N + k)) ≥ N / 2 := by
      have : (N : ℝ) * (1 / 2) ≤ N * r ^ (2 ^ (N + k)) :=
        mul_le_mul_of_nonneg_left hrpow (Nat.cast_nonneg N)
      linarith
    calc M < N / 2 - k := by linarith
      _ ≤ (lacunary ((r : ℂ) * ζ)).re := by linarith
      _ ≤ ‖lacunary ((r : ℂ) * ζ)‖ := re_le_norm _

/-- **No continuous extension across the circle.** The lacunary series has no continuous
extension to any ball around a point of the unit circle. -/
theorem not_exists_continuousOn_extension_lacunary {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) {ε : ℝ}
    (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, ContinuousOn g (ball ζ₀ ε) ∧ EqOn lacunary g (ball ζ₀ ε ∩ ball 0 1) := by
  rintro ⟨g, hg, heq⟩
  have hζ₀ε : ζ₀ ∈ ball ζ₀ ε := mem_ball_self hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.mp (hg ζ₀ hζ₀ε) 1 one_pos
  obtain ⟨z, hz, hM⟩ := exists_norm_lacunary_gt hζ₀ (lt_min hδ hε) (‖g ζ₀‖ + 1)
  have hzε : z ∈ ball ζ₀ ε := ball_subset_ball (min_le_right _ _) hz.1
  have hzδ : dist z ζ₀ < δ := (mem_ball.mp hz.1).trans_le (min_le_left _ _)
  have h1 : ‖g z‖ < ‖g ζ₀‖ + 1 := by
    have := hδg hzε hzδ
    rw [dist_eq_norm] at this
    linarith [norm_le_norm_add_norm_sub' (g z) (g ζ₀)]
  rw [heq ⟨hzε, hz.2⟩] at hM
  linarith

end Complex

end
