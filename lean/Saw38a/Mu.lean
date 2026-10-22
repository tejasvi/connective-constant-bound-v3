import Saw38a.Fekete

/-!
# `μ ≤ λ` from a bridge bound and the Hammersley-Welsh inequality

If `b_n ≤ C λ^n` for all `n` (the conclusion of `bridge_bound_of_cert` with `λ = num / den`) and `HW` holds
(`c_n ≤ f(n) b_{n+1}`, `log f(n) / n → 0`), then for `n ≥ 1`

  `log c_n / n ≤ log f(n) / n + log C / n + log λ + log λ / n`,

whose right side tends to `log λ`, while the left side tends to `log μ` (`tendsto_log_sawCount_div`). So `μ ≤ λ`.
All the logarithms are of positive numbers: `c_n ≥ 1` forces `f(n) > 0` and `C λ^{n+1} > 0`.

* `connMu_le_of_bridge_bound`: `μ ≤ λ` for the limit `μ = connMu` of `c_n ^ (1/n)`.
* `connective_constant_le_of_bridge_bound`: the variant from `HW` and the bridge bound directly.
* `connective_constant_le_of_cert'`: the statement of `connective_constant_le_of_cert`, with the conclusion of
  `bridge_bound_of_cert` as the extra hypothesis `hb`.
* `connective_constant_le_of_cert_of_bridge_bound`: the same with `bridge_bound_of_cert` itself as a hypothesis.
* `connective_constant_le'`: the statement of `connective_constant_le` (k26f constants), with the conclusion of
  `bridge_bound` as the extra hypothesis `hb`.
-/

namespace Saw38a

open Filter Topology

/-- `μ ≤ λ` from `HW` and `b_n ≤ C λ^n`. -/
theorem connMu_le_of_bridge_bound (hHW : HW) {lam C : ℝ} (hlam : 0 ≤ lam)
    (hb : ∀ n : ℕ, (bridgeCount n : ℝ) ≤ C * lam ^ n) : connMu ≤ lam := by
  obtain ⟨f, hf, hcf⟩ := hHW
  have hfpos : ∀ n, 0 < f n := by
    intro n
    by_contra h
    have h' : f n ≤ 0 := not_lt.1 h
    have hb0 : (0 : ℝ) ≤ bridgeCount (n + 1) := Nat.cast_nonneg _
    have h1 : f n * bridgeCount (n + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h' hb0
    linarith [one_le_sawCount_real n, hcf n]
  have hP : ∀ n : ℕ, (sawCount n : ℝ) ≤ f n * (C * lam ^ (n + 1)) := fun n =>
    (hcf n).trans (mul_le_mul_of_nonneg_left (hb (n + 1)) (hfpos n).le)
  have hClam : 0 < C * lam ^ (0 + 1) := by
    have h0 : 0 < f 0 * (C * lam ^ (0 + 1)) :=
      lt_of_lt_of_le (by linarith [one_le_sawCount_real 0]) (hP 0)
    exact (mul_pos_iff_of_pos_left (hfpos 0)).1 h0
  have hlam_pos : 0 < lam := by
    rcases hlam.lt_or_eq with h | h
    · exact h
    · rw [← h] at hClam
      simp at hClam
  have hC : 0 < C := by
    rw [zero_add, pow_one] at hClam
    exact (mul_pos_iff_of_pos_right hlam_pos).1 hClam
  have hineq : ∀ n : ℕ, 1 ≤ n → Real.log (sawCount n) / n ≤
      Real.log (f n) / n + Real.log C / n + (Real.log lam + Real.log lam / n) := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : Real.log (sawCount n) ≤ Real.log (f n) + Real.log C + (n + 1) * Real.log lam := by
      have h := Real.log_le_log (by exact_mod_cast sawCount_pos n) (hP n)
      rw [Real.log_mul (hfpos n).ne' (by positivity), Real.log_mul hC.ne' (by positivity),
        Real.log_pow] at h
      push_cast at h
      linarith
    have h2 : Real.log (f n) / n + Real.log C / n + (Real.log lam + Real.log lam / n) =
        (Real.log (f n) + Real.log C + (n + 1) * Real.log lam) / n := by
      field_simp
    rw [h2]
    gcongr
  have hlim : Tendsto (fun n : ℕ => Real.log (f n) / n + Real.log C / n +
      (Real.log lam + Real.log lam / n)) atTop (𝓝 (0 + 0 + (Real.log lam + 0))) :=
    (hf.add (tendsto_const_div_atTop_nhds_zero_nat _)).add
      (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _))
  have hle : Real.log connMu ≤ Real.log lam := by
    have h := le_of_tendsto_of_tendsto tendsto_log_sawCount_div hlim (eventually_atTop.2 ⟨1, hineq⟩)
    simpa using h
  exact (Real.log_le_log_iff connMu_pos hlam_pos).1 hle

/-- Variant from `HW` and a bridge bound directly. -/
theorem connective_constant_le_of_bridge_bound (hHW : HW) {lam : ℝ} (hlam : 0 ≤ lam)
    (hb : ∃ C : ℝ, ∀ n : ℕ, (bridgeCount n : ℝ) ≤ C * lam ^ n) :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧ μ ≤ lam := by
  obtain ⟨C, hC⟩ := hb
  exact ⟨connMu, tendsto_connMu, connMu_le_of_bridge_bound hHW hlam hC⟩

set_option linter.unusedVariables false in
/-- The statement of `connective_constant_le_of_cert`, with the conclusion of `bridge_bound_of_cert` as the extra
hypothesis `hb`. -/
theorem connective_constant_le_of_cert' (hHW : HW) (c : Cert) {K num den : ℕ} (hc : c.Valid K)
    (hr : c.RatioLE num den) (hden : 0 < den)
    (hb : ∃ C : ℝ, ∀ n : ℕ, (bridgeCount n : ℝ) ≤ C * ((num : ℝ) / den) ^ n) :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧
      μ ≤ (num : ℝ) / den :=
  connective_constant_le_of_bridge_bound hHW (by positivity) hb

/-- The statement of `connective_constant_le_of_cert`, with `bridge_bound_of_cert` (Theorem 4.1 and Lemma 5.1) as the
hypothesis `hbb`. -/
theorem connective_constant_le_of_cert_of_bridge_bound
    (hbb : ∀ (c : Cert) {K num den : ℕ}, c.Valid K → c.RatioLE num den → 0 < den →
      ∃ C : ℝ, ∀ n : ℕ, (bridgeCount n : ℝ) ≤ C * ((num : ℝ) / den) ^ n)
    (hHW : HW) (c : Cert) {K num den : ℕ} (hc : c.Valid K) (hr : c.RatioLE num den) (hden : 0 < den) :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧
      μ ≤ (num : ℝ) / den :=
  connective_constant_le_of_cert' hHW c hc hr hden (hbb c hc hr hden)

/-- The statement of `connective_constant_le` (k26f constants), with the conclusion of `bridge_bound` as the extra
hypothesis `hb`. -/
theorem connective_constant_le' (hHW : HW)
    (hb : ∃ C : ℝ, ∀ n : ℕ,
      (bridgeCount n : ℝ) ≤ C * ((2725816588621027200 : ℝ) / 1024176292618053632) ^ n) :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧
      μ ≤ (2725816588621027200 : ℝ) / 1024176292618053632 ∧ μ < 2.6614721 := by
  obtain ⟨μ, hμ, hle⟩ := connective_constant_le_of_bridge_bound hHW (by positivity) hb
  refine ⟨μ, hμ, hle, lt_of_le_of_lt hle ?_⟩
  norm_num

end Saw38a
