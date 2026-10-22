import Saw38a.Spec

/-!
# Statements, order-26 form (bodies `sorry`; not proved in this tree)

* `bridgeCount_le_autCount` (Theorem 4.1) and `autCount_le` (Lemma 5.1, all weights positive): any valid certificate
  bounds the bridges.
* `connective_constant_exists`: the connective constant exists (Fekete).
* `connective_constant_le_of_cert`: a valid certificate of ratio at most `num / den` gives `μ ≤ num / den`, under the
  Hammersley-Welsh inequality `HW`.
* `cert_exists`: the certificate of the paper (from the data modules: native_decide shards plus the checker's
  soundness). This file states it for a certificate of order 26 (K = 26,
  λ = 2725816588621027200 / 1024176292618053632) and is not used by the proof; the proved statements are
  those of `Statements28f.lean` (K = 28, λ = 5100683462145913 / 1917628724674902).
* `hw`: the Hammersley-Welsh inequality.
-/

namespace Saw38a

open Filter Topology

/-- Theorem 4.1: for a valid certificate, `b_n` is at most the number of automaton paths of length `n` from the start
state. -/
theorem bridgeCount_le_autCount (c : Cert) {K : ℕ} (hc : c.Valid K) (n : ℕ) :
    bridgeCount n ≤ c.autCount n := by
  sorry

/-- Lemma 5.1 (all weights positive): the automaton paths of length `n` from the start state number at most
`V_{S_st} (num/den)^n`. -/
theorem autCount_le (c : Cert) {K num den : ℕ} (hc : c.Valid K) (hr : c.RatioLE num den) (hden : 0 < den)
    (n : ℕ) : (c.autCount n : ℝ) ≤ c.V c.start * ((num : ℝ) / den) ^ n := by
  sorry

/-- The connective constant `μ = lim c_n^{1/n}` exists. -/
theorem connective_constant_exists :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) := by
  sorry

/-- Bridges grow at most like `(num/den)^n` when a valid certificate of ratio at most `num / den` exists. -/
theorem bridge_bound_of_cert (c : Cert) {K num den : ℕ} (hc : c.Valid K) (hr : c.RatioLE num den)
    (hden : 0 < den) : ∃ C : ℝ, ∀ n : ℕ, (bridgeCount n : ℝ) ≤ C * ((num : ℝ) / den) ^ n := by
  sorry

/-- A valid certificate of ratio at most `num / den` bounds the connective constant (under `HW`). -/
theorem connective_constant_le_of_cert (hHW : HW) (c : Cert) {K num den : ℕ} (hc : c.Valid K)
    (hr : c.RatioLE num den) (hden : 0 < den) :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧ μ ≤ (num : ℝ) / den := by
  sorry

/-- A certificate of order 26 (not proved in this tree). -/
theorem cert_exists : ∃ c : Cert, c.Valid 26 ∧ c.RatioLE 2725816588621027200 1024176292618053632 := by
  sorry

/-- Unconditional: `b_n ≤ C λ^n` for the paper's `λ`. -/
theorem bridge_bound : ∃ C : ℝ, ∀ n : ℕ,
    (bridgeCount n : ℝ) ≤ C * ((2725816588621027200 : ℝ) / 1024176292618053632) ^ n := by
  sorry

/-- Main theorem under `HW`: `μ(ℤ²) ≤ 2725816588621027200 / 1024176292618053632 < 2.6614721`. -/
theorem connective_constant_le (hHW : HW) :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧
      μ ≤ (2725816588621027200 : ℝ) / 1024176292618053632 ∧ μ < 2.6614721 := by
  sorry

/-- The Hammersley-Welsh inequality. -/
theorem hw : HW := by
  sorry

end Saw38a
