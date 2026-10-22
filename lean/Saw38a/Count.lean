import Saw38a.Spec

/-!
# Lemma 5.1 (all weights positive)

The words of length `n` that the automaton accepts from the start state number at most `V_{S_st} (num/den)^n`.

Proof: let `wcount c k i` be the number of words of length `k` read from state `i`, each accepted word counted with
the weight of the state where it ends. Splitting off the first letter gives
`wcount c (k+1) i = Σ_t wcount c k (entry i t)` (with `0` for the entry `none`), so
`den^k · wcount c k i ≤ num^k · V_i` by induction on `k`. Since all weights are at least `1`, the number of accepted
words is at most `wcount c n start`.
-/

namespace Saw38a

open Finset

namespace T3

variable (c : Cert)

/-- The weight of an optional state (`0` for `none`). -/
def oval (o : Option (Fin c.N)) : ℕ := o.elim 0 c.V

/-- The weighted number of words of length `k` read from state `i`. -/
def wcount (k : ℕ) (i : Fin c.N) : ℕ := ∑ ts : Fin k → Fin 3, oval c (c.run i (List.ofFn ts))

theorem childSum_eq_oval (i : Fin c.N) : c.childSum i = ∑ t : Fin 3, oval c (c.entry i t) := by
  unfold Cert.childSum oval
  refine Finset.sum_congr rfl fun t _ => ?_
  cases c.entry i t <;> rfl

theorem wcount_zero (i : Fin c.N) : wcount c 0 i = c.V i := by
  simp [wcount, Cert.run, oval]

theorem wcount_succ (k : ℕ) (i : Fin c.N) :
    wcount c (k + 1) i = ∑ t : Fin 3, (c.entry i t).elim 0 (wcount c k) := by
  unfold wcount
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin 3).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  cases h : c.entry i t with
  | none => simp [Cert.run, h, oval]
  | some j => simp [Cert.run, h]

theorem wcount_le {num den : ℕ} (hr : c.RatioLE num den) (k : ℕ) :
    ∀ i, den ^ k * wcount c k i ≤ num ^ k * c.V i := by
  induction k with
  | zero => intro i; simp [wcount_zero]
  | succ k ih =>
    intro i
    have h1 : den ^ k * ∑ t : Fin 3, (c.entry i t).elim 0 (wcount c k) ≤ num ^ k * c.childSum i := by
      rw [childSum_eq_oval, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun t _ => ?_
      cases c.entry i t with
      | none => simp [oval]
      | some j => exact ih j
    calc den ^ (k + 1) * wcount c (k + 1) i
        = den * (den ^ k * ∑ t : Fin 3, (c.entry i t).elim 0 (wcount c k)) := by
          rw [wcount_succ, pow_succ]; ring
      _ ≤ den * (num ^ k * c.childSum i) := Nat.mul_le_mul_left _ h1
      _ = num ^ k * (den * c.childSum i) := by ring
      _ ≤ num ^ k * (num * c.V i) := Nat.mul_le_mul_left _ (hr i)
      _ = num ^ (k + 1) * c.V i := by rw [pow_succ]; ring

theorem autCount_le_wcount {K : ℕ} (hc : c.Valid K) (n : ℕ) : c.autCount n ≤ wcount c n c.start := by
  unfold Cert.autCount wcount
  rw [Finset.card_filter]
  refine Finset.sum_le_sum fun ts _ => ?_
  cases h : c.run c.start (List.ofFn ts) with
  | none => simp
  | some j => have := hc.pos j; simp [oval]; omega

end T3

/-- Lemma 5.1 (all weights positive): the automaton paths of length `n` from the start state number at most
`V_{S_st} (num/den)^n`. -/
theorem autCount_le' (c : Cert) {K num den : ℕ} (hc : c.Valid K) (hr : c.RatioLE num den) (hden : 0 < den)
    (n : ℕ) : (c.autCount n : ℝ) ≤ c.V c.start * ((num : ℝ) / den) ^ n := by
  have h1 : (c.autCount n : ℝ) ≤ T3.wcount c n c.start := by exact_mod_cast T3.autCount_le_wcount c hc n
  have h2 : ((den : ℝ) ^ n * T3.wcount c n c.start) ≤ (num : ℝ) ^ n * c.V c.start := by
    exact_mod_cast T3.wcount_le c hr n c.start
  have hd : (0 : ℝ) < (den : ℝ) ^ n := pow_pos (by exact_mod_cast hden) n
  rw [div_pow, mul_div_assoc', le_div_iff₀ hd]
  calc (c.autCount n : ℝ) * (den : ℝ) ^ n ≤ T3.wcount c n c.start * (den : ℝ) ^ n := by gcongr
    _ = (den : ℝ) ^ n * T3.wcount c n c.start := by ring
    _ ≤ (num : ℝ) ^ n * c.V c.start := h2
    _ = c.V c.start * (num : ℝ) ^ n := by ring

end Saw38a
