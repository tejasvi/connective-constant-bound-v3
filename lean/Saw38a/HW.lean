import Saw38a.Fekete

/-!
# The Hammersley-Welsh inequality

`hw' : HW` with `f(n) = (n+1)^(2K+1)`, `K = ⌊√(2n)⌋`.

The proof follows Hammersley and Welsh: a half-plane walk is unfolded into a bridge by reflecting, again and again,
the part after the last time of largest first coordinate; the spans of the successive pieces strictly decrease, so at
most `K` reflections occur. A general self-avoiding walk is split at the first time of smallest first coordinate: the
reversed first part and the second part are half-plane walks. In step-sequence form every reflection flips the
`x`-direction (`e₁ ↔ -e₁`) of a segment of steps, so the result is the original step sequence with the
`x`-direction flipped on a set of steps (a flip pattern). With one `e₁` step put in front it is a bridge of length
`n + 1`.

Instead of the spans (partitions into distinct parts) the encoding records the reflection times, at most `K` for each
part: for a fixed flip pattern the flip is an involution, so the map (flip pattern, bridge) is injective, and the
number of flip patterns is at most `(n+1)^(2K+1)`. This gives `c_n ≤ (n+1)^(2K+1) b_{n+1}`, and
`log((n+1)^(2K+1)) / n → 0`.

* Integer sequences: `flipX b X` is the sequence with the increments of `X` negated where `b` holds; `togB T` toggles
  at the times in `T`. `unfold` is the unfolding of a half-plane walk, `assembly` the case of a general walk.
* Step sequences: `flipS b s` flips the `x`-direction of the steps `j` with `b j`; `wk_flipS` relates it to `flipX`.
* `sawCount_le_mul_bridgeCount`, then `hw'`.
-/

namespace Saw38a

open Finset Filter Topology

namespace HWProof

/-! ### Integer sequences with flipped increments -/

/-- The sequence that starts at `X 0` and whose increments are those of `X`, negated at the times `j` with `b j`. -/
def flipX (b : ℕ → Bool) (X : ℕ → ℤ) (k : ℕ) : ℤ :=
  X 0 + ∑ j ∈ range k, (if b j then -(X (j + 1) - X j) else X (j + 1) - X j)

theorem flipX_zero (b : ℕ → Bool) (X : ℕ → ℤ) : flipX b X 0 = X 0 := by
  simp [flipX]

theorem flipX_succ (b : ℕ → Bool) (X : ℕ → ℤ) (k : ℕ) :
    flipX b X (k + 1) = flipX b X k + (if b k then -(X (k + 1) - X k) else X (k + 1) - X k) := by
  simp only [flipX, Finset.sum_range_succ]
  ring

theorem flipX_sub (b : ℕ → Bool) (X : ℕ → ℤ) (k : ℕ) :
    flipX b X (k + 1) - flipX b X k = if b k then -(X (k + 1) - X k) else X (k + 1) - X k := by
  rw [flipX_succ]
  ring

theorem flipX_false (X : ℕ → ℤ) : flipX (fun _ => false) X = X := by
  funext k
  induction k with
  | zero => simp [flipX_zero]
  | succ k ih =>
    rw [flipX_succ, ih]
    simp

theorem flipX_flipX (b₁ b₂ : ℕ → Bool) (X : ℕ → ℤ) :
    flipX b₂ (flipX b₁ X) = flipX (fun j => xor (b₁ j) (b₂ j)) X := by
  funext k
  induction k with
  | zero => simp [flipX_zero]
  | succ k ih =>
    rw [flipX_succ, ih, flipX_succ (fun j => xor (b₁ j) (b₂ j)), flipX_sub]
    cases h₁ : b₁ k <;> cases h₂ : b₂ k <;> simp

/-- Flipping the increments from time `t` on reflects the sequence after `t` in the value `X t`. -/
theorem flipX_toggle (t : ℕ) (X : ℕ → ℤ) (k : ℕ) :
    flipX (fun j => decide (t ≤ j)) X k = if k ≤ t then X k else 2 * X t - X k := by
  induction k with
  | zero => simp [flipX_zero]
  | succ k ih =>
    rw [flipX_succ, ih]
    by_cases h₁ : k + 1 ≤ t
    · have h₂ : k ≤ t := by omega
      have h₃ : ¬ t ≤ k := by omega
      simp only [h₁, h₂, h₃, ite_true, decide_false, Bool.false_eq_true, ite_false]
      ring
    · by_cases h₂ : k ≤ t
      · have h₄ : k = t := by omega
        subst h₄
        simp only [h₁, le_refl, ite_true, decide_true, ite_false]
        ring
      · have h₃ : t ≤ k := by omega
        simp only [h₁, h₂, h₃, ite_false, decide_true, ite_true]
        ring

/-- Toggles: `togB T j` is the parity of the number of `t ∈ T` with `t ≤ j`. -/
def togB : List ℕ → ℕ → Bool
  | [], _ => false
  | t :: T, j => xor (decide (t ≤ j)) (togB T j)

theorem togB_nil : togB [] = fun _ => false := rfl

theorem togB_single (t : ℕ) : togB [t] = fun j => decide (t ≤ j) := by
  funext j
  simp [togB]

theorem togB_cons (t : ℕ) (T : List ℕ) (j : ℕ) : togB (t :: T) j = xor (decide (t ≤ j)) (togB T j) := rfl

theorem togB_append (T R : List ℕ) (j : ℕ) : togB (T ++ R) j = xor (togB T j) (togB R j) := by
  induction T with
  | nil => simp [togB]
  | cons t T ih => simp [togB, ih]

theorem togB_replicate (r n j : ℕ) (hj : j < n) : togB (List.replicate r n) j = false := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ, togB_cons, ih]
    simp
    omega

/-! ### Extremal times -/

theorem exists_last_argmax (X : ℕ → ℤ) (N : ℕ) :
    ∃ t ≤ N, (∀ k ≤ N, X k ≤ X t) ∧ ∀ k, t < k → k ≤ N → X k < X t := by
  induction N with
  | zero =>
    refine ⟨0, le_rfl, fun k hk => ?_, fun k h₁ h₂ => by omega⟩
    rw [Nat.le_zero.1 hk]
  | succ N ih =>
    obtain ⟨t, htN, hmax, hlast⟩ := ih
    by_cases h : X t ≤ X (N + 1)
    · refine ⟨N + 1, le_rfl, fun k hk => ?_, fun k h₁ h₂ => by omega⟩
      rcases Nat.lt_or_ge k (N + 1) with hk' | hk'
      · exact (hmax k (by omega)).trans h
      · rw [show k = N + 1 by omega]
    · have h' := not_le.1 h
      refine ⟨t, by omega, fun k hk => ?_, fun k h₁ h₂ => ?_⟩
      · rcases Nat.lt_or_ge k (N + 1) with hk' | hk'
        · exact hmax k (by omega)
        · rw [show k = N + 1 by omega]
          exact h'.le
      · rcases Nat.lt_or_ge k (N + 1) with hk' | hk'
        · exact hlast k h₁ (by omega)
        · rw [show k = N + 1 by omega]
          exact h'

theorem exists_last_argmin_tail (X : ℕ → ℤ) {t N : ℕ} (h : t < N) :
    ∃ t₁, t < t₁ ∧ t₁ ≤ N ∧ (∀ k, t < k → k ≤ N → X t₁ ≤ X k) ∧
      ∀ k, t₁ < k → k ≤ N → X t₁ < X k := by
  obtain ⟨j, hj, hmax, hlast⟩ := exists_last_argmax (fun k => -X (t + 1 + k)) (N - t - 1)
  refine ⟨t + 1 + j, by omega, by omega, fun k h₁ h₂ => ?_, fun k h₁ h₂ => ?_⟩
  · have h₃ := hmax (k - (t + 1)) (by omega)
    rw [show t + 1 + (k - (t + 1)) = k by omega] at h₃
    linarith
  · have h₃ := hlast (k - (t + 1)) (by omega) (by omega)
    rw [show t + 1 + (k - (t + 1)) = k by omega] at h₃
    linarith

theorem exists_first_argmin (X : ℕ → ℤ) (n : ℕ) :
    ∃ m ≤ n, (∀ k ≤ n, X m ≤ X k) ∧ ∀ k < m, X m < X k := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, fun k hk => ?_, fun k hk => by omega⟩
    rw [Nat.le_zero.1 hk]
  | succ n ih =>
    obtain ⟨m, hmn, hmin, hfirst⟩ := ih
    by_cases h : X (n + 1) < X m
    · refine ⟨n + 1, le_rfl, fun k hk => ?_, fun k hk => h.trans_le (hmin k (by omega))⟩
      rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
      · exact h.le.trans (hmin k (by omega))
      · rw [show k = n + 1 by omega]
    · have h' := not_lt.1 h
      refine ⟨m, by omega, fun k hk => ?_, hfirst⟩
      rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
      · exact hmin k (by omega)
      · rw [show k = n + 1 by omega]
        exact h'

/-! ### Unfolding a half-plane walk -/

/-- `(X, Y)` is injective on `[0, N]`. -/
def InjOn2 (X Y : ℕ → ℤ) (N : ℕ) : Prop :=
  ∀ a ≤ N, ∀ b ≤ N, X a = X b → Y a = Y b → a = b

/-- The increments of `X` on `[0, N]` are in `{-1, 0, 1}`. -/
def Lip (X : ℕ → ℤ) (N : ℕ) : Prop := ∀ k < N, |X (k + 1) - X k| ≤ 1

theorem flipX_lip (b : ℕ → Bool) (X : ℕ → ℤ) (N : ℕ) (h : Lip X N) : Lip (flipX b X) N := by
  intro k hk
  rw [flipX_sub]
  split_ifs
  · rw [abs_neg]
    exact h k hk
  · exact h k hk

theorem lip_sub_le (X : ℕ → ℤ) (N : ℕ) (h : Lip X N) : ∀ k ≤ N, X k - X 0 ≤ k := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have h₁ := ih (by omega)
    have h₂ := (abs_le.1 (h k (by omega))).2
    push_cast
    linarith

/-- One reflection after another. The current maximum `X t` is attained last at `t`, and after `t` the values lie in
`(X t - A, X t)`. Reflecting the part after `t` in `X t` moves it above `X t`; the new last maximum is the last
minimum `t₁` of the old part after `t`, and the new bound is `A' = X t - X t₁ < A`. -/
theorem unfold_aux (Y : ℕ → ℤ) (N A : ℕ) : ∀ (X : ℕ → ℤ) (t : ℕ), 1 ≤ A → t ≤ N →
    (∀ k ≤ N, X k ≤ X t) → (∀ k, t < k → k ≤ N → X t - A < X k ∧ X k < X t) → InjOn2 X Y N →
    ∃ T : List ℕ, (∀ τ ∈ T, t ≤ τ ∧ τ < N) ∧ T.length < A ∧
      ((T.length * (T.length + 1) : ℕ) : ℤ) ≤ 2 * (flipX (togB T) X N - X t) ∧
      InjOn2 (flipX (togB T) X) Y N ∧
      ∀ k ≤ N, X k ≤ flipX (togB T) X k ∧ flipX (togB T) X k ≤ flipX (togB T) X N := by
  induction A using Nat.strong_induction_on with
  | _ A ih =>
  intro X t hA htN hmax htail hinj
  rcases Nat.lt_or_ge t N with htN' | htN'
  · obtain ⟨t₁, ht₁, ht₁N, hmin, hlast⟩ := exists_last_argmin_tail X htN'
    have hlt := (htail t₁ ht₁ ht₁N).2
    have hgt := (htail t₁ ht₁ ht₁N).1
    -- the reflected sequence
    have hX₁e : ∀ k, flipX (togB [t]) X k = if k ≤ t then X k else 2 * X t - X k := by
      intro k
      rw [togB_single, flipX_toggle]
    have hX₁t₁ : flipX (togB [t]) X t₁ = 2 * X t - X t₁ := by
      rw [hX₁e, ite_eq_right (by omega)]
    obtain ⟨A', hA'z⟩ : ∃ A' : ℕ, (A' : ℤ) = X t - X t₁ := ⟨(X t - X t₁).toNat, by omega⟩
    have hA'1 : 1 ≤ A' := by omega
    have hA'A : A' < A := by omega
    have hmax₁ : ∀ k ≤ N, flipX (togB [t]) X k ≤ flipX (togB [t]) X t₁ := by
      intro k hk
      rw [hX₁t₁, hX₁e]
      split_ifs with h
      · linarith [hmax k hk]
      · linarith [hmin k (by omega) hk]
    have htail₁ : ∀ k, t₁ < k → k ≤ N →
        flipX (togB [t]) X t₁ - A' < flipX (togB [t]) X k ∧
          flipX (togB [t]) X k < flipX (togB [t]) X t₁ := by
      intro k h₁ h₂
      rw [hX₁t₁, hX₁e, ite_eq_right (by omega)]
      constructor
      · linarith [(htail k (by omega) h₂).2]
      · linarith [hlast k h₁ h₂]
    have hinj₁ : InjOn2 (flipX (togB [t]) X) Y N := by
      intro a ha b hb hab hy
      rw [hX₁e, hX₁e] at hab
      by_cases hat : a ≤ t
      · by_cases hbt : b ≤ t
        · rw [ite_eq_left hat, ite_eq_left hbt] at hab
          exact hinj a ha b hb hab hy
        · rw [ite_eq_left hat, ite_eq_right hbt] at hab
          linarith [hmax a ha, (htail b (by omega) hb).2]
      · by_cases hbt : b ≤ t
        · rw [ite_eq_right hat, ite_eq_left hbt] at hab
          linarith [hmax b hb, (htail a (by omega) ha).2]
        · rw [ite_eq_right hat, ite_eq_right hbt] at hab
          exact hinj a ha b hb (by linarith) hy
    obtain ⟨T₁, hT₁, hlen, hcount, hinj', hbd⟩ :=
      ih A' hA'A (flipX (togB [t]) X) t₁ hA'1 ht₁N hmax₁ htail₁ hinj₁
    have hcomp : flipX (togB T₁) (flipX (togB [t]) X) = flipX (togB (t :: T₁)) X := by
      rw [flipX_flipX]
      congr 1
      funext j
      simp [togB]
    rw [hcomp] at hcount hinj' hbd
    refine ⟨t :: T₁, ?_, ?_, ?_, hinj', ?_⟩
    · intro τ hτ
      rcases List.mem_cons.1 hτ with h | h
      · exact ⟨h ▸ le_rfl, h ▸ htN'⟩
      · have h' := hT₁ τ h
        exact ⟨by omega, h'.2⟩
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      push_cast at hcount ⊢
      have hl : (T₁.length : ℤ) + 1 ≤ A' := by exact_mod_cast hlen
      rw [hX₁t₁] at hcount
      nlinarith
    · intro k hk
      refine ⟨?_, (hbd k hk).2⟩
      have h₁ : X k ≤ flipX (togB [t]) X k := by
        rw [hX₁e]
        split_ifs with h
        · exact le_rfl
        · linarith [(htail k (by omega) hk).2]
      exact h₁.trans (hbd k hk).1
  · have htN'' : t = N := le_antisymm htN htN'
    subst htN''
    refine ⟨[], by simp, by simp; omega, ?_, ?_, ?_⟩
    · simp [togB_nil, flipX_false]
    · rw [togB_nil, flipX_false]
      exact hinj
    · intro k hk
      rw [togB_nil, flipX_false]
      exact ⟨le_rfl, hmax k hk⟩

/-- A half-plane walk (`X 0 ≤ X k`) unfolds into a weak bridge with at most `√(2N)` reflections. -/
theorem unfold (X Y : ℕ → ℤ) (N : ℕ) (hlip : Lip X N) (hinj : InjOn2 X Y N)
    (hhalf : ∀ k ≤ N, X 0 ≤ X k) :
    ∃ T : List ℕ, T.length * (T.length + 1) ≤ 2 * N ∧ (∀ τ ∈ T, τ < N) ∧
      InjOn2 (flipX (togB T) X) Y N ∧
      ∀ k ≤ N, X k ≤ flipX (togB T) X k ∧ flipX (togB T) X k ≤ flipX (togB T) X N := by
  obtain ⟨t, htN, hmax, hlast⟩ := exists_last_argmax X N
  have h0 : X 0 ≤ X t := hhalf t htN
  obtain ⟨A, hAz⟩ : ∃ A : ℕ, (A : ℤ) = X t - X 0 + 1 := ⟨(X t - X 0 + 1).toNat, by omega⟩
  obtain ⟨T, hT, -, hcount, hinj', hbd⟩ := unfold_aux Y N A X t (by omega) htN hmax
    (fun k h₁ h₂ => ⟨by linarith [hhalf k h₂], hlast k h₁ h₂⟩) hinj
  refine ⟨T, ?_, fun τ hτ => (hT τ hτ).2, hinj', hbd⟩
  have h₁ := lip_sub_le (flipX (togB T) X) N (flipX_lip _ _ _ hlip) N le_rfl
  rw [flipX_zero] at h₁
  have h₂ : ((T.length * (T.length + 1) : ℕ) : ℤ) ≤ 2 * N := by linarith
  exact_mod_cast h₂

/-! ### A general walk -/

/-- The flip pattern built from the toggles `TA` of the reversed first part `[0, m]` and the toggles `TB` of the
second part `[m, n]`: on the first part the pattern is reversed and complemented (one more reflection, of the whole
first part, makes its last point the largest). -/
def pat (m : ℕ) (TA TB : List ℕ) (j : ℕ) : Bool :=
  if j < m then !(togB TA (m - 1 - j)) else togB TB (j - m)

/-- On the first part, `flipX (pat m TA TB) X` is the unfolded reversed first part, read backwards and reflected. -/
theorem head_formula (X : ℕ → ℤ) (m : ℕ) (TA TB : List ℕ) : ∀ k ≤ m,
    flipX (pat m TA TB) X k =
      X 0 + flipX (togB TA) (fun i => X (m - i)) m - flipX (togB TA) (fun i => X (m - i)) (m - k) := by
  intro k hk
  induction k with
  | zero => simp [flipX_zero]
  | succ k ih =>
    rw [flipX_succ, ih (by omega)]
    have hstep := flipX_sub (togB TA) (fun i => X (m - i)) (m - (k + 1))
    rw [show m - (k + 1) + 1 = m - k by omega, show m - (m - k) = k by omega,
      show m - (m - (k + 1)) = k + 1 by omega] at hstep
    have hp : pat m TA TB k = !(togB TA (m - (k + 1))) := by
      rw [pat, ite_eq_left (by omega), show m - 1 - k = m - (k + 1) by omega]
    rw [hp]
    cases h : togB TA (m - (k + 1)) <;> simp only [h, Bool.not_false, Bool.not_true, ite_true, ite_false,
      Bool.false_eq_true] at hstep ⊢ <;> linarith

/-- On the second part, `flipX (pat m TA TB) X` is the unfolded second part, shifted. -/
theorem tail_formula (X : ℕ → ℤ) (m : ℕ) (TA TB : List ℕ) : ∀ j,
    flipX (pat m TA TB) X (m + j) =
      flipX (pat m TA TB) X m + flipX (togB TB) (fun i => X (m + i)) j - X m := by
  intro j
  induction j with
  | zero => simp [flipX_zero]
  | succ j ih =>
    rw [← add_assoc, flipX_succ, ih, flipX_succ (togB TB)]
    have hp : pat m TA TB (m + j) = togB TB j := by
      rw [pat, ite_eq_right (by omega), show m + j - m = j by omega]
    rw [hp]
    simp only [← add_assoc]
    cases h : togB TB j <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> ring

/-- A self-avoiding walk (in the form `(X, Y)`) becomes a weak bridge `X 0 ≤ X k ≤ X n` under a flip pattern
`pat m TA TB` with at most `√(2n)` toggles in each part. -/
theorem assembly (X Y : ℕ → ℤ) (n : ℕ) (hlip : Lip X n) (hinj : InjOn2 X Y n) :
    ∃ m ≤ n, ∃ TA TB : List ℕ, TA.length * (TA.length + 1) ≤ 2 * n ∧
      TB.length * (TB.length + 1) ≤ 2 * n ∧ (∀ τ ∈ TA, τ < n) ∧ (∀ τ ∈ TB, τ < n) ∧
      InjOn2 (flipX (pat m TA TB) X) Y n ∧
      ∀ k ≤ n, flipX (pat m TA TB) X 0 ≤ flipX (pat m TA TB) X k ∧
        flipX (pat m TA TB) X k ≤ flipX (pat m TA TB) X n := by
  obtain ⟨m, hmn, hmin, hfirst⟩ := exists_first_argmin X n
  -- the first part, reversed: a half-plane walk from the first minimum
  have hlipr : Lip (fun k => X (m - k)) m := by
    intro k hk
    have h := hlip (m - (k + 1)) (by omega)
    rw [show m - (k + 1) + 1 = m - k by omega] at h
    rw [abs_sub_comm]
    exact h
  have hinjr : InjOn2 (fun k => X (m - k)) (fun k => Y (m - k)) m := by
    intro a ha b hb hab hy
    have h := hinj (m - a) (by omega) (m - b) (by omega) hab hy
    omega
  have hhalfr : ∀ k ≤ m, (fun k => X (m - k)) 0 ≤ (fun k => X (m - k)) k := by
    intro k hk
    simp only [Nat.sub_zero]
    exact hmin (m - k) (by omega)
  obtain ⟨TA, hTAc, hTA, hinjA, hbdA⟩ := unfold _ _ m hlipr hinjr hhalfr
  -- the second part: a half-plane walk from the first minimum
  have hlipt : Lip (fun k => X (m + k)) (n - m) := by
    intro k hk
    have h := hlip (m + k) (by omega)
    simp only [← add_assoc]
    exact h
  have hinjt : InjOn2 (fun k => X (m + k)) (fun k => Y (m + k)) (n - m) := by
    intro a ha b hb hab hy
    have h := hinj (m + a) (by omega) (m + b) (by omega) hab hy
    omega
  have hhalft : ∀ k ≤ n - m, (fun k => X (m + k)) 0 ≤ (fun k => X (m + k)) k := by
    intro k hk
    simp only [Nat.add_zero]
    exact hmin (m + k) (by omega)
  obtain ⟨TB, hTBc, hTB, hinjB, hbdB⟩ := unfold _ _ (n - m) hlipt hinjt hhalft
  have hH := head_formula X m TA TB
  have hT := tail_formula X m TA TB
  have hXA0 : flipX (togB TA) (fun k => X (m - k)) 0 = X m := by rw [flipX_zero, Nat.sub_zero]
  have hXB0 : flipX (togB TB) (fun k => X (m + k)) 0 = X m := by rw [flipX_zero, Nat.add_zero]
  refine ⟨m, hmn, TA, TB, le_trans hTAc (by omega), le_trans hTBc (by omega),
    fun τ hτ => by have := hTA τ hτ; omega, fun τ hτ => by have := hTB τ hτ; omega, ?_⟩
  generalize flipX (pat m TA TB) X = Z at hH hT ⊢
  generalize flipX (togB TA) (fun k => X (m - k)) = XA at hH hinjA hbdA hXA0
  generalize flipX (togB TB) (fun k => X (m + k)) = XB at hT hinjB hbdB hXB0
  -- values on the two parts
  have hZm : Z m = X 0 + XA m - X m := by rw [hH m le_rfl, Nat.sub_self, hXA0]
  have hZ0 : Z 0 = X 0 := by rw [hH 0 (Nat.zero_le _), Nat.sub_zero]; ring
  have hhd : ∀ k < m, Z k = X 0 + XA m - XA (m - k) ∧ X m < XA (m - k) := by
    intro k hk
    refine ⟨hH k hk.le, ?_⟩
    have h := (hbdA (m - k) (by omega)).1
    simp only [show m - (m - k) = k by omega] at h
    linarith [hfirst k hk]
  have htl : ∀ k, m ≤ k → k ≤ n → Z k = Z m + XB (k - m) - X m ∧ X m ≤ XB (k - m) ∧
      XB (k - m) ≤ XB (n - m) := by
    intro k hk hkn
    have h := hT (k - m)
    rw [show m + (k - m) = k by omega] at h
    refine ⟨h, ?_, (hbdB (k - m) (by omega)).2⟩
    have h' := (hbdB (k - m) (by omega)).1
    simp only [show m + (k - m) = k by omega] at h'
    linarith [hmin k hkn]
  have hXAm : X m ≤ XA m := by rw [← hXA0]; exact (hbdA 0 (Nat.zero_le _)).2
  have hXAle : ∀ k ≤ m, XA k ≤ XA m := fun k hk => (hbdA k hk).2
  have hZn := htl n hmn le_rfl
  constructor
  · intro a ha b hb hab hy
    rcases Nat.lt_or_ge a m with ham | ham <;> rcases Nat.lt_or_ge b m with hbm | hbm
    · have h₁ := hhd a ham
      have h₂ := hhd b hbm
      have h := hinjA (m - a) (by omega) (m - b) (by omega) (by linarith)
        (by simp only [show m - (m - a) = a by omega, show m - (m - b) = b by omega]; exact hy)
      omega
    · exfalso
      have h₁ := hhd a ham
      have h₂ := htl b hbm hb
      linarith
    · exfalso
      have h₁ := htl a ham ha
      have h₂ := hhd b hbm
      linarith
    · have h₁ := htl a ham ha
      have h₂ := htl b hbm hb
      have h := hinjB (a - m) (by omega) (b - m) (by omega) (by linarith)
        (by simp only [show m + (a - m) = a by omega, show m + (b - m) = b by omega]; exact hy)
      omega
  · intro k hk
    rcases Nat.lt_or_ge k m with hkm | hkm
    · have h₁ := hhd k hkm
      have h₂ := hXAle (m - k) (by omega)
      constructor <;> linarith
    · have h₁ := htl k hkm hk
      constructor <;> linarith

/-! ### Step sequences -/

/-- The reflection `e₁ ↔ -e₁` of the four steps. -/
def refl4 : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3

theorem dir_refl4 (d : Fin 4) : dir (refl4 d) = (-(dir d).1, (dir d).2) := by
  fin_cases d <;> rfl

theorem refl4_refl4 (d : Fin 4) : refl4 (refl4 d) = d := by
  fin_cases d <;> rfl

/-- Flip the `x`-direction of the steps `j` with `b j`. -/
def flipS {n : ℕ} (b : ℕ → Bool) (s : Fin n → Fin 4) : Fin n → Fin 4 :=
  fun j => if b j then refl4 (s j) else s j

theorem flipS_flipS {n : ℕ} (b : ℕ → Bool) (s : Fin n → Fin 4) : flipS b (flipS b s) = s := by
  funext j
  simp only [flipS]
  cases b j <;> simp [refl4_refl4]

/-- The walk at an integer time, `walk s i = wk s i`. -/
def wk {n : ℕ} (s : Fin n → Fin 4) (k : ℕ) : Cell :=
  ∑ j : Fin n, if (j : ℕ) < k then dir (s j) else 0

theorem walk_eq_wk {n : ℕ} (s : Fin n → Fin 4) (i : Fin (n + 1)) : walk s i = wk s i := rfl

theorem wk_zero {n : ℕ} (s : Fin n → Fin 4) : wk s 0 = 0 := by
  simp [wk]

theorem wk_succ {n : ℕ} (s : Fin n → Fin 4) (k : ℕ) (hk : k < n) :
    wk s (k + 1) = wk s k + dir (s ⟨k, hk⟩) :=
  walk_succ s ⟨k, hk⟩

theorem lip_wk {n : ℕ} (s : Fin n → Fin 4) : Lip (fun k => (wk s k).1) n := by
  intro k hk
  simp only [wk_succ s k hk, Prod.fst_add, add_sub_cancel_left]
  generalize s ⟨k, hk⟩ = d
  fin_cases d <;> simp [dir]

theorem injOn2_wk {n : ℕ} (s : Fin n → Fin 4) (hs : Function.Injective (walk s)) :
    InjOn2 (fun k => (wk s k).1) (fun k => (wk s k).2) n := by
  intro a ha b hb hx hy
  have h : walk s ⟨a, by omega⟩ = walk s ⟨b, by omega⟩ := by
    rw [walk_eq_wk, walk_eq_wk]
    exact Prod.ext hx hy
  exact congrArg Fin.val (hs h)

/-- Flipping steps flips the increments of the first coordinate. -/
theorem wk_flipS {n : ℕ} (b : ℕ → Bool) (s : Fin n → Fin 4) : ∀ k ≤ n,
    wk (flipS b s) k = (flipX b (fun i => (wk s i).1) k, (wk s k).2) := by
  intro k hk
  induction k with
  | zero =>
    rw [flipX_zero]
    ext <;> simp [wk_zero]
  | succ k ih =>
    rw [wk_succ (flipS b s) k (by omega), ih (by omega), flipX_succ, wk_succ s k (by omega)]
    simp only [flipS]
    cases b k
    · ext <;> simp
    · ext <;> simp [dir_refl4]

theorem walk_cons_succ {n : ℕ} (a : Fin 4) (u : Fin n → Fin 4) (i : Fin (n + 1)) :
    walk (Fin.cons a u : Fin (n + 1) → Fin 4) i.succ = dir a + walk u i := by
  simp only [walk]
  rw [Fin.sum_univ_succ]
  simp [Fin.val_succ]

/-- A self-avoiding walk with `0 ≤ x(ω_k) ≤ x(ω_n)`, after one step `e₁`, is a bridge of length `n + 1`. -/
theorem isBridge_cons {n : ℕ} (u : Fin n → Fin 4)
    (hinj : InjOn2 (fun k => (wk u k).1) (fun k => (wk u k).2) n)
    (hlo : ∀ k ≤ n, 0 ≤ (wk u k).1) (hhi : ∀ k ≤ n, (wk u k).1 ≤ (wk u n).1) :
    IsBridge (Fin.cons 0 u : Fin (n + 1) → Fin 4) := by
  have hval : ∀ i : Fin (n + 1),
      walk (Fin.cons 0 u : Fin (n + 1) → Fin 4) i.succ = ((wk u i).1 + 1, (wk u i).2) := by
    intro i
    rw [walk_cons_succ, walk_eq_wk]
    ext
    · simp [dir, add_comm]
    · simp [dir]
  refine ⟨?_, ?_⟩
  · intro a b hab
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ j =>
        exfalso
        rw [walk_zero, hval] at hab
        have h := congrArg Prod.fst hab
        simp only [Prod.fst_zero] at h
        linarith [hlo j (by omega)]
    | succ i =>
      induction b using Fin.cases with
      | zero =>
        exfalso
        rw [walk_zero, hval] at hab
        have h := congrArg Prod.fst hab
        simp only [Prod.fst_zero] at h
        linarith [hlo i (by omega)]
      | succ j =>
        rw [hval, hval] at hab
        have hx := congrArg Prod.fst hab
        have hy := congrArg Prod.snd hab
        simp only at hx hy
        have h := hinj i (by omega) j (by omega) (by linarith) hy
        rw [Fin.succ_inj]
        exact Fin.ext h
  · intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi
    rw [walk_zero, ← Fin.succ_last, hval, hval]
    simp only [Prod.fst_zero, Fin.val_last]
    constructor
    · linarith [hlo j (by omega)]
    · linarith [hhi j (by omega)]

/-- Every self-avoiding walk becomes a bridge of length `n + 1` under a flip pattern `pat m TA TB` and one step
`e₁` in front. -/
theorem exists_pattern {n : ℕ} (s : Fin n → Fin 4) (hs : Function.Injective (walk s)) :
    ∃ m ≤ n, ∃ TA TB : List ℕ, TA.length ≤ Nat.sqrt (2 * n) ∧ TB.length ≤ Nat.sqrt (2 * n) ∧
      (∀ τ ∈ TA, τ < n) ∧ (∀ τ ∈ TB, τ < n) ∧
      IsBridge (Fin.cons 0 (flipS (pat m TA TB) s) : Fin (n + 1) → Fin 4) := by
  obtain ⟨m, hmn, TA, TB, hA, hB, hTA, hTB, hinj, hbd⟩ :=
    assembly (fun k => (wk s k).1) (fun k => (wk s k).2) n (lip_wk s) (injOn2_wk s hs)
  refine ⟨m, hmn, TA, TB, Nat.le_sqrt.2 (le_trans (Nat.mul_le_mul_left _ (Nat.le_succ _)) hA),
    Nat.le_sqrt.2 (le_trans (Nat.mul_le_mul_left _ (Nat.le_succ _)) hB), hTA, hTB, ?_⟩
  have hw := wk_flipS (pat m TA TB) s
  apply isBridge_cons
  · intro a ha b hb hx hy
    simp only [hw a ha, hw b hb] at hx hy
    exact hinj a ha b hb hx hy
  · intro k hk
    rw [hw k hk]
    have h := (hbd k hk).1
    rw [flipX_zero] at h
    simpa [wk_zero] using h
  · intro k hk
    rw [hw k hk, hw n le_rfl]
    exact (hbd k hk).2

/-! ### Counting -/

/-- The number of toggles recorded for each part. -/
def K (n : ℕ) : ℕ := Nat.sqrt (2 * n)

/-- The data of a flip pattern: the split time `m` and the toggle times of the two parts, padded with `n`. -/
abbrev Datum (n : ℕ) := Fin (n + 1) × (Fin (K n) → Fin (n + 1)) × (Fin (K n) → Fin (n + 1))

/-- The flip pattern of a datum. -/
def patOf {n : ℕ} (d : Datum n) : ℕ → Bool :=
  pat d.1 (List.ofFn fun p => (d.2.1 p : ℕ)) (List.ofFn fun p => (d.2.2 p : ℕ))

/-- `T` padded with `n` to length `k`. -/
def padFun (n : ℕ) (T : List ℕ) (hT : ∀ τ ∈ T, τ < n) (k : ℕ) (p : Fin k) : Fin (n + 1) :=
  if h : (p : ℕ) < T.length then ⟨T[(p : ℕ)], Nat.lt_succ_of_lt (hT _ (List.getElem_mem h))⟩
  else ⟨n, Nat.lt_succ_self n⟩

theorem padFun_list (n : ℕ) (T : List ℕ) (hT : ∀ τ ∈ T, τ < n) (k : ℕ) (hk : T.length ≤ k) :
    List.ofFn (fun p : Fin k => (padFun n T hT k p : ℕ)) = T ++ List.replicate (k - T.length) n := by
  apply List.ext_getElem
  · simp
    omega
  · intro p h₁ h₂
    rw [List.getElem_ofFn]
    by_cases hp : p < T.length
    · rw [List.getElem_append_left hp]
      simp [padFun, hp]
    · rw [List.getElem_append_right (by omega)]
      simp [padFun, hp]

theorem togB_padFun (n : ℕ) (T : List ℕ) (hT : ∀ τ ∈ T, τ < n) (k : ℕ) (hk : T.length ≤ k) (i : ℕ)
    (hi : i < n) : togB (List.ofFn (fun p : Fin k => (padFun n T hT k p : ℕ))) i = togB T i := by
  rw [padFun_list n T hT k hk, togB_append, togB_replicate _ _ _ hi]
  simp

theorem exists_datum {n : ℕ} (s : Fin n → Fin 4) (hs : Function.Injective (walk s)) :
    ∃ d : Datum n, IsBridge (Fin.cons 0 (flipS (patOf d) s) : Fin (n + 1) → Fin 4) := by
  obtain ⟨m, hmn, TA, TB, hA, hB, hTA, hTB, hbr⟩ := exists_pattern s hs
  refine ⟨(⟨m, by omega⟩, padFun n TA hTA (K n), padFun n TB hTB (K n)), ?_⟩
  have h : flipS (patOf ((⟨m, by omega⟩, padFun n TA hTA (K n), padFun n TB hTB (K n)) : Datum n)) s =
      flipS (pat m TA TB) s := by
    funext j
    have hj := j.isLt
    have e₁ := togB_padFun n TA hTA (K n) hA (m - 1 - j) (by omega)
    have e₂ := togB_padFun n TB hTB (K n) hB (j - m) (by omega)
    simp only [flipS, patOf, pat, e₁, e₂]
    rfl
  rw [h]
  exact hbr

theorem card_datum (n : ℕ) : Fintype.card (Datum n) = (n + 1) ^ (2 * K n + 1) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring

/-- `c_n ≤ (n+1)^(2K+1) b_{n+1}`. -/
theorem sawCount_le_mul_bridgeCount (n : ℕ) :
    sawCount n ≤ (n + 1) ^ (2 * K n + 1) * bridgeCount (n + 1) := by
  classical
  have hex : ∀ s ∈ (univ.filter fun s : Fin n → Fin 4 => Function.Injective (walk s)),
      ∃ d : Datum n, IsBridge (Fin.cons 0 (flipS (patOf d) s) : Fin (n + 1) → Fin 4) :=
    fun s hs => exists_datum s (Finset.mem_filter.1 hs).2
  choose! g hg using hex
  unfold sawCount bridgeCount
  calc (univ.filter fun s : Fin n → Fin 4 => Function.Injective (walk s)).card
      ≤ ((univ.image fun d : Datum n => fun j : Fin n => patOf d j) ×ˢ
          (univ.filter fun t : Fin (n + 1) → Fin 4 => IsBridge t)).card := by
        refine Finset.card_le_card_of_injOn
          (fun s => ((fun j : Fin n => patOf (g s) j), (Fin.cons 0 (flipS (patOf (g s)) s) : Fin (n + 1) → Fin 4)))
          ?_ ?_
        · intro s hs
          simp only [Finset.coe_product, Finset.coe_image, Finset.coe_univ, Set.image_univ,
            Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod, Set.mem_range, Set.mem_ofPred_eq]
          exact ⟨⟨g s, rfl⟩, hg s hs⟩
        · intro s₁ hs₁ s₂ hs₂ h
          simp only [Prod.mk.injEq] at h
          obtain ⟨h₁, h₂⟩ := h
          have h₃ : flipS (patOf (g s₁)) s₁ = flipS (patOf (g s₂)) s₂ := by
            have := congrArg Fin.tail h₂
            simpa using this
          have h₄ : flipS (patOf (g s₂)) s₂ = flipS (patOf (g s₁)) s₂ := by
            funext j
            simp only [flipS]
            rw [show patOf (g s₂) j = patOf (g s₁) j from (congrFun h₁ j).symm]
          rw [h₄] at h₃
          calc s₁ = flipS (patOf (g s₁)) (flipS (patOf (g s₁)) s₁) := (flipS_flipS _ _).symm
            _ = flipS (patOf (g s₁)) (flipS (patOf (g s₁)) s₂) := by rw [h₃]
            _ = s₂ := flipS_flipS _ _
    _ = (univ.image fun d : Datum n => fun j : Fin n => patOf d j).card *
          (univ.filter fun t : Fin (n + 1) → Fin 4 => IsBridge t).card := Finset.card_product _ _
    _ ≤ (n + 1) ^ (2 * K n + 1) * (univ.filter fun t : Fin (n + 1) → Fin 4 => IsBridge t).card := by
        apply Nat.mul_le_mul_right
        calc _ ≤ (univ : Finset (Datum n)).card := Finset.card_image_le
          _ = (n + 1) ^ (2 * K n + 1) := by rw [Finset.card_univ, card_datum]

/-! ### The subexponential factor -/

/-- `f(n) = (n+1)^(2K+1)`. -/
noncomputable def hwF (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (2 * K n + 1)

theorem hwF_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.log (hwF n) / n ≤ 10 * (Real.log ((n : ℝ) + 1) / Real.sqrt ((n : ℝ) + 1)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (n : ℝ) + 1 := ⟨_, rfl⟩
  rw [← hx]
  have hx1 : 1 ≤ x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hsx1 : 1 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hK : (K n : ℝ) ≤ 2 * Real.sqrt x := by
    have h₁ : K n * K n ≤ 2 * n := Nat.sqrt_le (2 * n)
    have h₂ : (K n : ℝ) * K n ≤ 2 * n := by exact_mod_cast h₁
    nlinarith [Real.sqrt_nonneg x, (Nat.cast_nonneg (K n) : (0 : ℝ) ≤ K n)]
  have hkey : ((2 * K n + 1 : ℕ) : ℝ) * Real.sqrt x ≤ 10 * n := by
    have f₁ := mul_le_mul_of_nonneg_right hK hsx.le
    have f₂ := mul_le_mul_of_nonneg_left hsx1 hsx.le
    push_cast
    nlinarith
  unfold hwF
  rw [← hx, Real.log_pow, div_le_iff₀ hnpos]
  have h₁ : 10 * (Real.log x / Real.sqrt x) * n = (10 * n * Real.log x) / Real.sqrt x := by ring
  rw [h₁, le_div_iff₀ hsx]
  have h₂ := mul_le_mul_of_nonneg_right hkey hL
  linarith

theorem hwF_tendsto : Tendsto (fun n : ℕ => Real.log (hwF n) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards with x
    rw [Real.sqrt_eq_rpow]
  have hlog' : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) :=
    hlog.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h10 := hlog'.const_mul 10
  rw [mul_zero] at h10
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h10 ?_ ?_
  · filter_upwards with n
    apply div_nonneg _ (Nat.cast_nonneg n)
    apply Real.log_nonneg
    unfold hwF
    exact one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact hwF_bound n hn

theorem sawCount_le_hwF (n : ℕ) : (sawCount n : ℝ) ≤ hwF n * bridgeCount (n + 1) := by
  have h := sawCount_le_mul_bridgeCount n
  unfold hwF
  exact_mod_cast h

end HWProof

/-- The Hammersley-Welsh inequality, with `f(n) = (n+1)^(2⌊√(2n)⌋+1)`. -/
theorem hw' : HW := ⟨HWProof.hwF, HWProof.hwF_tendsto, HWProof.sawCount_le_hwF⟩

end Saw38a
