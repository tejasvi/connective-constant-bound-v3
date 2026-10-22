import Saw38a.Spec

/-!
# Theorem 4.1: bridges inject into the paths of the automaton

`bridgeCount_le_autCount'` (the statement of `Saw38a.bridgeCount_le_autCount`): for a valid certificate, `b_n` is at
most the number of words of length `n` that the automaton accepts from its start state.

Proof (paper, Section 4), with one fixed continuation. For an `n`-step bridge `ω` (`n ≥ 1`) let `γ` be the two-sided
self-avoiding path that runs through the history `{(x, 0) : x ≤ 0}`, then along `ω` and its translates by `ω_n`.
Along the bridge the automaton visits states `S^k` with isometries `Φ_k z = h_k z + ω_k` (`h_k` a product of `D₄`
elements) such that
  (4.1')  `γ_i ∉ Φ_k(|S^k|)` for all `i > k`.
At time `k` the next step `t = Φ_k⁻¹(ω_{k+1})` is not in `|S^k|` and is connected to infinity in `ℤ² \ |S^k|` (by the
tail of `γ`), so by (C1) its entry is a state `S'`; with a symmetry `g` from (C2), `Φ_{k+1} z = Φ_k(g z + t)`. The new
cells are cells of `E = |S^k| ∪ {t}` or dead for `(S^k, t)`; a dead cell is never visited by the tail of `γ` after
time `k + 1` (the case analysis (a)-(c) of the paper, `dead_not_visited`). The steps read along the way determine the
bridge, so the map from bridges to accepted words is injective.
-/

namespace Saw38a

namespace Bridge

open Finset

/-! ### Adjacency -/

lemma adj_iff {a b : Cell} : Adj a b ↔ (b.1 = a.1 + 1 ∧ b.2 = a.2) ∨ (b.1 = a.1 - 1 ∧ b.2 = a.2) ∨
    (b.1 = a.1 ∧ b.2 = a.2 + 1) ∨ (b.1 = a.1 ∧ b.2 = a.2 - 1) := by
  unfold Adj
  constructor
  · intro h
    rcases abs_cases (a.1 - b.1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (a.2 - b.2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rw [h1, h2] <;> simp

lemma adj_symm {a b : Cell} (h : Adj a b) : Adj b a := by
  rw [adj_iff] at *; omega

lemma adj_translate {a b : Cell} (c : Cell) : Adj (a + c) (b + c) ↔ Adj a b := by
  simp only [adj_iff, Prod.fst_add, Prod.snd_add]; omega

lemma adj_iff_dir {a b : Cell} : Adj a b ↔ ∃ d : Fin 4, b = a + dir d := by
  rw [adj_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨0, Prod.ext (by simp [dir, h1]) (by simp [dir, h2])⟩
    · exact ⟨1, Prod.ext (by simp [dir, h1]; ring) (by simp [dir, h2])⟩
    · exact ⟨2, Prod.ext (by simp [dir, h1]) (by simp [dir, h2])⟩
    · exact ⟨3, Prod.ext (by simp [dir, h1]) (by simp [dir, h2]; ring)⟩
  · rintro ⟨d, rfl⟩
    fin_cases d <;> simp [dir] <;> omega

lemma adj_add_dir (a : Cell) (d : Fin 4) : Adj a (a + dir d) := adj_iff_dir.mpr ⟨d, rfl⟩

lemma dir_injective : Function.Injective dir := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [dir]

/-- Two distinct neighbours of `z` outside `A` leave at most two of its four neighbours in `A`. -/
lemma card_dir_mem_le_two {A : Finset Cell} {z u₁ u₂ : Cell} (h₁ : Adj z u₁) (h₂ : Adj z u₂) (hne : u₁ ≠ u₂)
    (hu₁ : u₁ ∉ A) (hu₂ : u₂ ∉ A) : (univ.filter fun d : Fin 4 => z + dir d ∈ A).card ≤ 2 := by
  obtain ⟨d₁, rfl⟩ := adj_iff_dir.mp h₁
  obtain ⟨d₂, rfl⟩ := adj_iff_dir.mp h₂
  have hd : d₁ ≠ d₂ := fun h => hne (by rw [h])
  have hsub : (univ.filter fun d : Fin 4 => z + dir d ∈ A) ⊆ univ \ {d₁, d₂} := by
    intro d hdA
    rw [mem_filter] at hdA
    rw [mem_sdiff, mem_insert, mem_singleton]
    refine ⟨mem_univ _, ?_⟩
    rintro (rfl | rfl)
    · exact hu₁ hdA.2
    · exact hu₂ hdA.2
  have h2 : ({d₁, d₂} : Finset (Fin 4)).card = 2 := card_pair hd
  have := card_le_card hsub
  rw [card_sdiff_of_subset (subset_univ _), h2, card_univ, Fintype.card_fin] at this
  exact this

/-! ### Paths, reachability, connection to infinity -/

/-- An infinite self-avoiding path. -/
structure IPath (δ : ℕ → Cell) : Prop where
  inj : Function.Injective δ
  adj : ∀ i, Adj (δ i) (δ (i + 1))

lemma reach_of_path {X : Set Cell} {δ : ℕ → Cell} (hadj : ∀ i, Adj (δ i) (δ (i + 1))) {i j : ℕ} (hij : i ≤ j)
    (hX : ∀ k, i ≤ k → k ≤ j → δ k ∉ X) : Reach X (δ i) (δ j) := by
  refine ⟨hX i le_rfl hij, ?_⟩
  induction j, hij using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ j hij ih =>
    exact Relation.ReflTransGen.tail (ih fun k h1 h2 => hX k h1 (by omega)) ⟨hadj j, hX (j + 1) (by omega) le_rfl⟩

lemma reach_of_path_rev {X : Set Cell} {δ : ℕ → Cell} (hadj : ∀ i, Adj (δ i) (δ (i + 1))) {i j : ℕ}
    (hij : i ≤ j) (hX : ∀ k, i ≤ k → k ≤ j → δ k ∉ X) : Reach X (δ j) (δ i) := by
  refine ⟨hX j hij le_rfl, ?_⟩
  induction j, hij using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ j hij ih =>
    exact Relation.ReflTransGen.head ⟨adj_symm (hadj j), hX j hij (by omega)⟩ (ih fun k h1 h2 => hX k h1 (by omega))

/-- An infinite self-avoiding path that avoids `X` from time `i₀` on connects `δ i₀` to infinity in `ℤ² \ X`. -/
lemma connInf_of_path {X : Set Cell} {δ : ℕ → Cell} (hδ : IPath δ) {i₀ : ℕ} (hav : ∀ k, i₀ ≤ k → δ k ∉ X) :
    ConnInf X (δ i₀) := by
  intro F
  have hex : ∃ k, i₀ ≤ k ∧ δ k ∉ F := by
    by_contra hno
    push Not at hno
    have hinj : Function.Injective fun k : ℕ => δ (i₀ + k) := fun a b h => by
      have := hδ.inj h; omega
    have hsub : Set.range (fun k : ℕ => δ (i₀ + k)) ⊆ (F : Set Cell) := by
      rintro _ ⟨k, rfl⟩; exact hno (i₀ + k) (by omega)
    exact (Set.infinite_range_of_injective hinj).mono hsub F.finite_toSet
  obtain ⟨k, hk, hkF⟩ := hex
  exact ⟨δ k, hkF, reach_of_path hδ.adj hk fun j h1 _ => hav j h1⟩

/-! ### Dead cells are never visited (the case analysis of the proof of Theorem 4.1) -/

/-- Let `t ∉ A`, `E = A ∪ {t}`, and `δ` an infinite self-avoiding path that starts at a neighbour of `t` and avoids
`E`. Then `δ` never visits a cell that is dead for `(A, t)`. -/
theorem dead_not_visited {A : Finset Cell} {t z : Cell} (ht : t ∉ A) (hz : Dead A t z) {δ : ℕ → Cell}
    (hδ : IPath δ) (h0 : Adj t (δ 0)) (hav : ∀ i, δ i ∉ insert t A) : ∀ i, δ i ≠ z := by
  intro i hi
  have havS : ∀ i, δ i ∉ insert t (A : Set Cell) := fun i h => hav i (by simpa using h)
  obtain ⟨hzE, hdead⟩ := hz
  rcases hdead with ha | hb | ⟨w, hwE, hwz, hwinf, hwt⟩
  · -- (a): three neighbours of `z` lie in `A`, but the path brings two distinct neighbours outside `A`
    have hnA : ∀ k, δ k ∉ A := fun k h => hav k (mem_insert_of_mem h)
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have h1 : Adj z t := hi ▸ adj_symm h0
      have h2 : Adj z (δ 1) := hi ▸ hδ.adj 0
      have hne : t ≠ δ 1 := fun h => hav 1 (h ▸ mem_insert_self _ _)
      have := card_dir_mem_le_two h1 h2 hne ht (hnA 1)
      omega
    · have hprev : Adj z (δ (i - 1)) := by
        have := hδ.adj (i - 1)
        rw [Nat.sub_add_cancel hpos, hi] at this
        exact adj_symm this
      have hnext : Adj z (δ (i + 1)) := hi ▸ hδ.adj i
      have hne : δ (i - 1) ≠ δ (i + 1) := fun h => by have := hδ.inj h; omega
      have := card_dir_mem_le_two hprev hnext hne (hnA _) (hnA _)
      omega
  · -- (b): `z` is not connected to infinity in `ℤ² \ E`
    exact hb (hi ▸ connInf_of_path hδ fun k _ => havS k)
  · -- (c): the path passes through `w` before reaching `z` and again after leaving it
    have hnot : ∀ k, δ k ≠ w → δ k ∉ insert w (insert t (A : Set Cell)) := by
      intro k hk h
      rcases Set.mem_insert_iff.mp h with h | h
      · exact hk h
      · exact havS k h
    have hafter : ∃ j, i < j ∧ δ j = w := by
      by_contra hno
      push Not at hno
      apply hwinf
      rw [← hi]
      refine connInf_of_path hδ fun k hk => hnot k ?_
      rcases eq_or_lt_of_le hk with rfl | hlt
      · exact fun h => hwz (h.symm.trans hi)
      · exact hno k hlt
    have hbefore : ∃ j, j < i ∧ δ j = w := by
      by_contra hno
      push Not at hno
      have hstart : δ 0 ≠ w := by
        intro h
        rcases Nat.eq_zero_or_pos i with h0' | hpos
        · subst h0'; exact hwz (h.symm.trans hi)
        · exact hno 0 hpos h
      have hreach : Reach (insert w (insert t (A : Set Cell))) (δ i) (δ 0) :=
        reach_of_path_rev hδ.adj (Nat.zero_le i) fun k _ hk => hnot k (by
          rcases eq_or_lt_of_le hk with rfl | hlt
          · exact fun h => hwz (h.symm.trans hi)
          · exact hno k hlt)
      exact hwt (δ 0) (adj_symm h0) (hnot 0 hstart) (hi ▸ hreach)
    obtain ⟨j₁, hj₁, hw₁⟩ := hafter
    obtain ⟨j₂, hj₂, hw₂⟩ := hbefore
    have := hδ.inj (hw₁.trans hw₂.symm)
    omega

/-! ### The walk of a bridge and its continuation -/

/-- The positions of the walk of `s` at every time `k : ℕ` (constant from `n` on). -/
def pos {n : ℕ} (s : Fin n → Fin 4) (k : ℕ) : Cell := ∑ j : Fin n, if (j : ℕ) < k then dir (s j) else 0

lemma walk_eq_pos {n : ℕ} (s : Fin n → Fin 4) (i : Fin (n + 1)) : walk s i = pos s i := rfl

lemma pos_zero {n : ℕ} (s : Fin n → Fin 4) : pos s 0 = 0 := by simp [pos]

lemma pos_succ {n : ℕ} (s : Fin n → Fin 4) {k : ℕ} (hk : k < n) : pos s (k + 1) = pos s k + dir (s ⟨k, hk⟩) := by
  unfold pos
  have e : ∀ j : Fin n, (if (j : ℕ) < k + 1 then dir (s j) else 0) =
      (if (j : ℕ) < k then dir (s j) else 0) + (if j = ⟨k, hk⟩ then dir (s j) else 0) := by
    intro j
    by_cases h1 : (j : ℕ) < k
    · have h2 : j ≠ ⟨k, hk⟩ := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      rw [ite_eq_left (by omega), ite_eq_left h1, ite_eq_right h2, add_zero]
    · by_cases h3 : (j : ℕ) = k
      · have h4 : j = ⟨k, hk⟩ := Fin.ext h3
        rw [ite_eq_left (by omega), ite_eq_right h1, ite_eq_left h4, zero_add]
      · have h5 : j ≠ ⟨k, hk⟩ := fun h => h3 (by rw [h])
        rw [ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h5, add_zero]
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- The facts about a bridge that the proof uses (positions `ω : ℕ → Cell`). -/
structure IsBr (n : ℕ) (ω : ℕ → Cell) : Prop where
  one_le : 1 ≤ n
  start : ω 0 = (0, 0)
  adj : ∀ i < n, Adj (ω i) (ω (i + 1))
  inj : ∀ i ≤ n, ∀ j ≤ n, ω i = ω j → i = j
  xpos : ∀ i, 1 ≤ i → i ≤ n → 0 < (ω i).1 ∧ (ω i).1 ≤ (ω n).1

lemma isBr_of_isBridge {n : ℕ} {s : Fin n → Fin 4} (hn : 1 ≤ n) (hs : IsBridge s) : IsBr n (pos s) where
  one_le := hn
  start := pos_zero s
  adj i hi := by rw [pos_succ s hi]; exact adj_add_dir _ _
  inj i hi j hj h := by
    have := hs.1 (a₁ := ⟨i, by omega⟩) (a₂ := ⟨j, by omega⟩) (by rw [walk_eq_pos, walk_eq_pos]; exact h)
    exact congrArg Fin.val this
  xpos i hi1 hin := by
    have := hs.2 ⟨i, by omega⟩ (by intro h; rw [Fin.ext_iff] at h; simp at h; omega)
    rw [walk_eq_pos, walk_eq_pos, walk_eq_pos] at this
    simpa [pos_zero] using this

/-- The forward part of the continuation: `ω (i mod n) + ⌊i / n⌋ ω_n`. -/
def fwd (n : ℕ) (ω : ℕ → Cell) (i : ℕ) : Cell :=
  ((ω (i % n)).1 + (i / n : ℕ) * (ω n).1, (ω (i % n)).2 + (i / n : ℕ) * (ω n).2)

/-- The continuation: the history `(i, 0)` for `i ≤ 0`, then the bridge and its translates. -/
def cont (n : ℕ) (ω : ℕ → Cell) (i : ℤ) : Cell := if i ≤ 0 then (i, 0) else fwd n ω i.toNat

section Cont

variable {n : ℕ} {ω : ℕ → Cell}

lemma adj_translate' {a b : Cell} (c₁ c₂ : ℤ) (h : Adj a b) : Adj (a.1 + c₁, a.2 + c₂) (b.1 + c₁, b.2 + c₂) := by
  rw [adj_iff] at *; simp only; omega

lemma fwd_eq_of_le (hb : IsBr n ω) {i : ℕ} (hi : i ≤ n) : fwd n ω i = ω i := by
  rcases eq_or_lt_of_le hi with rfl | hlt
  · simp only [fwd, Nat.mod_self, Nat.div_self hb.one_le, hb.start]; push_cast; ring_nf
  · simp only [fwd, Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt]; push_cast; ring_nf

lemma fwd_x (hb : IsBr n ω) (q r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    fwd n ω (q * n + r) = ((ω r).1 + q * (ω n).1, (ω r).2 + q * (ω n).2) := by
  rcases eq_or_lt_of_le hrn with rfl | hlt
  · have h1 : (q * r + r) % r = 0 := by rw [show q * r + r = (q + 1) * r by ring, Nat.mul_mod_left]
    have h2 : (q * r + r) / r = q + 1 := by
      rw [show q * r + r = (q + 1) * r by ring, Nat.mul_div_cancel _ (by omega)]
    simp only [fwd, h1, h2, hb.start]; push_cast; ring_nf
  · have h1 : (q * n + r) % n = r := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    have h2 : (q * n + r) / n = q := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hlt, zero_add]
    simp only [fwd, h1, h2]

lemma blocks {i : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) : ∃ q r, 1 ≤ r ∧ r ≤ n ∧ i = q * n + r :=
  ⟨(i - 1) / n, (i - 1) % n + 1, by omega, by have := Nat.mod_lt (i - 1) (by omega : 0 < n); omega, by
    have := Nat.div_add_mod (i - 1) n; rw [mul_comm] at this; omega⟩

lemma fwd_block (hb : IsBr n ω) {m : ℕ} (hm : 1 ≤ m) :
    ∃ q r, 1 ≤ r ∧ r ≤ n ∧ m = q * n + r ∧ fwd n ω m = ((ω r).1 + q * (ω n).1, (ω r).2 + q * (ω n).2) := by
  obtain ⟨q, r, hr1, hrn, rfl⟩ := blocks hb.one_le hm
  exact ⟨q, r, hr1, hrn, rfl, fwd_x hb q r hr1 hrn⟩

lemma fwd_x_bounds (hb : IsBr n ω) {q r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    (q : ℤ) * (ω n).1 + 1 ≤ (ω r).1 + q * (ω n).1 ∧ (ω r).1 + q * (ω n).1 ≤ (q + 1) * (ω n).1 := by
  obtain ⟨h1, h2⟩ := hb.xpos r hr1 hrn
  constructor <;> nlinarith

lemma cont_hist (i : ℤ) (hi : i ≤ 0) : cont n ω i = (i, 0) := by simp [cont, hi]

lemma cont_agree (hb : IsBr n ω) (i : ℕ) (hi : i ≤ n) : cont n ω i = ω i := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp [cont, hb.start]
  · have : ¬ ((i : ℤ) ≤ 0) := by omega
    simp only [cont, this, ite_false, Int.toNat_natCast]
    exact fwd_eq_of_le hb hi

/-- After time `0` the continuation stays in the half-plane `x ≥ 1`. -/
lemma cont_x_pos (hb : IsBr n ω) {i : ℤ} (hi : 0 < i) : 1 ≤ (cont n ω i).1 := by
  have hX : 0 < (ω n).1 := (hb.xpos n hb.one_le le_rfl).1
  have h' : ¬ i ≤ 0 := by omega
  simp only [cont, h', ite_false]
  obtain ⟨q, r, hr1, hrn, -, hf⟩ := fwd_block hb (m := i.toNat) (by omega)
  rw [hf]
  have := (fwd_x_bounds hb (q := q) hr1 hrn).1
  have hq : (0 : ℤ) ≤ q * (ω n).1 := by positivity
  simp only
  omega

lemma cont_injective (hb : IsBr n ω) : Function.Injective (cont n ω) := by
  have hX : 0 < (ω n).1 := (hb.xpos n hb.one_le le_rfl).1
  intro i j hij
  by_cases hi : i ≤ 0 <;> by_cases hj : j ≤ 0
  · rw [cont_hist i hi, cont_hist j hj, Prod.mk.injEq] at hij; exact hij.1
  · exfalso
    have h1 := cont_x_pos hb (i := j) (by omega)
    rw [← hij, cont_hist i hi] at h1
    simp only at h1; omega
  · exfalso
    have h1 := cont_x_pos hb (i := i) (by omega)
    rw [hij, cont_hist j hj] at h1
    simp only at h1; omega
  · simp only [cont, hi, hj, ite_false] at hij
    obtain ⟨q, r, hr1, hrn, hmi, hfi⟩ := fwd_block hb (m := i.toNat) (by omega)
    obtain ⟨q', r', hr1', hrn', hmj, hfj⟩ := fwd_block hb (m := j.toNat) (by omega)
    rw [hfi, hfj] at hij
    have hx := congrArg Prod.fst hij
    have hy := congrArg Prod.snd hij
    simp only at hx hy
    have b1 := fwd_x_bounds hb (q := q) hr1 hrn
    have b2 := fwd_x_bounds hb (q := q') hr1' hrn'
    have hqq : q = q' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have : (q : ℤ) + 1 ≤ q' := by exact_mod_cast h
        nlinarith
      · have : (q' : ℤ) + 1 ≤ q := by exact_mod_cast h
        nlinarith
    subst hqq
    have hω : ω r = ω r' := Prod.ext (by linarith) (by linarith)
    have hrr := hb.inj r hrn r' hrn' hω
    subst hrr
    omega

lemma cont_adj (hb : IsBr n ω) (i : ℤ) : Adj (cont n ω i) (cont n ω (i + 1)) := by
  by_cases hi1 : i + 1 ≤ 0
  · rw [cont_hist i (by omega), cont_hist (i + 1) hi1, adj_iff]; simp
  · by_cases hi0 : i = 0
    · subst hi0
      rw [cont_hist 0 le_rfl, show (0 : ℤ) + 1 = ((1 : ℕ) : ℤ) by norm_num, cont_agree hb 1 hb.one_le]
      have := hb.adj 0 hb.one_le
      rwa [hb.start] at this
    · have hi' : ¬ i ≤ 0 := by omega
      simp only [cont, hi', hi1, ite_false]
      have he : (i + 1).toNat = i.toNat + 1 := by omega
      rw [he]
      obtain ⟨q, r, hr1, hrn, hm, hf⟩ := fwd_block hb (m := i.toNat) (by omega)
      rw [hf]
      rcases eq_or_lt_of_le hrn with hrn' | hlt
      · have hm' : i.toNat + 1 = (q + 1) * n + 1 := by rw [hm, hrn']; ring
        rw [hm', fwd_x hb (q + 1) 1 le_rfl hb.one_le]
        have := adj_translate' ((q + 1 : ℕ) * (ω n).1) ((q + 1 : ℕ) * (ω n).2) (hb.adj 0 hb.one_le)
        rw [hb.start] at this
        rw [hrn']
        convert this using 2 <;> push_cast <;> ring
      · have hm' : i.toNat + 1 = q * n + (r + 1) := by rw [hm]; ring
        rw [hm', fwd_x hb q (r + 1) (by omega) hlt]
        exact adj_translate' ((q : ℤ) * (ω n).1) ((q : ℤ) * (ω n).2) (hb.adj r hlt)

end Cont

/-! ### The symmetries `z ↦ g z + t` -/

/-- The inverse symmetries. -/
def d4inv : Fin 8 → Fin 8 := ![0, 3, 2, 1, 4, 5, 6, 7]

lemma d4_inv_left (g : Fin 8) (z : Cell) : d4 (d4inv g) (d4 g z) = z := by
  obtain ⟨x, y⟩ := z
  fin_cases g <;> simp [d4, d4inv]

lemma d4_inv_right (g : Fin 8) (z : Cell) : d4 g (d4 (d4inv g) z) = z := by
  obtain ⟨x, y⟩ := z
  fin_cases g <;> simp [d4, d4inv]

lemma d4_zero (g : Fin 8) : d4 g 0 = 0 := by
  fin_cases g <;> rfl

lemma d4_adj (g : Fin 8) (a b : Cell) : Adj (d4 g a) (d4 g b) ↔ Adj a b := by
  obtain ⟨x, y⟩ := a
  obtain ⟨u, v⟩ := b
  fin_cases g <;> simp only [d4, adj_iff] <;> omega

/-- `z ↦ g z + t` as a bijection of `ℤ²`. -/
def placeEquiv (g : Fin 8) (t : Cell) : Cell ≃ Cell where
  toFun z := d4 g z + t
  invFun z := d4 (d4inv g) (z - t)
  left_inv z := by simp only [add_sub_cancel_right, d4_inv_left]
  right_inv z := by simp only [d4_inv_right, sub_add_cancel]

lemma placeEquiv_apply (g : Fin 8) (t z : Cell) : placeEquiv g t z = d4 g z + t := rfl

lemma placeEquiv_adj (g : Fin 8) (t a b : Cell) : Adj (placeEquiv g t a) (placeEquiv g t b) ↔ Adj a b := by
  rw [placeEquiv_apply, placeEquiv_apply, adj_translate, d4_adj]

lemma placeEquiv_zero (g : Fin 8) (t : Cell) : placeEquiv g t 0 = t := by
  rw [placeEquiv_apply, d4_zero, zero_add]

/-! ### The run of the automaton along a bridge -/

/-- The index of a step (`2` for every cell other than `e₁, e₂`). -/
def stepIdx (t : Cell) : Fin 3 := if t = (1, 0) then 0 else if t = (0, 1) then 1 else 2

/-- The neighbours of the origin other than `−e₁` are the three steps. -/
lemma step_stepIdx {t : Cell} (ht : Adj 0 t) (hne : t ≠ ((-1 : ℤ), (0 : ℤ))) : step (stepIdx t) = t := by
  obtain ⟨x, y⟩ := t
  rw [adj_iff] at ht
  simp only [Prod.fst_zero, Prod.snd_zero] at ht
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; simp [stepIdx, step]
  · subst h1; subst h2; exact absurd rfl hne
  · subst h1; subst h2; simp [stepIdx, step]
  · subst h1; subst h2; simp [stepIdx, step]

open Classical in
/-- A symmetry for the entry `(i, t) ↦ j` that satisfies (C2) (a fixed choice; `0` if there is none). -/
noncomputable def chooseG (c : Cert) (i : Fin c.N) (t : Fin 3) (j : Fin c.N) : Fin 8 :=
  if h : ∃ g : Fin 8, ∀ z ∈ c.cells j,
      d4 g z + step t ∈ insert (step t) (c.cells i) ∨ Dead (c.cells i) (step t) (d4 g z + step t) then
    Classical.choose h
  else 0

/-- The run along a bridge with positions `ω`: the state `S^k` and the isometry `Φ_k` at time `k`. -/
noncomputable def runB (c : Cert) (ω : ℕ → Cell) : ℕ → Fin c.N × (Cell ≃ Cell)
  | 0 => (c.start, Equiv.refl _)
  | k + 1 =>
    let p := runB c ω k
    let t := stepIdx (p.2.symm (ω (k + 1)))
    match c.entry p.1 t with
    | none => p
    | some j => (j, (placeEquiv (chooseG c p.1 t j) (step t)).trans p.2)

/-- The step read at time `k`. -/
noncomputable def stepAt (c : Cert) (ω : ℕ → Cell) (k : ℕ) : Fin 3 := stepIdx ((runB c ω k).2.symm (ω (k + 1)))

/-- The invariant (4.1') at time `k`, for the continuation `γ`. -/
structure RunInv (c : Cert) (ω : ℕ → Cell) (γ : ℤ → Cell) (k : ℕ) : Prop where
  adj : ∀ a b, Adj ((runB c ω k).2 a) ((runB c ω k).2 b) ↔ Adj a b
  origin : (runB c ω k).2 0 = ω k
  avoid : ∀ z ∈ c.cells (runB c ω k).1, ∀ i : ℤ, (k : ℤ) < i → γ i ≠ (runB c ω k).2 z

lemma mem_cells_minus_e1 (c : Cert) {K : ℕ} (hc : c.Valid K) (i : Fin c.N) : ((-1 : ℤ), (0 : ℤ)) ∈ c.cells i := by
  obtain ⟨-, -, -, -, h⟩ := hc.state i
  unfold Cert.cells
  rw [List.mem_toFinset, ← List.mem_reverse]
  exact List.mem_of_getElem? h

lemma start_cells (c : Cert) {K : ℕ} (hc : c.Valid K) {z : Cell} (hz : z ∈ c.cells c.start) :
    z.2 = 0 ∧ z.1 ≤ 0 := by
  unfold Cert.cells at hz
  rw [hc.start, List.mem_toFinset] at hz
  simp [startPath] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  refine ⟨rfl, ?_⟩
  show (a : ℤ) - (K : ℤ) / 2 ≤ 0
  omega

section Run

theorem runInv_zero (c : Cert) {K : ℕ} (hc : c.Valid K) {n : ℕ} {ω : ℕ → Cell} (hb : IsBr n ω) :
    RunInv c ω (cont n ω) 0 := by
  refine ⟨fun a b => Iff.rfl, ?_, fun z hz i hi => ?_⟩
  · simp [runB, hb.start]; rfl
  · have hz' := start_cells c hc hz
    have h1 := cont_x_pos hb (i := i) (by exact_mod_cast hi)
    intro heq
    have : (cont n ω i).1 = z.1 := by rw [heq]; rfl
    omega

/-- One step of the invariant: `t ∉ |S^k|`, `t` is connected to infinity in `ℤ² \ |S^k|`, and the new cells are
avoided by the continuation after time `k + 1`. -/
theorem step_inv {n : ℕ} {ω : ℕ → Cell} (hb : IsBr n ω) {k : ℕ} (hk : k < n) {A : Finset Cell} {Φ : Cell ≃ Cell} (hΦ : ∀ a b, Adj (Φ a) (Φ b) ↔ Adj a b)
    (hav : ∀ z ∈ A, ∀ i : ℤ, (k : ℤ) < i → cont n ω i ≠ Φ z) {t : Cell} (ht : Φ t = ω (k + 1)) :
    t ∉ A ∧ ConnInf (A : Set Cell) t ∧
      ∀ z, (z ∈ insert t A ∨ Dead A t z) → ∀ i : ℤ, ((k + 1 : ℕ) : ℤ) < i → cont n ω i ≠ Φ z := by
  have hγk : cont n ω ((k + 1 : ℕ) : ℤ) = Φ t := by rw [cont_agree hb (k + 1) hk, ht]
  have htA : t ∉ A := fun htA => hav t htA ((k + 1 : ℕ) : ℤ) (by push_cast; omega) hγk
  -- the tail of the continuation, pulled back by `Φ`
  let δ : ℕ → ℕ → Cell := fun m j => Φ.symm (cont n ω ((m + j : ℕ) : ℤ))
  have hδ : ∀ m, IPath (δ m) := fun m => by
    refine ⟨fun a b h => ?_, fun j => ?_⟩
    · have := cont_injective hb (Φ.symm.injective h)
      have : ((m + a : ℕ) : ℤ) = ((m + b : ℕ) : ℤ) := this
      omega
    · rw [← hΦ]
      simp only [δ, Equiv.apply_symm_apply]
      have := cont_adj hb ((m + j : ℕ) : ℤ)
      rwa [show (((m + j : ℕ) : ℤ) + 1) = ((m + (j + 1) : ℕ) : ℤ) by push_cast; ring] at this
  refine ⟨htA, ?_, ?_⟩
  · -- connection to infinity along the tail after time `k`
    have h0 : δ (k + 1) 0 = t := by
      simp only [δ, Nat.add_zero, hγk, Equiv.symm_apply_apply]
    rw [← h0]
    refine connInf_of_path (hδ (k + 1)) fun j _ hj => ?_
    have hj' : Φ (δ (k + 1) j) ∈ Φ '' A := ⟨_, hj, rfl⟩
    simp only [δ, Equiv.apply_symm_apply] at hj'
    obtain ⟨z, hz, hzeq⟩ := hj'
    exact hav z hz ((k + 1 + j : ℕ) : ℤ) (by push_cast; omega) hzeq.symm
  · intro z hz i hi heq
    rcases hz with hz | hz
    · rcases mem_insert.mp hz with rfl | hz
      · -- `Φ t = γ_{k+1}` is visited only at time `k + 1`
        have := cont_injective hb (heq.trans hγk.symm)
        omega
      · exact hav z hz i (by push_cast at hi ⊢; omega) heq
    · -- a dead cell: the tail after time `k + 1` never visits it
      have havE : ∀ j, δ (k + 2) j ∉ insert t A := by
        intro j hj
        rcases mem_insert.mp hj with hj | hj
        · have h1 : cont n ω ((k + 2 + j : ℕ) : ℤ) = Φ t := by
            rw [← hj]; simp [δ]
          have := cont_injective hb (h1.trans hγk.symm)
          omega
        · have h1 : cont n ω ((k + 2 + j : ℕ) : ℤ) = Φ (δ (k + 2) j) := by simp [δ]
          exact hav _ hj ((k + 2 + j : ℕ) : ℤ) (by push_cast; omega) h1
      have h0 : Adj t (δ (k + 2) 0) := by
        rw [← hΦ]
        simp only [δ, Nat.add_zero, Equiv.apply_symm_apply, ← hγk]
        have := cont_adj hb ((k + 1 : ℕ) : ℤ)
        rwa [show (((k + 1 : ℕ) : ℤ) + 1) = ((k + 2 : ℕ) : ℤ) by push_cast; ring] at this
      have hnv := dead_not_visited htA hz (hδ (k + 2)) h0 havE
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = ((k + 2 + j : ℕ) : ℤ) := ⟨(i - (k + 2)).toNat, by push_cast at hi; omega⟩
      exact hnv j (by simp only [δ]; rw [heq, Equiv.symm_apply_apply])

theorem runInv_succ (c : Cert) {K : ℕ} (hc : c.Valid K) {n : ℕ} {ω : ℕ → Cell} (hb : IsBr n ω) {k : ℕ}
    (hk : k < n) (h : RunInv c ω (cont n ω) k) :
    step (stepAt c ω k) = (runB c ω k).2.symm (ω (k + 1)) ∧
      c.entry (runB c ω k).1 (stepAt c ω k) = some (runB c ω (k + 1)).1 ∧ RunInv c ω (cont n ω) (k + 1) := by
  set p := runB c ω k with hp
  set t := p.2.symm (ω (k + 1)) with htdef
  have ht : p.2 t = ω (k + 1) := by simp [htdef]
  have hadj0 : Adj 0 t := by
    rw [← h.adj, h.origin, ht]; exact hb.adj k hk
  obtain ⟨htS, hconn, hnew⟩ := step_inv hb hk h.adj h.avoid ht
  have hne : t ≠ ((-1 : ℤ), (0 : ℤ)) := fun he => htS (he ▸ mem_cells_minus_e1 c hc p.1)
  have hj : step (stepIdx t) = t := step_stepIdx hadj0 hne
  have hsa : stepAt c ω k = stepIdx t := rfl
  obtain ⟨s', hs'⟩ : ∃ s', c.entry p.1 (stepIdx t) = some s' := by
    cases hE : c.entry p.1 (stepIdx t) with
    | none =>
      rcases hc.c1 _ _ hE with h1 | h1
      · rw [hj] at h1; exact absurd h1 htS
      · rw [hj] at h1; exact absurd hconn h1
    | some s' => exact ⟨s', rfl⟩
  have hrun : runB c ω (k + 1) = (s', (placeEquiv (chooseG c p.1 (stepIdx t) s') (step (stepIdx t))).trans p.2) := by
    show (match c.entry p.1 (stepIdx t) with
      | none => p
      | some j => (j, (placeEquiv (chooseG c p.1 (stepIdx t) j) (step (stepIdx t))).trans p.2)) = _
    rw [hs']
  have hex := hc.c2 p.1 (stepIdx t) s' hs' (by rw [hj]; exact htS)
  have hg : ∀ z ∈ c.cells s', d4 (chooseG c p.1 (stepIdx t) s') z + step (stepIdx t) ∈
      insert (step (stepIdx t)) (c.cells p.1) ∨
      Dead (c.cells p.1) (step (stepIdx t)) (d4 (chooseG c p.1 (stepIdx t) s') z + step (stepIdx t)) := by
    unfold chooseG
    split_ifs
    exact Classical.choose_spec hex
  refine ⟨by rw [hsa, hj], by rw [hsa, hs', hrun], ⟨?_, ?_, ?_⟩⟩
  · intro a b; rw [hrun]; simp only [Equiv.trans_apply]; rw [h.adj, placeEquiv_adj]
  · rw [hrun]; simp only [Equiv.trans_apply, placeEquiv_zero, hj]; exact ht
  · intro z hz i hi
    rw [hrun] at hz ⊢
    simp only [Equiv.trans_apply, placeEquiv_apply]
    have := hg z hz
    generalize d4 (chooseG c p.1 (stepIdx t) s') z + step (stepIdx t) = z' at this ⊢
    rw [hj] at this
    exact hnew z' this i (by exact_mod_cast hi)

theorem runInv_all (c : Cert) {K : ℕ} (hc : c.Valid K) {n : ℕ} {ω : ℕ → Cell} (hb : IsBr n ω) :
    ∀ k ≤ n, RunInv c ω (cont n ω) k := by
  intro k
  induction k with
  | zero => intro _; exact runInv_zero c hc hb
  | succ k ih => intro hk; exact (runInv_succ c hc hb (by omega) (ih (by omega))).2.2

end Run

/-! ### The word read along a bridge is accepted, and determines the bridge -/

lemma run_concat (c : Cert) (i : Fin c.N) (l : List (Fin 3)) (t : Fin 3) :
    c.run i (l ++ [t]) = (c.run i l).bind fun j => c.entry j t := by
  induction l generalizing i with
  | nil =>
    simp only [List.nil_append, Cert.run, Option.bind_some]
    cases c.entry i t <;> rfl
  | cons a l ih =>
    simp only [List.cons_append, Cert.run]
    cases c.entry i a with
    | none => rfl
    | some j => exact ih j

theorem run_stepAt (c : Cert) {K : ℕ} (hc : c.Valid K) {n : ℕ} {ω : ℕ → Cell} (hb : IsBr n ω) :
    ∀ m ≤ n, c.run c.start (List.ofFn fun k : Fin m => stepAt c ω k) = some (runB c ω m).1 := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [List.ofFn_succ', List.concat_eq_append, run_concat]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), Option.bind_some]
    exact (runInv_succ c hc hb (by omega) (runInv_all c hc hb m (by omega))).2.1

theorem stepSeq_inj (c : Cert) {K : ℕ} (hc : c.Valid K) {n : ℕ} {ω ω' : ℕ → Cell} (hb : IsBr n ω)
    (hb' : IsBr n ω') (h : ∀ k < n, stepAt c ω k = stepAt c ω' k) :
    ∀ k ≤ n, ω k = ω' k ∧ runB c ω k = runB c ω' k := by
  intro k
  induction k with
  | zero => intro _; simp [runB, hb.start, hb'.start]
  | succ k ih =>
    intro hk
    obtain ⟨hω, hr⟩ := ih (by omega)
    have h1 := (runInv_succ c hc hb (by omega) (runInv_all c hc hb k (by omega))).1
    have h2 := (runInv_succ c hc hb' (by omega) (runInv_all c hc hb' k (by omega))).1
    have hωk : ω (k + 1) = ω' (k + 1) := by
      have e1 : ω (k + 1) = (runB c ω k).2 (step (stepAt c ω k)) := by rw [h1]; simp
      have e2 : ω' (k + 1) = (runB c ω' k).2 (step (stepAt c ω' k)) := by rw [h2]; simp
      rw [e1, e2, hr, h k (by omega)]
    refine ⟨hωk, ?_⟩
    show (match c.entry (runB c ω k).1 (stepIdx ((runB c ω k).2.symm (ω (k + 1)))) with
      | none => runB c ω k
      | some j => (j, (placeEquiv (chooseG c (runB c ω k).1 (stepIdx ((runB c ω k).2.symm (ω (k + 1)))) j)
          (step (stepIdx ((runB c ω k).2.symm (ω (k + 1)))))).trans (runB c ω k).2)) =
      (match c.entry (runB c ω' k).1 (stepIdx ((runB c ω' k).2.symm (ω' (k + 1)))) with
      | none => runB c ω' k
      | some j => (j, (placeEquiv (chooseG c (runB c ω' k).1 (stepIdx ((runB c ω' k).2.symm (ω' (k + 1)))) j)
          (step (stepIdx ((runB c ω' k).2.symm (ω' (k + 1)))))).trans (runB c ω' k).2))
    rw [hr, hωk]

/-- Equal positions give equal step sequences. -/
lemma steps_eq_of_pos_eq {n : ℕ} {s s' : Fin n → Fin 4} (h : ∀ k ≤ n, pos s k = pos s' k) : s = s' := by
  funext k
  have h1 := pos_succ s k.isLt
  have h2 := pos_succ s' k.isLt
  rw [h (k + 1) k.isLt, h k (le_of_lt k.isLt), h2] at h1
  exact dir_injective (add_left_cancel h1).symm

end Bridge

open Bridge in
/-- **Theorem 4.1.** For a valid certificate, `b_n` is at most the number of words of length `n` that the automaton
accepts from the start state (the statement of `Saw38a.bridgeCount_le_autCount`). -/
theorem bridgeCount_le_autCount' (c : Cert) {K : ℕ} (hc : c.Valid K) (n : ℕ) :
    bridgeCount n ≤ c.autCount n := by
  unfold bridgeCount Cert.autCount
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · calc (Finset.univ.filter fun s : Fin 0 → Fin 4 => IsBridge s).card
        ≤ (Finset.univ : Finset (Fin 0 → Fin 4)).card := Finset.card_filter_le _ _
      _ = 1 := by simp
      _ = (Finset.univ.filter fun ts : Fin 0 → Fin 3 => (c.run c.start (List.ofFn ts)).isSome).card := by
          rw [Finset.filter_true_of_mem fun ts _ => by simp [Cert.run]]; simp
  · refine Finset.card_le_card_of_injOn (fun s : Fin n → Fin 4 => fun k : Fin n => stepAt c (pos s) k) ?_ ?_
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
      have hb := isBr_of_isBridge hn hs
      rw [run_stepAt c hc hb n le_rfl]
      rfl
    · intro s hs s' hs' h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs hs'
      have hb := isBr_of_isBridge hn hs
      have hb' := isBr_of_isBridge hn hs'
      have hk : ∀ k < n, stepAt c (pos s) k = stepAt c (pos s') k := fun k hk =>
        congrFun h ⟨k, hk⟩
      exact steps_eq_of_pos_eq fun k hkn => (stepSeq_inj c hc hb hb' hk k hkn).1

end Saw38a
