import Saw38a.CheckDead
import Saw38a.CheckDecode

/-!
# Soundness of the checker, part 4: the certificate of the data

`certOf chunks cs N` is the certificate whose states are the records of the data; `valid_of_check` shows that it is
valid with ratio at most `num / den` when `checkState` accepts every record and record 0 decodes to the start path.
`checkRange_sound`, `checkRangePar_sound` and `checkState_of_shards` reduce the hypothesis to the shard checks.
-/

namespace Saw38a

open Saw38aCore

/-! ## Entries -/

theorem stepC_cases {t : Nat} (ht : t < 3) : stepC t = (1, 0) ∨ stepC t = (0, 1) ∨ stepC t = (0, -1) := by
  interval_cases t <;> simp [stepC]

theorem inRange_stepC {t : Nat} (ht : t < 3) : inRange (stepC t) = true := by
  rcases stepC_cases ht with h | h | h <;> rw [h] <;> decide

theorem entryOK_none {chunks : Array String} {cs N : Nat} {S : List Cell} (hS : Small S) {b1 : Box} {t : Nat}
    (ht : t < 3) (h : entryOK chunks cs N S (gridOf S) b1 t NONEC = true) :
    stepC t ∈ S ∨ ¬ ConnInf (↑S.toFinset : Set Cell) (stepC t) := by
  simp only [entryOK, beq_self_eq_true, ite_true, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl ((mem_gridOf_iff hS _).1 h)
  · right
    rw [← cellOf_ox (inRange_stepC ht)]
    exact not_connInf_of_confined (blockedIn_of_rep (rep_gridOf' S)) h

theorem entryOK_some {chunks : Array String} {cs N : Nat} {S : List Cell} (hS : Small S) {b1 : Box} {t c : Nat}
    (hc : c ≠ NONEC) (h : entryOK chunks cs N S (gridOf S) b1 t c = true) :
    c < N ∧ (stepC t ∈ S ∨ ∃ C, decode (readRec chunks cs c).n (readRec chunks cs c).T = some C ∧
      childOK S (gridOf S) (stepC t) C = true) := by
  have hb : (c == NONEC) = false := by simpa using hc
  simp only [entryOK, hb, Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true] at h
  obtain ⟨hcN, h⟩ := h
  refine ⟨hcN, ?_⟩
  rcases h with h | h
  · exact Or.inl ((mem_gridOf_iff hS _).1 h)
  · right
    revert h
    cases hd : decode (readRec chunks cs c).n (readRec chunks cs c).T with
    | none => simp
    | some C => intro h; exact ⟨C, rfl, h⟩

/-! ## States -/

theorem checkState_sound {chunks : Array String} {cs N num den i : Nat}
    (h : checkState chunks cs N num den i = true) :
    ∃ S, decode (readRec chunks cs i).n (readRec chunks cs i).T = some S ∧ 0 < (readRec chunks cs i).V ∧
      entryOK chunks cs N S (gridOf S) (bboxE S 1) 0 (readRec chunks cs i).c0 = true ∧
      entryOK chunks cs N S (gridOf S) (bboxE S 1) 1 (readRec chunks cs i).c1 = true ∧
      entryOK chunks cs N S (gridOf S) (bboxE S 1) 2 (readRec chunks cs i).c2 = true ∧
      den * (childV chunks cs (readRec chunks cs i).c0 + childV chunks cs (readRec chunks cs i).c1 +
        childV chunks cs (readRec chunks cs i).c2) ≤ num * (readRec chunks cs i).V := by
  unfold checkState at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i S hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hV, h0⟩, h1⟩, h2⟩, hr⟩ := h
    exact ⟨S, hd, hV, h0, h1, h2, hr⟩

/-! ## The certificate of the data -/

/-- The child index stored in slot `t` of a record. -/
def slotC (r : Rec) (t : Fin 3) : Nat := if t.val = 0 then r.c0 else if t.val = 1 then r.c1 else r.c2

/-- The certificate whose states are the records `0, …, N - 1`; record 0 is the start state. -/
def certOf (chunks : Array String) (cs N : Nat) (hN : 0 < N) : Cert where
  N := N
  path i := (decode (readRec chunks cs i).n (readRec chunks cs i).T).getD []
  V i := (readRec chunks cs i).V
  entry i t := if slotC (readRec chunks cs i) t = NONEC then none
    else if h : slotC (readRec chunks cs i) t < N then some ⟨_, h⟩ else none
  start := ⟨0, hN⟩

theorem small_of_decode {n T : Nat} {p : List Cell} (h : decode n T = some p) : Small p := by
  intro c hc
  have := decode_small h c hc
  simp only [small, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem stepC_fin (t : Fin 3) : stepC t.val = step t := stepC_eq t

/-- The checks of all records give a valid certificate of ratio at most `num / den`. -/
theorem valid_of_check {chunks : Array String} {cs N num den K : Nat} (hN : 0 < N)
    (hall : ∀ i < N, checkState chunks cs N num den i = true)
    (hstart : decode (readRec chunks cs 0).n (readRec chunks cs 0).T = some (startPath K)) :
    (certOf chunks cs N hN).Valid K ∧ (certOf chunks cs N hN).RatioLE num den := by
  have hloc : ∀ i : Fin N, ∃ S, decode (readRec chunks cs i).n (readRec chunks cs i).T = some S ∧
      (certOf chunks cs N hN).path i = S := by
    intro i
    obtain ⟨S, hd, -⟩ := checkState_sound (hall i i.2)
    exact ⟨S, hd, by simp [certOf, hd]⟩
  -- the three slots of a record, as entries
  have slot_spec : ∀ (i : Fin N) (t : Fin 3) (S : List Cell),
      decode (readRec chunks cs i).n (readRec chunks cs i).T = some S →
      entryOK chunks cs N S (gridOf S) (bboxE S 1) t.val (slotC (readRec chunks cs i) t) = true := by
    intro i t S hd
    obtain ⟨S', hd', -, h0, h1, h2, -⟩ := checkState_sound (hall i i.2)
    rw [hd] at hd'; cases hd'
    fin_cases t
    · simpa [slotC] using h0
    · simpa [slotC] using h1
    · simpa [slotC] using h2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    obtain ⟨S, hd, hp⟩ := hloc i
    rw [hp]; exact decode_isState hd
  · simp [certOf, hstart]
  · intro i
    obtain ⟨S, -, hV, -⟩ := checkState_sound (hall i i.2)
    exact hV
  · intro i t ht
    obtain ⟨S, hd, hp⟩ := hloc i
    have hS := small_of_decode hd
    have hslot := slot_spec i t S hd
    have hnone : slotC (readRec chunks cs i) t = NONEC := by
      by_contra hne
      have := (entryOK_some hS hne hslot).1
      simp [certOf, hne, this] at ht
    rw [hnone] at hslot
    have := entryOK_none hS t.2 hslot
    simp only [Cert.cells, hp, List.mem_toFinset, ← stepC_fin t]
    exact this
  · intro i t j hj ht
    obtain ⟨S, hd, hp⟩ := hloc i
    have hS := small_of_decode hd
    have hslot := slot_spec i t S hd
    have hne : slotC (readRec chunks cs i) t ≠ NONEC := by
      intro h; simp [certOf, h] at hj
    obtain ⟨hcN, hor⟩ := entryOK_some hS hne hslot
    have hjv : j.val = slotC (readRec chunks cs i) t := by
      simp only [certOf, hne, ite_false, hcN, dite_true] at hj
      have := Option.some.inj hj
      rw [← this]
    simp only [Cert.cells, hp, List.mem_toFinset, ← stepC_fin t] at ht ⊢
    rcases hor with hin | ⟨C, hdC, hok⟩
    · exact absurd hin ht
    · have hpj : (certOf chunks cs N hN).path j = C := by
        simp only [certOf, hjv, hdC, Option.getD_some]
      rw [hpj]
      have hst : stepC t.val = (1, 0) ∨ stepC t.val = (0, 1) ∨ stepC t.val = (0, -1) := stepC_cases t.2
      obtain ⟨g, hg⟩ := childOK_sound hS hst hok
      exact ⟨g, fun z hz => by simpa [List.mem_toFinset] using hg z (List.mem_toFinset.2 hz)⟩
  · intro i
    obtain ⟨S, hd, -, h0, h1, h2, hr⟩ := checkState_sound (hall i i.2)
    have hS := small_of_decode hd
    have hsum : (certOf chunks cs N hN).childSum i =
        ∑ t : Fin 3, childV chunks cs (slotC (readRec chunks cs i) t) := by
      unfold Cert.childSum
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have hslot := slot_spec i t S hd
      by_cases hc : slotC (readRec chunks cs i) t = NONEC
      · have hE : (certOf chunks cs N hN).entry i t = none := by simp [certOf, hc]
        rw [hE]; simp [childV, hc]
      · have hcN := (entryOK_some hS hc hslot).1
        have hE : (certOf chunks cs N hN).entry i t = some ⟨_, hcN⟩ := by simp [certOf, hc, hcN]
        rw [hE]
        have hb : (slotC (readRec chunks cs i) t == NONEC) = false := by simpa using hc
        simp [childV, hb, certOf]
    show den * (certOf chunks cs N hN).childSum i ≤ num * (certOf chunks cs N hN).V i
    rw [hsum, Fin.sum_univ_three]
    simpa [slotC, certOf] using hr

/-! ## Ranges and shards -/

theorem checkRange_sound {chunks : Array String} {cs N num den lo hi : Nat}
    (h : checkRange chunks cs N num den lo hi = true) :
    ∀ i, lo ≤ i → i < hi → checkState chunks cs N num den i = true :=
  fun i h1 h2 => allFrom_true h i h1 (by omega)

theorem pieces_cover {step : Nat} (hstep : 0 < step) :
    ∀ fuel lo hi, hi - lo ≤ fuel → ∀ i, lo ≤ i → i < hi → ∃ p ∈ pieces step fuel lo hi, p.1 ≤ i ∧ i < p.2 := by
  intro fuel
  induction fuel with
  | zero => intro lo hi h i h1 h2; omega
  | succ f ih =>
    intro lo hi h i h1 h2
    have hlt : lo < hi := by omega
    simp only [pieces, hlt, ite_true, List.mem_cons]
    by_cases hi' : i < min hi (lo + step)
    · exact ⟨_, Or.inl rfl, h1, hi'⟩
    · obtain ⟨p, hp, hp1, hp2⟩ := ih (min hi (lo + step)) hi (by omega) i (by omega) h2
      exact ⟨p, Or.inr hp, hp1, hp2⟩

theorem checkRangePar_sound {chunks : Array String} {cs N num den lo hi T : Nat}
    (h : checkRangePar chunks cs N num den lo hi T = true) :
    ∀ i, lo ≤ i → i < hi → checkState chunks cs N num den i = true := by
  intro i h1 h2
  unfold checkRangePar at h
  simp only [List.all_map, List.all_eq_true, Function.comp_apply] at h
  obtain ⟨p, hp, hp1, hp2⟩ := pieces_cover (Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _))
    (hi - lo) lo hi (Nat.le_refl _) i h1 h2
  exact checkRange_sound (h p hp) i hp1 hp2

/-- The shards `[k B, min N ((k+1) B))`, `k < M`, cover all records. -/
theorem checkState_of_shards {chunks : Array String} {cs N num den M B T : Nat} (hB : 0 < B) (hM : N ≤ M * B)
    (hsh : ∀ k < M, checkRangePar chunks cs N num den (k * B) (min N ((k + 1) * B)) T = true) :
    ∀ i < N, checkState chunks cs N num den i = true := by
  intro i hi
  have hk : i / B < M := by
    rw [Nat.div_lt_iff_lt_mul hB]; omega
  refine checkRangePar_sound (hsh _ hk) i (Nat.div_mul_le_self i B) ?_
  simp only [lt_min_iff]
  refine ⟨hi, ?_⟩
  rw [Nat.add_mul, one_mul]; exact Nat.lt_div_mul_add hB

end Saw38a
