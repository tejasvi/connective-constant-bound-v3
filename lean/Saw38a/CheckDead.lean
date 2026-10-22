import Saw38a.CheckConf

/-!
# Soundness of the checker, part 3: dead cells, children and entries

`deadTest` implies `Dead` (Definition 3.1), `childOK` implies (C2) and `entryOK` implies (C1)/(C2) for one slot.
-/

namespace Saw38a

open Saw38aCore

/-! ## The checker's step, direction and symmetry tables are the spec's -/

theorem addC_eq (a b : Cell) : addC a b = a + b := rfl

theorem dirC_eq (k : Fin 4) : dirC k = dir k := by
  fin_cases k <;> rfl

theorem stepC_eq (k : Fin 3) : stepC k = step k := by
  fin_cases k <;> rfl

theorem d4c_eq (g : Fin 8) (z : Cell) : d4c g z = d4 g z := by
  obtain ⟨x, y⟩ := z
  fin_cases g <;> rfl

/-! ## Grids of small cell lists -/

/-- All cells of `S` have coordinates in `[-28, 28]`. -/
def Small (S : List Cell) : Prop := ∀ c ∈ S, small c = true

theorem inRange_of_small {c : Cell} (h : small c = true) : inRange c = true := by
  simp only [small, inRange, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem mem_gridOf_iff {S : List Cell} (hS : Small S) (q : Cell) : mem (gridOf S) q = true ↔ q ∈ S := by
  rw [mem_gridOf]
  constructor
  · intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  · intro h; simp [h, inRange_of_small (hS q h)]

theorem rep_gridOf' (S : List Cell) : Rep (gridOf S) (↑S.toFinset : Set Cell) := by
  intro c hc; rw [List.coe_toFinset]; exact rep_gridOf S c hc

theorem adj_cases {u t : Cell} (h : Adj u t) :
    u = t + dir 0 ∨ u = t + dir 1 ∨ u = t + dir 2 ∨ u = t + dir 3 := by
  obtain ⟨a, b⟩ := u; obtain ⟨c, d⟩ := t
  simp only [Adj] at h
  simp only [dir, Prod.mk_add_mk, Prod.mk.injEq]
  rcases abs_cases (a - c) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (b - d) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega

/-! ## Dead cells -/

theorem nbCount_eq {S : List Cell} (hS : Small S) (z : Cell) :
    nbCount (gridOf S) z = (Finset.univ.filter fun d : Fin 4 => z + dir d ∈ S.toFinset).card := by
  rw [Finset.card_filter, Fin.sum_univ_four]
  simp only [nbCount, addC_eq]
  have e : ∀ k : Fin 4, dirC k = dir k := dirC_eq
  simp only [show dirC 0 = dir 0 from e 0, show dirC 1 = dir 1 from e 1, show dirC 2 = dir 2 from e 2,
    show dirC 3 = dir 3 from e 3, List.mem_toFinset]
  have hm : ∀ q, (if mem (gridOf S) q = true then 1 else 0) = (if q ∈ S then 1 else 0) := by
    intro q; by_cases hq : q ∈ S
    · simp [hq, (mem_gridOf_iff hS q).2 hq]
    · have : mem (gridOf S) q = false := by
        cases h : mem (gridOf S) q
        · rfl
        · exact absurd ((mem_gridOf_iff hS q).1 h) hq
      simp [hq, this]
  simp only [hm]

theorem small_of_inRange_step {t : Cell} (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1)) (k : Fin 4) :
    inRange (t + dir k) = true := by
  rcases ht with rfl | rfl | rfl <;> fin_cases k <;> decide

/-- `tNbrsOK` and confinement: no free neighbour of `t` is reachable. -/
theorem no_reach_tNbr {blk R : Grid} {b : Box} {X : Set Cell} (hrep : Rep blk X) {x y : Nat} {t : Cell}
    (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1)) (hc : confined blk R b x y = true) (hn : tNbrsOK blk R t = true) :
    ∀ u, Adj u t → u ∉ X → ¬ Reach X (cellOf x y) u := by
  intro u hu huX hr
  have hin := reach_of_confined (blockedIn_of_rep hrep) hc u hr
  obtain ⟨x', y', rfl, -, hx1, -, hy1, hm⟩ := hin
  obtain ⟨hbx, hby, -, -⟩ := confined_parts hc
  have hmem : mem R (cellOf x' y') = true := by rw [mem_cellOf R (by omega) (by omega)]; exact hm
  have hnot : ∀ k : Fin 4, cellOf x' y' = t + dir k → False := by
    intro k hk
    have hinr := small_of_inRange_step ht k
    rw [← hk] at hinr
    have hb : mem blk (cellOf x' y') = false := by
      cases h : mem blk (cellOf x' y')
      · rfl
      · exact absurd ((hrep _ hinr).1 h) huX
    simp only [tNbrsOK, addC_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hn
    have e : ∀ k : Fin 4, dirC k = dir k := dirC_eq
    rw [show dirC 0 = dir 0 from e 0, show dirC 1 = dir 1 from e 1, show dirC 2 = dir 2 from e 2,
      show dirC 3 = dir 3 from e 3] at hn
    fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hk <;> rw [← hk] at hn <;>
      simp_all
  rcases adj_cases hu with h | h | h | h
  · exact hnot 0 h
  · exact hnot 1 h
  · exact hnot 2 h
  · exact hnot 3 h

theorem add_cellOf (g : Grid) {x y : Nat} (hx : x ≤ 62) (hy : y ≤ 62) : add g (cellOf x y) = setN g x y := by
  have hin : inRange (cellOf x y) = true := by simp [inRange, cellOf]; omega
  unfold add; simp only [hin, ite_true]; simp [cellOf, ox]

theorem deadTest_sound {S : List Cell} (hS : Small S) {t w : Cell} (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1))
    {eb bigb : Box} (h : deadTest (gridOf S) (add (gridOf S) t) eb bigb t w = true)
    (hw : w ∉ insert t S.toFinset) : Dead S.toFinset t w := by
  refine ⟨hw, ?_⟩
  have htr : inRange t = true := by rcases ht with rfl | rfl | rfl <;> decide
  have hrepE : Rep (add (gridOf S) t) (insert t (↑S.toFinset : Set Cell)) :=
    rep_add (gok_gridOf S) (rep_gridOf' S) t
  simp only [deadTest, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hwr, h⟩ := h
  have hw' : w = cellOf (ox w.1) (ox w.2) := (cellOf_ox hwr).symm
  rcases h with ha | hb | hc
  · left; rwa [← nbCount_eq hS]
  · right; left
    rw [hw']; exact not_connInf_of_confined (blockedIn_of_rep hrepE) hb
  · right; right
    obtain ⟨-, hany⟩ := hc
    obtain ⟨⟨wx, wy⟩, -, hC⟩ := Array.any_eq_true'.1 hany
    simp only [testC, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at hC
    obtain ⟨⟨⟨⟨⟨hwx, hwy⟩, hnE⟩, hne⟩, hconf⟩, htn⟩ := hC
    refine ⟨cellOf wx wy, ?_, ?_, ?_, ?_⟩
    · intro hmem
      have hin : inRange (cellOf wx wy) = true := by simp [inRange, cellOf]; omega
      have := (hrepE _ hin).2 (by simpa [Finset.mem_insert, List.mem_toFinset] using hmem)
      rw [mem_cellOf _ (by omega) (by omega)] at this
      simp [this] at hnE
    · intro heq
      rw [hw'] at heq
      obtain ⟨h1, h2⟩ := cellOf_inj heq
      subst h1; subst h2
      simp at hne
    · have hrep2 : Rep (setN (add (gridOf S) t) wx wy) (insert (cellOf wx wy) (insert t (↑S.toFinset : Set Cell))) := by
        rw [← add_cellOf _ hwx hwy]; exact rep_add (gok_add (gok_gridOf S) t) hrepE _
      rw [hw']; exact not_connInf_of_confined (blockedIn_of_rep hrep2) hconf
    · have hrep2 : Rep (setN (add (gridOf S) t) wx wy) (insert (cellOf wx wy) (insert t (↑S.toFinset : Set Cell))) := by
        rw [← add_cellOf _ hwx hwy]; exact rep_add (gok_add (gok_gridOf S) t) hrepE _
      intro u hu huX
      rw [hw']; exact no_reach_tNbr hrep2 ht hconf htn u hu huX

/-! ## Children -/

theorem childOK_sound {S C : List Cell} (hS : Small S) {t : Cell} (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1))
    (h : childOK S (gridOf S) t C = true) :
    ∃ g : Fin 8, ∀ z ∈ C.toFinset, d4 g z + t ∈ insert t S.toFinset ∨ Dead S.toFinset t (d4 g z + t) := by
  have htr : inRange t = true := by rcases ht with rfl | rfl | rfl <;> decide
  have hrepE : Rep (add (gridOf S) t) (insert t (↑S.toFinset : Set Cell)) :=
    rep_add (gok_gridOf S) (rep_gridOf' S) t
  simp only [childOK, List.any_eq_true, List.mem_range, List.all_eq_true, Bool.or_eq_true] at h
  rcases h with ⟨g, hg, hq⟩ | ⟨g, hg, hall⟩
  · -- a symmetry that maps every cell into `E`
    refine ⟨⟨g, hg⟩, fun z hz => Or.inl ?_⟩
    have hz' : z ∈ C := List.mem_toFinset.1 hz
    have e : addC (d4c g z) t = d4 ⟨g, hg⟩ z + t := by rw [addC_eq, ← d4c_eq]
    have hm := hq z hz'
    rw [e] at hm
    have hin : inRange (d4 ⟨g, hg⟩ z + t) = true := by
      simp only [mem, Bool.and_eq_true] at hm; exact hm.1
    have := (hrepE _ hin).1 hm
    simpa [Finset.mem_insert, List.mem_toFinset] using this
  refine ⟨⟨g, hg⟩, fun z hz => ?_⟩
  have hz' : z ∈ C := List.mem_toFinset.1 hz
  have e : addC (d4c g z) t = d4 ⟨g, hg⟩ z + t := by rw [addC_eq, ← d4c_eq]
  rcases hall z hz' with hm | hd
  · left
    rw [e] at hm
    have hin : inRange (d4 ⟨g, hg⟩ z + t) = true := by
      simp only [mem, Bool.and_eq_true] at hm; exact hm.1
    have := (hrepE _ hin).1 hm
    simpa [Finset.mem_insert, List.mem_toFinset] using this
  · by_cases hmem : d4 ⟨g, hg⟩ z + t ∈ insert t S.toFinset
    · exact Or.inl hmem
    · right; rw [e] at hd; exact deadTest_sound hS ht hd hmem

end Saw38a
