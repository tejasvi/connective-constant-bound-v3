import Saw38a.Spec
import Saw38aCore.Check

/-!
# Soundness of the checker, part 1: grids and confinement

`mem g c` is membership of the cell `c` in the grid `g`; `gridOf cs` represents the (in-range) cells of `cs`.
`closedIn` and `confined` imply that a cell cannot reach far away while avoiding the blocked set (`not_connInf_of_confined`).
-/

namespace Saw38a

open Saw38aCore

/-! ## Powers of two, bits -/

theorem pow2_eq {k : Nat} (hk : k < 63) : pow2 k = 2 ^ k := by
  simp [pow2, POW2, hk]

theorem testBit_or_pow2 (a k j : Nat) (hk : k < 63) :
    (a ||| pow2 k).testBit j = (a.testBit j || decide (k = j)) := by
  rw [pow2_eq hk, Nat.testBit_or, Nat.testBit_two_pow]

/-! ## Grids of size 63 -/

/-- A grid has 63 rows. -/
def GOK (g : Grid) : Prop := g.size = 63

theorem gok_empty : GOK emptyG := by simp [GOK, emptyG]

theorem gok_setN {g : Grid} (hg : GOK g) (x y : Nat) : GOK (setN g x y) := by
  simpa [GOK, setN] using hg

theorem memN_setN {g : Grid} (hg : GOK g) {x y : Nat} (hx : x < 63) (hy : y < 63) (x' y' : Nat) :
    memN (setN g x y) x' y' = (memN g x' y' || (decide (x = x') && decide (y = y'))) := by
  unfold memN setN
  by_cases hy' : y' < 63
  · have h1 : y' < (g.modify y (· ||| pow2 x)).size := by simp [GOK] at hg; simp [hg, hy']
    have h2 : y' < g.size := by simp [GOK] at hg; simp [hg, hy']
    rw [getElem!_pos (g.modify y (· ||| pow2 x)) y' h1, getElem!_pos g y' h2, Array.getElem_modify]
    by_cases hyy : y = y'
    · subst hyy; simp [testBit_or_pow2 _ _ _ hx]
    · simp [hyy]
  · have h1 : ¬ y' < (g.modify y (· ||| pow2 x)).size := by simp [GOK] at hg; simp [hg, hy']
    have h2 : ¬ y' < g.size := by simp [GOK] at hg; simp [hg, hy']
    rw [getElem!_neg (g.modify y (· ||| pow2 x)) y' h1, getElem!_neg g y' h2]
    have : y ≠ y' := by omega
    simp [this]

theorem memN_empty (x y : Nat) : memN emptyG x y = false := by
  unfold memN emptyG
  by_cases hy : y < 63
  · rw [getElem!_pos (Array.replicate 63 0) y (by simpa using hy)]; simp
  · rw [getElem!_neg (Array.replicate 63 0) y (by simpa using hy)]; simp

/-! ## Cells and offset coordinates -/

/-- The cell with offset coordinates `(x, y)`. -/
def cellOf (x y : Nat) : Cell := ((x : ℤ) - 31, (y : ℤ) - 31)

theorem ox_cellOf (x : Nat) : ox ((x : ℤ) - 31) = x := by
  simp [ox]

theorem inRange_iff (c : Cell) : inRange c = true ↔ -31 ≤ c.1 ∧ c.1 ≤ 31 ∧ -31 ≤ c.2 ∧ c.2 ≤ 31 := by
  simp [inRange, and_assoc]

theorem cellOf_ox {c : Cell} (h : inRange c = true) : cellOf (ox c.1) (ox c.2) = c := by
  rw [inRange_iff] at h
  obtain ⟨a, b⟩ := c
  simp only [cellOf, ox] at *
  ext <;> simp <;> omega

theorem ox_lt {a : ℤ} (h1 : -31 ≤ a) (h2 : a ≤ 31) : ox a < 63 := by
  simp [ox]; omega

theorem mem_cellOf (g : Grid) {x y : Nat} (hx : x < 63) (hy : y < 63) :
    mem g (cellOf x y) = memN g x y := by
  simp [mem, cellOf, inRange, ox_cellOf]
  omega

/-- `g` represents the set `X` (as far as in-range cells go): in-range cells are in `g` iff in `X`. -/
def Rep (g : Grid) (X : Set Cell) : Prop := ∀ c : Cell, inRange c = true → (mem g c = true ↔ c ∈ X)

theorem mem_add {g : Grid} (hg : GOK g) (c q : Cell) :
    mem (add g c) q = (mem g q || (inRange c && decide (q = c))) := by
  unfold add
  by_cases hc : inRange c = true
  · simp only [hc, ite_true]
    rw [inRange_iff] at hc
    unfold mem
    by_cases hq : inRange q = true
    · have hq' := (inRange_iff q).1 hq
      rw [memN_setN hg (ox_lt hc.1 hc.2.1) (ox_lt hc.2.2.1 hc.2.2.2)]
      simp only [hq, Bool.true_and]
      congr 1
      have : (ox c.1 = ox q.1 ∧ ox c.2 = ox q.2) ↔ q = c := by
        obtain ⟨a, b⟩ := c; obtain ⟨a', b'⟩ := q
        simp only [ox, Prod.mk.injEq] at *
        constructor
        · rintro ⟨h1, h2⟩; constructor <;> omega
        · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
      by_cases hqc : q = c
      · simp [hqc, (inRange_iff c).2 hc]
      · simp [hqc]; intro h1; exact fun h2 => hqc (this.1 ⟨h1, h2⟩)
    · simp only [hq, Bool.false_and, Bool.false_or]
      have : q ≠ c := by rintro rfl; exact hq ((inRange_iff q).2 hc)
      simp [this]
  · have hc' : inRange c = false := by simpa using hc
    simp [hc']

theorem gok_add {g : Grid} (hg : GOK g) (c : Cell) : GOK (add g c) := by
  unfold add; split
  · exact gok_setN hg _ _
  · exact hg

theorem gok_foldl_add {g : Grid} (hg : GOK g) (cs : List Cell) : GOK (cs.foldl add g) := by
  induction cs generalizing g with
  | nil => exact hg
  | cons c cs ih => exact ih (gok_add hg c)

theorem mem_foldl_add {g : Grid} (hg : GOK g) (cs : List Cell) (q : Cell) :
    mem (cs.foldl add g) q = (mem g q || (inRange q && decide (q ∈ cs))) := by
  induction cs generalizing g with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih (gok_add hg c), mem_add hg]
    by_cases hqc : q = c
    · subst hqc; cases h : inRange q <;> simp [h]
    · simp [hqc]

theorem gok_gridOf (cs : List Cell) : GOK (gridOf cs) := gok_foldl_add gok_empty cs

theorem mem_gridOf (cs : List Cell) (q : Cell) : mem (gridOf cs) q = (inRange q && decide (q ∈ cs)) := by
  unfold gridOf
  rw [mem_foldl_add gok_empty]
  have : mem emptyG q = false := by simp [mem, memN_empty]
  simp [this]

theorem rep_gridOf (cs : List Cell) : Rep (gridOf cs) {c | c ∈ cs} := by
  intro c hc; simp [mem_gridOf, hc]

theorem rep_add {g : Grid} (hg : GOK g) {X : Set Cell} (h : Rep g X) (c : Cell) : Rep (add g c) (insert c X) := by
  intro q hq
  rw [mem_add hg]
  by_cases hqc : q = c
  · subst hqc; simp [hq]
  · simp [hqc, h q hq]

end Saw38a
