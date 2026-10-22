import Saw38a.CheckGrid

/-!
# Soundness of the checker, part 2: closed sets confine paths

If `closedIn blk R b` holds, then a lattice path that starts at a cell of `R` (inside the box `b`) and avoids a set `X`
containing the blocked cells stays in `R`. Hence `confined` certifies `¬ ConnInf X z`.
-/

namespace Saw38a

open Saw38aCore

theorem allFrom_true {p : Nat → Bool} {i k : Nat} (h : allFrom p i k = true) :
    ∀ j, i ≤ j → j < i + k → p j = true := by
  induction k generalizing i with
  | zero => intro j h1 h2; omega
  | succ k ih =>
    simp only [allFrom, Bool.and_eq_true] at h
    intro j h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact h.1
    · exact ih h.2 j (by omega) (by omega)

/-- The cells of `R` in the box `b`. -/
def RSet (R : Grid) (b : Box) : Set Cell :=
  {c | ∃ x y, c = cellOf x y ∧ b.x0 ≤ x ∧ x ≤ b.x1 ∧ b.y0 ≤ y ∧ y ≤ b.y1 ∧ memN R x y = true}

theorem closedIn_cell {blk R : Grid} {b : Box} (h : closedIn blk R b = true) {x y : Nat}
    (hx0 : b.x0 ≤ x) (hx1 : x ≤ b.x1) (hy0 : b.y0 ≤ y) (hy1 : y ≤ b.y1) (hr : memN R x y = true) :
    b.x0 < x ∧ x < b.x1 ∧ b.y0 < y ∧ y < b.y1 ∧ okN blk R (x + 1) y = true ∧ okN blk R (x - 1) y = true ∧
      okN blk R x (y + 1) = true ∧ okN blk R x (y - 1) = true := by
  unfold closedIn at h
  have h1 := allFrom_true h y hy0 (by omega)
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · simp [memN, h1] at hr
  · have h2 := allFrom_true h1 x hx0 (by omega)
    simp only [hr, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := h2
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩

theorem cellOf_inj {x y x' y' : Nat} (h : cellOf x y = cellOf x' y') : x = x' ∧ y = y' := by
  simp only [cellOf, Prod.mk.injEq] at h; omega

theorem adj_cellOf {x y : Nat} {v : Cell} (h : Adj (cellOf x y) v) (hx : 0 < x) (hy : 0 < y) :
    v = cellOf (x + 1) y ∨ v = cellOf (x - 1) y ∨ v = cellOf x (y + 1) ∨ v = cellOf x (y - 1) := by
  obtain ⟨a, b⟩ := v
  simp only [Adj, cellOf] at h
  simp only [cellOf, Prod.mk.injEq]
  rcases abs_cases ((x : ℤ) - 31 - a) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases ((y : ℤ) - 31 - b) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega

/-- The blocked cells of `blk` lie in `X`. -/
def BlockedIn (blk : Grid) (X : Set Cell) : Prop :=
  ∀ x y, x < 63 → y < 63 → memN blk x y = true → cellOf x y ∈ X

theorem blockedIn_of_rep {g : Grid} {X : Set Cell} (h : Rep g X) : BlockedIn g X := by
  intro x y hx hy hm
  have hin : inRange (cellOf x y) = true := by simp [inRange, cellOf]; omega
  exact (h _ hin).1 (by rw [mem_cellOf g hx hy]; exact hm)

theorem reach_subset {blk R : Grid} {b : Box} {X : Set Cell} (hbx : b.x1 ≤ 62) (hby : b.y1 ≤ 62)
    (hblk : BlockedIn blk X) (hcl : closedIn blk R b = true) {z : Cell} (hz : z ∈ RSet R b) :
    ∀ w, Relation.ReflTransGen (fun u v => Adj u v ∧ v ∉ X) z w → w ∈ RSet R b := by
  intro w hw
  induction hw with
  | refl => exact hz
  | @tail u v _ hst ih =>
    obtain ⟨x, y, rfl, hx0, hx1, hy0, hy1, hr⟩ := ih
    obtain ⟨hadj, hvX⟩ := hst
    obtain ⟨s1, s2, s3, s4, o1, o2, o3, o4⟩ := closedIn_cell hcl hx0 hx1 hy0 hy1 hr
    have key : ∀ x' y', x' < 63 → y' < 63 → okN blk R x' y' = true → b.x0 ≤ x' → x' ≤ b.x1 → b.y0 ≤ y' →
        y' ≤ b.y1 → v = cellOf x' y' → v ∈ RSet R b := by
      intro x' y' hx' hy' hok a1 a2 a3 a4 hv
      simp only [okN, Bool.or_eq_true] at hok
      rcases hok with hok | hok
      · exact absurd (hv ▸ hblk x' y' hx' hy' hok) hvX
      · exact ⟨x', y', hv, a1, a2, a3, a4, hok⟩
    rcases adj_cellOf hadj (by omega) (by omega) with hv | hv | hv | hv
    · exact key _ _ (by omega) (by omega) o1 (by omega) (by omega) (by omega) (by omega) hv
    · exact key _ _ (by omega) (by omega) o2 (by omega) (by omega) (by omega) (by omega) hv
    · exact key _ _ (by omega) (by omega) o3 (by omega) (by omega) (by omega) (by omega) hv
    · exact key _ _ (by omega) (by omega) o4 (by omega) (by omega) (by omega) (by omega) hv

theorem confined_parts {blk R : Grid} {b : Box} {x y : Nat} (h : confined blk R b x y = true) :
    b.x1 ≤ 62 ∧ b.y1 ≤ 62 ∧ cellOf x y ∈ RSet R b ∧ closedIn blk R b = true := by
  simp only [confined, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩, h9⟩ := h
  exact ⟨h1, h2, ⟨x, y, rfl, h3, h4, h5, h6, h7⟩, h9⟩

/-- Everything reachable from a confined cell lies in the box. -/
theorem reach_of_confined {blk R : Grid} {b : Box} {X : Set Cell} (hblk : BlockedIn blk X) {x y : Nat}
    (h : confined blk R b x y = true) : ∀ w, Reach X (cellOf x y) w → w ∈ RSet R b := by
  obtain ⟨h1, h2, h3, h4⟩ := confined_parts h
  intro w hw
  exact reach_subset h1 h2 hblk h4 h3 w hw.2

theorem rset_finite (R : Grid) (b : Box) :
    RSet R b ⊆ ((Finset.Icc b.x0 b.x1 ×ˢ Finset.Icc b.y0 b.y1).image fun p => cellOf p.1 p.2 : Finset Cell) := by
  rintro c ⟨x, y, rfl, h1, h2, h3, h4, -⟩
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
  exact ⟨(x, y), ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩

/-- `confined` certifies that the cell is not connected to infinity. -/
theorem not_connInf_of_confined {blk R : Grid} {b : Box} {X : Set Cell} (hblk : BlockedIn blk X) {x y : Nat}
    (h : confined blk R b x y = true) : ¬ ConnInf X (cellOf x y) := by
  intro hc
  obtain ⟨w, hwF, hw⟩ := hc ((Finset.Icc b.x0 b.x1 ×ˢ Finset.Icc b.y0 b.y1).image fun p => cellOf p.1 p.2)
  exact hwF (rset_finite R b (reach_of_confined hblk h w hw))

end Saw38a
