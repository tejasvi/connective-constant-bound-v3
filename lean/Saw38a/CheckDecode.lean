import Saw38a.Spec
import Saw38aCore.Check

/-!
# Decoding of certificate states

`Saw38aCore.decode n T` returns a path only if it is a state in the sense of `IsState` whose cells have coordinates in
`[-28, 28]`, and the start state of order 26 is `decode 14 0`.

`pathOf n T = back (1,0) (-1,0) ds [(-1,0), (0,0)]`, and `back` only prepends cells, each adjacent to the previous
first cell (the step `d` stays a unit vector under `turnBack`).
-/

namespace Saw38a

namespace CheckDecode

/-- `back` only prepends cells. -/
theorem back_eq_append (d c : Saw38aCore.Cell) (ts : List Nat) (acc : List Saw38aCore.Cell) :
    ∃ L, Saw38aCore.back d c ts acc = L ++ acc := by
  induction ts generalizing d c acc with
  | nil => exact ⟨[], rfl⟩
  | cons t ts ih =>
    obtain ⟨L, hL⟩ := ih (Saw38aCore.turnBack t d)
      (c.1 - (Saw38aCore.turnBack t d).1, c.2 - (Saw38aCore.turnBack t d).2)
      ((c.1 - (Saw38aCore.turnBack t d).1, c.2 - (Saw38aCore.turnBack t d).2) :: acc)
    refine ⟨L ++ [(c.1 - (Saw38aCore.turnBack t d).1, c.2 - (Saw38aCore.turnBack t d).2)], ?_⟩
    simp only [Saw38aCore.back]
    rw [hL, List.append_assoc, List.singleton_append]

/-- `turnBack` maps unit vectors to unit vectors. -/
theorem turnBack_unit (t : Nat) (d : Saw38aCore.Cell) (hd : |d.1| + |d.2| = 1) :
    |(Saw38aCore.turnBack t d).1| + |(Saw38aCore.turnBack t d).2| = 1 := by
  unfold Saw38aCore.turnBack
  split_ifs
  · simp only [abs_neg]; linarith
  · simp only [abs_neg]; linarith
  · exact hd

/-- `back` keeps a chain of adjacent cells whose first cell is `c`, when `d` is a unit vector. -/
theorem back_chain (d c : Saw38aCore.Cell) (ts : List Nat) (rest : List Saw38aCore.Cell)
    (hd : |d.1| + |d.2| = 1) (hacc : List.IsChain Adj (c :: rest)) :
    List.IsChain Adj (Saw38aCore.back d c ts (c :: rest)) := by
  induction ts generalizing d c rest with
  | nil => simpa [Saw38aCore.back] using hacc
  | cons t ts ih =>
    simp only [Saw38aCore.back]
    apply ih _ _ _ (turnBack_unit t d hd)
    refine List.IsChain.cons_cons ?_ hacc
    have h := turnBack_unit t d hd
    unfold Adj
    simp only [sub_sub_cancel_left, abs_neg]
    exact h

theorem nodupC_sound : ∀ {p : List Saw38aCore.Cell}, Saw38aCore.nodupC p = true → p.Nodup
  | [], _ => List.nodup_nil
  | c :: cs, h => by
    simp only [Saw38aCore.nodupC, Bool.and_eq_true, List.all_eq_true] at h
    refine List.nodup_cons.2 ⟨fun hc => ?_, nodupC_sound h.2⟩
    have := h.1 c hc
    simp at this

/-- What `decode` checks. -/
theorem decode_some {n T : Nat} {p : List Saw38aCore.Cell} (h : Saw38aCore.decode n T = some p) :
    p = Saw38aCore.pathOf n T ∧ p.all Saw38aCore.small = true ∧ p.Nodup := by
  unfold Saw38aCore.decode at h
  dsimp only at h
  split_ifs at h with h1 h2 h3
  all_goals cases h
  simp only [Bool.and_eq_true] at h3
  exact ⟨rfl, h3.1, nodupC_sound h3.2⟩

end CheckDecode

/-- A decoded path is a state. -/
theorem decode_isState {n T : Nat} {p : List Saw38aCore.Cell} (h : Saw38aCore.decode n T = some p) :
    IsState p := by
  obtain ⟨rfl, -, hnd⟩ := CheckDecode.decode_some h
  obtain ⟨L, hL⟩ := CheckDecode.back_eq_append (1, 0) (-1, 0) (Saw38aCore.digitsQ (n - 2) T).1
    [(-1, 0), (0, 0)]
  have hp : Saw38aCore.pathOf n T = L ++ [(-1, 0), (0, 0)] := hL
  refine ⟨?_, hnd, ?_, ?_, ?_⟩
  · rw [hp]; simp
  · unfold Saw38aCore.pathOf
    apply CheckDecode.back_chain _ _ _ _ (by norm_num)
    refine List.IsChain.cons_cons ?_ (List.IsChain.singleton _)
    unfold Adj
    norm_num
  · rw [hp]; simp
  · rw [hp]; simp

/-- The cells of a decoded path have coordinates in `[-28, 28]`. -/
theorem decode_small {n T : Nat} {p} (h : Saw38aCore.decode n T = some p) :
    ∀ c ∈ p, -28 ≤ c.1 ∧ c.1 ≤ 28 ∧ -28 ≤ c.2 ∧ c.2 ≤ 28 := by
  obtain ⟨-, hs, -⟩ := CheckDecode.decode_some h
  intro c hc
  have := List.all_eq_true.1 hs c hc
  simpa [Saw38aCore.small, and_assoc] using this

/-- The start state of order 26 is the record `(14, 0)`. -/
theorem decode_start : Saw38aCore.decode 14 0 = some (startPath 26) := by
  decide

end Saw38a
