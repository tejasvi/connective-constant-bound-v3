import Mathlib

/-!
# Specification: self-avoiding walks on `ℤ²` and memory-automaton certificates

The definitions follow Sections 2-5 of the paper: walks, self-avoiding walks and bridges (Section 2), states, steps and
dead cells (Definition 3.1), certificates (Definition 3.2), the automaton graph and its paths (Sections 3-5).

Conventions. Cells are `ℤ × ℤ`. A walk is given by its step sequence `s : Fin n → Fin 4`, so the counts `sawCount n`
(the paper's `c_n`) and `bridgeCount n` (`b_n`) are cardinalities of finite sets of step sequences. Certificate states are
indexed by `Fin N`; a state is a lattice path (a list of cells), and only its set of cells `|S|` enters (C1) and (C2).
The certificates used here have only positive weights, so (C3) of Definition 3.2 holds automatically and is replaced by
`pos`.
-/

namespace Saw38a

open Finset Filter Topology

/-- Cells of the square lattice. -/
abbrev Cell := ℤ × ℤ

/-- Two cells are adjacent if they differ by a unit vector. -/
def Adj (a b : Cell) : Prop := |a.1 - b.1| + |a.2 - b.2| = 1

instance : DecidableRel Adj := fun a b => by unfold Adj; infer_instance

/-- The four unit steps `e₁, -e₁, e₂, -e₂`. -/
def dir : Fin 4 → Cell
  | 0 => (1, 0)
  | 1 => (-1, 0)
  | 2 => (0, 1)
  | 3 => (0, -1)

/-! ## Walks, self-avoiding walks and bridges (Section 2) -/

/-- The walk of the step sequence `s`: `ω₀ = 0` and `ω_{i+1} = ω_i + dir (s i)`. -/
def walk {n : ℕ} (s : Fin n → Fin 4) (i : Fin (n + 1)) : Cell :=
  ∑ j : Fin n, if (j : ℕ) < (i : ℕ) then dir (s j) else 0

/-- `c_n`: the number of `n`-step self-avoiding walks that start at the origin. -/
def sawCount (n : ℕ) : ℕ :=
  (univ.filter fun s : Fin n → Fin 4 => Function.Injective (walk s)).card

/-- The bridge condition `x(ω₀) < x(ω_i) ≤ x(ω_n)` for `1 ≤ i ≤ n`, for a self-avoiding walk. -/
def IsBridge {n : ℕ} (s : Fin n → Fin 4) : Prop :=
  Function.Injective (walk s) ∧
    ∀ i : Fin (n + 1), i ≠ 0 → (walk s 0).1 < (walk s i).1 ∧ (walk s i).1 ≤ (walk s (Fin.last n)).1

instance {n : ℕ} (s : Fin n → Fin 4) : Decidable (IsBridge s) := by unfold IsBridge; infer_instance

/-- `b_n`: the number of `n`-step bridges that start at the origin. -/
def bridgeCount (n : ℕ) : ℕ := (univ.filter fun s : Fin n → Fin 4 => IsBridge s).card

/-- The Hammersley-Welsh bound in the weak form used here: `c_n ≤ f(n) b_{n+1}` with a subexponential factor `f`
(`log f(n) / n → 0`). Hammersley and Welsh (1962) proved it with `f(n) = e^{π √(2n/3)}` (Madras and Slade 1993,
Section 3.1). `HW.lean` proves it. -/
def HW : Prop :=
  ∃ f : ℕ → ℝ, Tendsto (fun n : ℕ => Real.log (f n) / n) atTop (𝓝 0) ∧
    ∀ n : ℕ, (sawCount n : ℝ) ≤ f n * bridgeCount (n + 1)

/-! ## States, steps and dead cells (Section 3.1) -/

/-- The three steps `e₁, e₂, -e₂` of a state. -/
def step : Fin 3 → Cell
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (0, -1)

/-- The eight symmetries of `ℤ²` that fix the origin (the group `D₄`). -/
def d4 : Fin 8 → Cell → Cell
  | 0, (x, y) => (x, y)
  | 1, (x, y) => (-y, x)
  | 2, (x, y) => (-x, -y)
  | 3, (x, y) => (y, -x)
  | 4, (x, y) => (x, -y)
  | 5, (x, y) => (-x, y)
  | 6, (x, y) => (y, x)
  | 7, (x, y) => (-y, -x)

/-- A state: a self-avoiding lattice path `s₀, …, s_{m-1}` with `m ≥ 2`, `s_{m-1} = 0` and `s_{m-2} = -e₁`. -/
def IsState (p : List Cell) : Prop :=
  2 ≤ p.length ∧ p.Nodup ∧ List.IsChain Adj p ∧ p.getLast? = some 0 ∧ p.reverse[1]? = some (-1, 0)

/-- The start state of order `K`: the straight path `s_i = (i - K/2, 0)`, `0 ≤ i ≤ K/2`. -/
def startPath (K : ℕ) : List Cell :=
  (List.range (K / 2 + 1)).map fun i => ((i : ℤ) - ((K / 2 : ℕ) : ℤ), 0)

/-- `Reach X a b`: a lattice path from `a` to `b` that avoids `X` (including its ends). -/
def Reach (X : Set Cell) (a b : Cell) : Prop :=
  a ∉ X ∧ Relation.ReflTransGen (fun u v => Adj u v ∧ v ∉ X) a b

/-- `z` is connected to infinity in `ℤ² \ X`: it reaches cells outside every finite set. For finite `X` this says
that `z` lies in the infinite component of `ℤ² \ X`. -/
def ConnInf (X : Set Cell) (z : Cell) : Prop := ∀ F : Finset Cell, ∃ w ∉ F, Reach X z w

/-- Definition 3.1: for a state with cells `A = |S|` and a step `t ∉ A`, with `E = A ∪ {t}`, the cell `z ∉ E` is dead
if (a) at least three of its four neighbours lie in `A`; or (b) it is not connected to infinity in `ℤ² \ E`; or (c) for
some cell `w ∉ E ∪ {z}`, in `ℤ² \ (E ∪ {w})` it is connected neither to infinity nor to any neighbour of `t` outside
`E ∪ {w}`. -/
def Dead (A : Finset Cell) (t z : Cell) : Prop :=
  z ∉ insert t A ∧
    (3 ≤ (univ.filter fun d : Fin 4 => z + dir d ∈ A).card ∨
     ¬ ConnInf (insert t (A : Set Cell)) z ∨
     ∃ w, w ∉ insert t A ∧ w ≠ z ∧
       ¬ ConnInf (insert w (insert t (A : Set Cell))) z ∧
       ∀ u, Adj u t → u ∉ insert w (insert t (A : Set Cell)) →
         ¬ Reach (insert w (insert t (A : Set Cell))) z u)

/-! ## Certificates (Definition 3.2) and the automaton graph -/

/-- Certificate data: states indexed by `Fin N`, with a path, a weight `V` and, for each step, an entry that is `none`
(the symbol `∅`) or the index of a state; `start` is the index of the start state. -/
structure Cert where
  N : ℕ
  path : Fin N → List Cell
  V : Fin N → ℕ
  entry : Fin N → Fin 3 → Option (Fin N)
  start : Fin N

namespace Cert

variable (c : Cert)

/-- The cells `|S|` of state `i`. -/
def cells (i : Fin c.N) : Finset Cell := (c.path i).toFinset

/-- Definition 3.2 for a certificate of order `K` whose weights are all positive. -/
structure Valid (K : ℕ) : Prop where
  state : ∀ i, IsState (c.path i)
  start : c.path c.start = startPath K
  pos : ∀ i, 0 < c.V i
  c1 : ∀ i t, c.entry i t = none → step t ∈ c.cells i ∨ ¬ ConnInf (c.cells i : Set Cell) (step t)
  c2 : ∀ i t j, c.entry i t = some j → step t ∉ c.cells i →
    ∃ g : Fin 8, ∀ z ∈ c.cells j,
      d4 g z + step t ∈ insert (step t) (c.cells i) ∨ Dead (c.cells i) (step t) (d4 g z + step t)

/-- The sum of the weights of the children of state `i`. -/
def childSum (i : Fin c.N) : ℕ :=
  ∑ t : Fin 3, match c.entry i t with
    | none => 0
    | some j => c.V j

/-- The ratio of the certificate is at most `num / den`: `den · Σ_t V_{S'_t} ≤ num · V_S` for every state. -/
def RatioLE (num den : ℕ) : Prop := ∀ i, den * c.childSum i ≤ num * c.V i

/-- The state reached from `i` along the steps `ts`, or `none` if an entry on the way is `∅`. -/
def run : Fin c.N → List (Fin 3) → Option (Fin c.N)
  | i, [] => some i
  | i, t :: ts =>
    match c.entry i t with
    | none => none
    | some j => run j ts

/-- The number of paths of length `n` in the automaton graph that start at the start state. -/
def autCount (n : ℕ) : ℕ :=
  (univ.filter fun ts : Fin n → Fin 3 => (c.run c.start (List.ofFn ts)).isSome).card

end Cert

end Saw38a
