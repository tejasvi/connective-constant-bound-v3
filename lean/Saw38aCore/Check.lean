/-!
# Native checker for 38a memory-automaton certificates (core Lean only)

The checker of `Saw38a.Cert.Valid` and `Saw38a.Cert.RatioLE` for certificate data stored as 7-bit strings (one record
per state). Proof-friendly form: every claim that a cell cannot escape (entries `∅` for trapped steps, dead cells of
kind (b) and (c)) is re-checked by `closedIn` on the flood-fill result, so neither the flood fill nor the search for the
cell `w` of test (c) needs a proof.

Grids use offset coordinates: the cell `(x, y)` with `x, y ∈ [-31, 31]` is bit `x + 31` of row `y + 31` of an array of
63 natural numbers. Rows stay below `2^63`, so they are scalars in compiled code (shifts by addition and a table of
powers of two keep them off the GMP paths).
-/

namespace Saw38aCore

abbrev Cell := Int × Int
abbrev Grid := Array Nat

/-! ## Grids -/

@[noinline] def POW2 : Array Nat := Array.ofFn fun i : Fin 63 => 2 ^ (i : Nat)
@[inline] def pow2 (k : Nat) : Nat := POW2[k]!
@[noinline] def FULL : Nat := 9223372036854775807
@[noinline] def MASK62 : Nat := 4611686018427387903

def emptyG : Grid := Array.replicate 63 0

@[inline] def memN (g : Grid) (x y : Nat) : Bool := g[y]!.testBit x
@[inline] def setN (g : Grid) (x y : Nat) : Grid := g.modify y (· ||| pow2 x)

@[inline] def inRange (c : Cell) : Bool := -31 ≤ c.1 && c.1 ≤ 31 && -31 ≤ c.2 && c.2 ≤ 31
@[inline] def ox (a : Int) : Nat := (a + 31).toNat

/-- Membership of a cell in a grid (false outside the range). -/
@[inline] def mem (g : Grid) (c : Cell) : Bool := inRange c && memN g (ox c.1) (ox c.2)
@[inline] def add (g : Grid) (c : Cell) : Grid := if inRange c then setN g (ox c.1) (ox c.2) else g
def gridOf (cs : List Cell) : Grid := cs.foldl add emptyG

structure Box where
  x0 : Nat
  x1 : Nat
  y0 : Nat
  y1 : Nat

/-- The bounding box (offset coordinates) of in-range cells, enlarged by `e`; `none` for an empty list. -/
def bboxE (cs : List Cell) (e : Nat) : Box :=
  let xs := cs.map fun c => ox c.1
  let ys := cs.map fun c => ox c.2
  ⟨xs.foldl min 62 - e, xs.foldl max 0 + e, ys.foldl min 62 - e, ys.foldl max 0 + e⟩

/-! ## Flood fill (untrusted) and its check -/

@[inline] def lowMask (k : Nat) : Nat := if k ≥ 63 then FULL else pow2 k - 1
@[inline] def rowmask (x0 x1 : Nat) : Nat := lowMask (x1 + 1) ^^^ lowMask x0
@[inline] def shl1 (v : Nat) : Nat := let w := v &&& MASK62; w + w

/-- 4-connected flood fill from `(sx, sy)` over the cells of the box that are not blocked. Its result is only used
through `closedIn`. -/
def flood (blocked : Grid) (bx : Box) (sx sy : Nat) : Grid := Id.run do
  let m := rowmask bx.x0 bx.x1
  let mut free : Grid := emptyG
  for r in [bx.y0 : bx.y1 + 1] do
    free := free.set! r (m &&& (m ^^^ (blocked[r]! &&& m)))
  let mut out : Grid := emptyG
  if (free[sy]! >>> sx) &&& 1 == 0 then return out
  out := out.set! sy (pow2 sx)
  let mut ch := true
  let mut fuel := 4096
  while ch && fuel > 0 do
    ch := false
    fuel := fuel - 1
    for r in [bx.y0 : bx.y1 + 1] do
      let v := out[r]!
      let mut nv := v ||| shl1 v ||| (v >>> 1)
      if r > bx.y0 then nv := nv ||| out[r - 1]!
      if r < bx.y1 then nv := nv ||| out[r + 1]!
      nv := nv &&& free[r]!
      if nv != v then
        out := out.set! r nv
        ch := true
    for k in [0 : bx.y1 + 1 - bx.y0] do
      let r := bx.y1 - k
      let v := out[r]!
      let mut nv := v ||| shl1 v ||| (v >>> 1)
      if r > bx.y0 then nv := nv ||| out[r - 1]!
      if r < bx.y1 then nv := nv ||| out[r + 1]!
      nv := nv &&& free[r]!
      if nv != v then
        out := out.set! r nv
        ch := true
  return out

/-- `p i` for all `i ∈ [a, a + k)`. -/
def allFrom (p : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | i, k + 1 => p i && allFrom p (i + 1) k

@[inline] def okN (blk R : Grid) (x y : Nat) : Bool := memN blk x y || memN R x y

/-- Every cell of `R` in the box lies strictly inside the box, and each of its four neighbours is blocked or in `R`. -/
def closedIn (blk R : Grid) (b : Box) : Bool :=
  allFrom (fun y => R[y]! == 0 || allFrom (fun x =>
    !memN R x y || (b.x0 < x && x < b.x1 && b.y0 < y && y < b.y1 &&
      okN blk R (x + 1) y && okN blk R (x - 1) y && okN blk R x (y + 1) && okN blk R x (y - 1)))
    b.x0 (b.x1 + 1 - b.x0)) b.y0 (b.y1 + 1 - b.y0)

/-- The filled region meets the outermost ring of the box (a cheap filter before `closedIn`; untrusted). -/
def touchesRing (f : Grid) (bx : Box) : Bool := Id.run do
  let m := rowmask bx.x0 bx.x1
  if f[bx.y0]! &&& m != 0 then return true
  if f[bx.y1]! &&& m != 0 then return true
  let edges := pow2 bx.x0 ||| pow2 bx.x1
  for r in [bx.y0 + 1 : bx.y1] do
    if f[r]! &&& edges != 0 then return true
  return false

/-- `R` (inside the box) contains `(x, y)` and is closed: `(x, y)` cannot leave the box avoiding `blk`. -/
@[inline] def confined (blk R : Grid) (b : Box) (x y : Nat) : Bool :=
  b.x1 ≤ 62 && b.y1 ≤ 62 && b.x0 ≤ x && x ≤ b.x1 && b.y0 ≤ y && y ≤ b.y1 && memN R x y && !touchesRing R b &&
    closedIn blk R b

/-! ## States -/

def turnBack (t : Nat) (d : Cell) : Cell :=
  if t = 1 then (d.2, -d.1) else if t = 2 then (-d.2, d.1) else d

/-- Prepend the earlier cells: `d` is the step into the current first cell `c`, the turns are read from the end. -/
def back : Cell → Cell → List Nat → List Cell → List Cell
  | _, _, [], acc => acc
  | d, c, t :: ts, acc =>
    let d' := turnBack t d
    let c' : Cell := (c.1 - d'.1, c.2 - d'.2)
    back d' c' ts (c' :: acc)

/-- The `k` base-3 digits of `T` (least significant first) and the remaining quotient. -/
def digitsQ : Nat → Nat → List Nat × Nat
  | 0, T => ([], T)
  | k + 1, T => let r := digitsQ k (T / 3); (T % 3 :: r.1, r.2)

/-- The path of `n` cells with turn code `T`: the last step is `+e₁` into the origin. -/
def pathOf (n T : Nat) : List Cell := back (1, 0) (-1, 0) (digitsQ (n - 2) T).1 [(-1, 0), (0, 0)]

@[inline] def small (c : Cell) : Bool := -28 ≤ c.1 && c.1 ≤ 28 && -28 ≤ c.2 && c.2 ≤ 28

/-- No cell occurs twice. An explicit loop: `decide p.Nodup` runs generic instance code from the core library, which is
slow and scales badly over many threads. -/
def nodupC : List Cell → Bool
  | [] => true
  | c :: cs => cs.all (fun d => d.1 != c.1 || d.2 != c.2) && nodupC cs

/-- Decode a state from its cell count `n` and turn code `T` (none if malformed). -/
def decode (n T : Nat) : Option (List Cell) :=
  if n < 2 || 40 < n then none
  else if (digitsQ (n - 2) T).2 != 0 then none
  else
    let p := pathOf n T
    if p.all small && nodupC p then some p else none

/-! ## Dead cells -/

def dirC : Nat → Cell
  | 0 => (1, 0)
  | 1 => (-1, 0)
  | 2 => (0, 1)
  | _ => (0, -1)

def stepC : Nat → Cell
  | 0 => (1, 0)
  | 1 => (0, 1)
  | _ => (0, -1)

def d4c : Nat → Cell → Cell
  | 0, (x, y) => (x, y)
  | 1, (x, y) => (-y, x)
  | 2, (x, y) => (-x, -y)
  | 3, (x, y) => (y, -x)
  | 4, (x, y) => (x, -y)
  | 5, (x, y) => (-x, y)
  | 6, (x, y) => (y, x)
  | _, (x, y) => (-y, -x)

@[inline] def addC (a b : Cell) : Cell := (a.1 + b.1, a.2 + b.2)

/-- The number of neighbours of `z` in the grid. -/
def nbCount (g : Grid) (z : Cell) : Nat :=
  (if mem g (addC z (dirC 0)) then 1 else 0) + (if mem g (addC z (dirC 1)) then 1 else 0) +
  (if mem g (addC z (dirC 2)) then 1 else 0) + (if mem g (addC z (dirC 3)) then 1 else 0)

@[inline] def adist (a b : Nat) : Nat := if a ≥ b then a - b else b - a

/-- Cells after the first on one shortest 4-connected path from `(x, y)` through cells of `fl` to the ring of the box
(breadth-first search; untrusted). -/
def pathToRing (fl : Grid) (bx : Box) (x y : Nat) : Array (Nat × Nat) := Id.run do
  let sz := 63 * 63
  let s0 := y * 63 + x
  let mut par : Array Nat := Array.replicate sz sz
  par := par.set! s0 s0
  let mut queue : Array Nat := #[s0]
  let mut head := 0
  let mut goal := sz
  let mut fuel := sz + 1
  while head < queue.size && goal == sz && fuel > 0 do
    fuel := fuel - 1
    let v := queue[head]!
    head := head + 1
    let r := v / 63
    let c := v % 63
    if r ≤ bx.y0 || r ≥ bx.y1 || c ≤ bx.x0 || c ≥ bx.x1 then
      goal := v
    else
      for w in [v + 1, v - 1, v + 63, v - 63] do
        if memN fl (w % 63) (w / 63) && par[w]! == sz then
          par := par.set! w v
          queue := queue.push w
  let mut out : Array (Nat × Nat) := #[]
  if goal == sz then return out
  let mut v := goal
  let mut fuel2 := sz
  while v != s0 && fuel2 > 0 do
    fuel2 := fuel2 - 1
    out := out.push (v % 63, v / 63)
    v := par[v]!
  return out.reverse

/-- Candidates for the cell `w` of test (c) (untrusted): cells near `E` on one shortest path from `(x, y)` to the
ring inside the component `fl`. Every cell `w` that passes the test lies on every such path. -/
def cands (Eg : Grid) (eb : Box) (fl : Grid) (bigb : Box) (x y : Nat) : Array (Nat × Nat) :=
  let _ := eb
  (pathToRing fl bigb x y).filter fun c =>
    let xx := c.1
    let yy := c.2
    xx ≥ 1 && yy ≥ 1 && !memN Eg xx yy && ((Eg[yy - 1]! ||| Eg[yy]! ||| Eg[yy + 1]!) >>> (xx - 1)) &&& 7 != 0

/-- No neighbour of `t` outside the blocked set lies in `R`. -/
def tNbrsOK (blk R : Grid) (t : Cell) : Bool :=
  (mem blk (addC t (dirC 0)) || !mem R (addC t (dirC 0))) &&
  (mem blk (addC t (dirC 1)) || !mem R (addC t (dirC 1))) &&
  (mem blk (addC t (dirC 2)) || !mem R (addC t (dirC 2))) &&
  (mem blk (addC t (dirC 3)) || !mem R (addC t (dirC 3)))

/-- Test (c) for the cell `(wx, wy)`: it is outside `E`, differs from `(x, y)`, and in the complement of `E ∪ {w}` the
cell `(x, y)` is confined to a set without free neighbours of `t`. -/
@[inline] def testC (Eg : Grid) (bigb : Box) (t : Cell) (x y wx wy : Nat) : Bool :=
  let Bw := setN Eg wx wy
  let f2 := flood Bw bigb x y
  wx ≤ 62 && wy ≤ 62 && !memN Eg wx wy && !(wx == x && wy == y) && confined Bw f2 bigb x y && tNbrsOK Bw f2 t

/-- The cell `w` (outside `E`) is dead for `(S, t)`: tests (a), (b), (c) of Definition 3.1. -/
def deadTest (Sg Eg : Grid) (eb bigb : Box) (t w : Cell) : Bool :=
  inRange w &&
    (decide (3 ≤ nbCount Sg w) ||
      (let x := ox w.1
       let y := ox w.2
       let fl := flood Eg bigb x y
       confined Eg fl bigb x y ||
         (bigb.x0 < x && x < bigb.x1 && bigb.y0 < y && y < bigb.y1 &&
           (cands Eg eb fl bigb x y).any fun c => testC Eg bigb t x y c.1 c.2)))

/-- (C2) for the child with cells `C`: for some `g ∈ D₄` every cell of `g(C) + t` is in `E` or dead. A first pass looks
for a symmetry that maps every cell into `E` (no dead-cell tests). -/
def childOK (S : List Cell) (Sg : Grid) (t : Cell) (C : List Cell) : Bool :=
  let Eg := add Sg t
  (List.range 8).any (fun g => C.all fun z => mem Eg (addC (d4c g z) t)) ||
    (let eb := bboxE (t :: S) 0
     let bigb : Box := ⟨eb.x0 - 3, eb.x1 + 3, eb.y0 - 3, eb.y1 + 3⟩
     (List.range 8).any fun g => C.all fun z =>
       let w := addC (d4c g z) t
       mem Eg w || deadTest Sg Eg eb bigb t w)

/-! ## Records -/

structure Rec where
  n : Nat
  T : Nat
  c0 : Nat
  c1 : Nat
  c2 : Nat
  V : Nat

/-- The child index that stands for the symbol `∅` (`2^33 - 1`). -/
@[noinline] def NONEC : Nat := 8589934591

@[inline] def byteAt (s : String) (off : Nat) : UInt64 :=
  if h : (⟨off⟩ : String.Pos.Raw) < s.rawEndPos then (s.getUTF8Byte ⟨off⟩ h).toUInt64 else 0

/-- Little-endian base-128 number from `n` characters of `s` at `off`. -/
@[inline] def b128 (s : String) (off n : Nat) : UInt64 := Id.run do
  let mut r : UInt64 := 0
  for k in [0 : n] do
    r := r ||| (byteAt s (off + k) <<< (7 * k).toUInt64)
  return r

/-- Record `i` (31 characters: cell count and turn code 7, the three child indices 15, weight 9) from chunk `i / cs`.
The key field is `n · 2^44 + T`; the child field is `c₀ + c₁ 2^33 + c₂ 2^66`. -/
def readRec (chunks : Array String) (cs i : Nat) : Rec :=
  match chunks[i / cs]? with
  | none => ⟨0, 0, 0, 0, 0, 0⟩
  | some s =>
    let o := 31 * (i % cs)
    let u := b128 s o 7
    let lo := b128 s (o + 7) 9
    let hi := b128 s (o + 16) 6
    let m33 : UInt64 := 8589934591
    ⟨(u >>> 44).toNat, (u &&& 17592186044415).toNat, (lo &&& m33).toNat,
      (((lo >>> 33) ||| (hi <<< 30)) &&& m33).toNat, ((hi >>> 3) &&& m33).toNat, (b128 s (o + 22) 9).toNat⟩

/-! ## The check of a state, a range, and a range in parallel -/

/-- The entry of slot `t` (child index `c`, `NONEC` for `∅`) of the state with cells `S`. -/
def entryOK (chunks : Array String) (cs N : Nat) (S : List Cell) (Sg : Grid) (b1 : Box) (t c : Nat) : Bool :=
  let tc := stepC t
  if c == NONEC then
    mem Sg tc || confined Sg (flood Sg b1 (ox tc.1) (ox tc.2)) b1 (ox tc.1) (ox tc.2)
  else
    decide (c < N) && (mem Sg tc ||
      (let r := readRec chunks cs c
       match decode r.n r.T with
       | none => false
       | some C => childOK S Sg tc C))

@[inline] def childV (chunks : Array String) (cs : Nat) (c : Nat) : Nat :=
  if c == NONEC then 0 else (readRec chunks cs c).V

/-- The check of state `i`: decodes, positive weight, (C1)/(C2) for the three slots, ratio at most `num / den`. -/
def checkState (chunks : Array String) (cs N num den i : Nat) : Bool :=
  let r := readRec chunks cs i
  match decode r.n r.T with
  | none => false
  | some S =>
    let Sg := gridOf S
    let b1 := bboxE S 1
    decide (0 < r.V) &&
      entryOK chunks cs N S Sg b1 0 r.c0 && entryOK chunks cs N S Sg b1 1 r.c1 &&
      entryOK chunks cs N S Sg b1 2 r.c2 &&
      decide (den * (childV chunks cs r.c0 + childV chunks cs r.c1 + childV chunks cs r.c2) ≤ num * r.V)

def checkRange (chunks : Array String) (cs N num den lo hi : Nat) : Bool :=
  allFrom (checkState chunks cs N num den) lo (hi - lo)

/-- Consecutive pieces `[a, a + step)` covering `[lo, hi)`. -/
def pieces (step : Nat) : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | fuel + 1, lo, hi => if lo < hi then (lo, min hi (lo + step)) :: pieces step fuel (min hi (lo + step)) hi else []

/-- `checkRange` split into about `T` tasks. -/
def checkRangePar (chunks : Array String) (cs N num den lo hi T : Nat) : Bool :=
  let step := max 1 ((hi - lo + T - 1) / T)
  let tasks := (pieces step (hi - lo) lo hi).map fun p =>
    Task.spawn fun _ => checkRange chunks cs N num den p.1 p.2
  tasks.all fun t => t.get

end Saw38aCore
