/- Campaign Arc 2, U3 microbench kernel point nops=1000. Expected value
confirmed compiled first (trie-bench.lean #eval: bench 1000 = 9318608). -/
import GoLean.GoCore.State
set_option maxHeartbeats 0
set_option maxRecDepth 10000000
set_option smartUnfolding false

open GoLean

inductive T where
  | leaf
  | node (v : Option GoCore.HeapCell) (l r : T)

/-- Canonical LSB-first bits, structural on fuel (20 covers every
address the twin reaches: nextAddr ≤ 36,376 < 2^20). -/
def keyBits : Nat → Nat → List Bool
  | 0, _ => []
  | fuel + 1, k =>
      if k == 0 then []
      else (k % 2 == 1) :: keyBits fuel (k / 2)

def T.setB : T → List Bool → GoCore.HeapCell → T
  | .leaf, [], c => .node (some c) .leaf .leaf
  | .node _ l r, [], c => .node (some c) l r
  | .leaf, false :: bs, c => .node none (T.setB .leaf bs c) .leaf
  | .leaf, true :: bs, c => .node none .leaf (T.setB .leaf bs c)
  | .node v l r, false :: bs, c => .node v (l.setB bs c) r
  | .node v l r, true :: bs, c => .node v l (r.setB bs c)

def T.getB : T → List Bool → Option GoCore.HeapCell
  | .leaf, _ => none
  | .node v _ _, [] => v
  | .node _ l _, false :: bs => l.getB bs
  | .node _ _ r, true :: bs => r.getB bs

def T.set (t : T) (k : Nat) (c : GoCore.HeapCell) : T :=
  t.setB (keyBits 20 k) c

def T.get (t : T) (k : Nat) : Option GoCore.HeapCell :=
  t.getB (keyBits 20 k)

/-- Occupied-node count — the full-trie fold that forces every path. -/
def T.count : T → Nat
  | .leaf => 0
  | .node (some _) l r => 1 + l.count + r.count
  | .node none l r => l.count + r.count

def mkCell (n : Nat) : GoCore.HeapCell :=
  { value := .int (Int.ofNat n) .int }

/-- Seed trie: one entry per address 0..36375 (the twin's end-of-run
heap scale, probe C). Structural on `n`. -/
def build : Nat → T → T
  | 0, t => t
  | n + 1, t => build n (t.set n (mkCell n))

def T0 : T := build 36376 .leaf

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- `nops` alternating ops from LCG keys: even index = lookup and
accumulate, odd index = set. Structural on `nops`. -/
def loop : Nat → Nat → Nat → T → Nat × T
  | 0, _, acc, t => (acc, t)
  | n + 1, s, acc, t =>
      let s' := lcg s
      let k := s' % 36376
      if n % 2 == 0 then
        let acc' :=
          match t.get k with
          | some c =>
              match c.value with
              | .int i _ => acc + i.toNat
              | _ => acc
          | none => acc
        loop n s' acc' t
      else
        loop n s' acc (t.set k (mkCell (acc % 1000)))

/-- The benched quantity: checksum + a full fold of the final trie
(forces all set paths and the whole seed build). -/
def bench (nops : Nat) : Nat :=
  let r := loop nops 1 0 T0
  r.1 + r.2.count

example : bench 1000 = 9318608 := by with_unfolding_all rfl
