/- Campaign Arc 2, U3 OPENING MEASUREMENT (the (d) gate — route memo
§6.4 slice 1): kernel-reduction microbenchmark of the candidate heap
representation, run BEFORE any evaluator build.

Representation candidate: a binary trie keyed by the address's binary
digits (LSB-first bit list, canonical — no trailing zero bits — so
key→path is injective), values `GoLean.HeapCell`. ALL functions are
STRUCTURAL recursion (bit lists + fuel), never well-founded fix — the
kernel does not usefully reduce `WellFounded.fix`.

The bench: build a 36,376-entry trie (the twin's end-of-run heap
size), then `nops` mixed ops (alternating LCG-keyed lookup-accumulate
and set), and return `checksum + finalTrie.count` — the `.count` fold
FORCES the whole final trie, so the kernel cannot lazily skip the set
paths; the nops=0 point isolates the build+count fixed cost.

PASS TARGETS, stated before running ([AGENT], memo §6.5): marginal
per-op kernel time ≤ 25 ms AND marginal retention ≤ 2 MB/op at 36k
entries (projects the heap-op component of a full fast run to
≤ ~50 CPU-h and workable segmentation; the ideal is ms-and-KB scale).
A miss PARKS route (d) — the park clause in the memo then states what
the Sym-automated route needs from this arc's artifacts.

Run (expected values by #eval FIRST, then the kernel examples in
trie-bench-k*.lean):
  cd proofs && GOLEAN_MEM_MAX=16G ../scripts/capped \
    lake env lean ../docs/campaign-arc2-probes/trie-bench.lean
-/
import GoLean.GoCore.State

open GoLean

/-- The candidate trie (bench-local; the real `HeapT` lands in
`proofs/` only if this gate passes). -/
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

#eval do
  IO.println s!"bench 0     = {bench 0}"
  IO.println s!"bench 1000  = {bench 1000}"
  IO.println s!"bench 10000 = {bench 10000}"
