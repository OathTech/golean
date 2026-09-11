# BUG-090 re-diagnosed with a profile: two mechanisms, neither the association list (2026-09-11)

[AGENT] lane `records/bug090-rediagnosis-0911`, records only (no fix, no runtime
edit, no baseline change). Authority: [USER] Mike 2026-09-11, «Great, go ahead and
land this, then launch the lanes» (relayed), on `docs/2026-09-11_review-dispositions.md`
§4 step 2(i); input to the C1 memory-module design (§4 step 3). Evidence — probe
sources, runner, sampler, `results.json`, `steps.json`, generated `summary.md`, five
profiles — `docs/evidence/2026-09-11_bug090-rediagnosis/` (README has the commands).

## 1. Scope

Tree `a461ed8b` (clean); the primary's certified `golean` (sha256
`18beb979fbcc90fe3f13d5f659ed27c515c25840e3ad37db80c717c2bfea7ba4`) copied and run
read-only — no lake build; frontend built from `tools/nativefrontend` at the same tree
with go1.26.5 (the oracle pin); linux/amd64, 32 CPUs, load1 2.3→3.5 (a sibling Lean
build ran; CPU time = wall on every point). Every point: 3 runs, median (min..max in
the evidence); **net** = median wall − the empty probe's median (0.0193 s, 7 runs).
Per-run timeouts 120–150 s, NONE fired — the review's 30 s cut-off at 4,000 appends
completes here in 31.6 s. Profiles: a leaf-IP sampler over ptrace (`ipsample.py`; `perf`
refused, `perf_event_paranoid = 4`) at 1 ms on the worker thread — FLAT leaf-function
profile, no call stacks. Steps per iteration: bisection on `--fuel` (`steps.json`).

## 2. Measurements (per-op = net / op count; ratios are successive nets)

Baseline (e): `s += i`, 49 steps/iteration; 10k–80k iterations net
0.131/0.248/0.491/0.989 s — linear, **12.4 µs/iteration = 252 ns/step**. Reads (i):
1,000 reads of `xs[0]` at len 10/100/1,000/10,000 → 15.4–16.7 µs each — flat in m.
Write count at len 10: 100/1k/10k writes → 15/14.8/14.1 µs each — linear in the count.

| (b) 100 writes `xs[0] = v`, `[]byte` len m | 10 | 100 | 1,000 | 3,000 | 10,000 |
|---|---:|---:|---:|---:|---:|
| net s | 0.0015 | 0.0041 | 0.125 | 0.992 | 10.93 |
| per write | 15 µs | 41 µs | 1.25 ms | 9.9 ms | 109 ms |
| ratio (quadratic would be) | | ×2.7 | ×30 (×100; baseline-dominated) | ×7.9 (×9) | ×11.0 (×11.1) |

(f′) 100 in-place appends into `make([]byte,0,c)`, c = 100…6,400 doubling: net
0.0054/0.0108/0.0273/0.083/0.298/1.13/4.47 s, ratios 2.0, 2.5, 3.05, 3.6, 3.8,
**3.96** → quadratic in the capacity; 44.7 ms per append at c = 6,400 (≈1.1 ns × c²).

| (a)/(f) n appends, net s | 250 | 500 | 1,000 | 2,000 | 4,000 |
|---|---:|---:|---:|---:|---:|
| grow from nil (the review's loop) | 0.026 | 0.120 | 0.728 | 4.66 | 31.6 (3 runs) |
| ratio (cubic = ×8) | | ×4.6 | ×6.1 | ×6.4 | ×6.8 |
| in place, cap = n (no spill) | 0.034 | 0.185 | 1.42 | 9.09 | — |
| ratio | | ×5.4 | ×7.7 | ×6.4 | |

| (c) 100 writes, aggregate shape | net s | per write |
|---|---:|---:|
| `struct{y,x int}`: `s.x = i` | 0.0007 | 7 µs |
| `struct{a [1000]byte; x int}`: `s.x = i` | 0.124 | 1.24 ms |
| `struct{a [10000]byte; x int}`: `s.x = i` | 11.09 | 111 ms |
| `struct{a []byte; x int}`, len(a) = 10,000: `s.x = i` | 0.0011 | 11 µs |
| `[10000]byte`: `b[0] = v` | 11.03 | 110 ms |
| `[10][1000]byte`: `a[0][0] = v` | 1.22 | 12.2 ms (1/9 of flat) |
| `[100][100]byte`: `a[0][0] = v` | 0.25 | 2.5 ms (1/44 of flat) |
| `[][]byte` 10×1,000, separate cells: `xs[0][0] = v` | 0.126 | 1.26 ms (= one 1,000-cell) |

| (d)/(h)/(g) live heap and maps | net s | reading |
|---|---:|---|
| `new(int)` loop, n = 1k/4k/16k/32k (`make([]byte,4)`: 0.035/0.243/3.58, same curve) | 0.034/0.260/3.68/14.05 | ×7.6, ×14.1, ×3.8 for ×4, ×4, ×2 → quadratic |
| 20,000-iteration scalar loop after h = 0/1k/10k/40k live cells (= (h,w) − (h,0)) | 0.246/0.377/1.78/7.35 | +7.1 s at h = 40k = 355 µs/iteration, 2 cell writes → **≈4.4 ns per live cell per write** |
| 300 in-place appends after h = 0/10k/40k | 0.052/0.144/0.347 | same dependence on h |
| map writes, n = 500/1k/2k/4k keys | 0.009/0.021/0.059/0.182 | ×2.4, ×2.8, ×3.1 → quadratic per loop; 45 µs/write at 4k |

Profiles (share of samples; `stepFn` ≤ 0.6 % in each): `append_grow` 2000 (3,742 samples)
— `Array.append` 35 %, `lean_array_push` 29 %, `lean_del_core_other` 19 %, libc memmove-class
5.6 %; `write_fixed` 3000×100 — `Array.append` 48 %, push 20 %, del_core 18 %; `alloc_new`
32000 (12,146 samples) — **`lean_copy_expand_array` 48 %, `lean_del_core_other` 44 %**;
`map_write` 16000 — `mapEntryIndex?` loop 33 %, `valueEq` 22 %, `TypeEnv.resolve` 9.6 %,
heap copy 6 %; `scalar` 80000 — diffuse.

## 3. The cost model the data supports (anchors at `a461ed8b`)

**A. A leaf write re-normalizes its whole root cell — quadratically.** `storeLoc`
resolves a field/index path to the root and rewrites the root value
(`GoLean/GoCore/Ops.lean:1367-1392`; the index arm first copies the array — `arraySet`,
`Ops.lean:316-323`, `set!` on an array the cell still references); the root arm
normalizes the WHOLE value at the declared type (`Ops.lean:1367-1372` →
`ExecState.updateCell`, `GoLean/GoCore/State.lean:529-535`); `normalizeListWith`
rebuilds the array as `#[head] ++ tail` per element (`Ops.lean:1100-1106`; struct twin
`normalizeFieldsWith`, `Ops.lean:1110-1119`). One write into a root of m elements:
**≈1.1 ns × m²** (+ an O(m) term, visible only when m² is small). Table (c) shows the
cost is per ROOT CELL: a scalar field beside a `[10000]byte` pays 111 ms, beside a
`[]byte` of that length 11 µs (its own cell); nested arrays pay Σ mᵢ², not (Σ mᵢ)².
In-place `append` (`GoLean/GoCore/Machine.lean:1343-1350`) is one such write per
element, so n appends at capacity ≈ n are **cubic**; the spill path
(`buildAppendBackingValue`, `Ops.lean:2386-2395`) is linear and NOT the cost.

**B. Every cell write copies the whole heap.** The heap is `Array HeapCell`
(`State.lean:68`; `alloc` = `push`, `:517`; lookup = `h[i]?`, `:149`), but the pre-step
state stays referenced across the step, so `Array.set`/`push` on `σ.heap` (RC > 1)
runs `lean_copy_expand_array` over all H cells and the old array's release decrements
each (the `alloc_new` profile, 92 %): **≈4.4 ns × H per cell write** — allocation-heavy
loops are quadratic in the allocation COUNT (BUG-090's observation stands; its
mechanism does not). Retention sites, by reading (which dominates needs a rebuild —
not done here): (i) the drivers pass `m.shared m.threads` to `raceUpdate` AFTER
`stepMulti m` (`GoLean/GoCore/Multi.lean:2186, 2196, 2237, 2252`; a no-op for one
thread, `:1835`, but the arguments keep `m` alive); (ii) `deliverS` hands back the
PRE-op state on its panic arm (`GoLean/GoCore/StepFn.lean:52-57`), so every op arm of
`stepFn` holds `s` across `applyStmtOp s …` (e.g. `StepFn.lean:460-461`) — whole-state
rollback of a panicking op. Either site alone forces the copy.

**C. Maps: a linear key scan per write** (`mapEntryIndex?`, `Ops.lean:2141-2150`,
resolving the key type per comparison) plus whole payload replacement — ≈11 ns per
live entry per write.

Shares in the review's loop at n = 2,000: A ≈ 99 %, B ≈ 1 % (H ≈ n — the frontend allocates
a one-element `slice-lit`, `$c0`, per `append`); B dominates once a program keeps ≥ 10⁴ cells.

## 4. What the data refutes

- The association-list walk (BUG-090's heading/Mechanism): no list exists (`State.lean:68`);
  reads are flat; the time is in the copy, not a lookup. Retired under a banner in `docs/BUGS.md`.
- Review §13 ("`storeLoc` root reconstruction + `normalizeValueForTy` traversal" ⇒ whole-
  array work per update): right site, wrong exponent (quadratic per write, cubic per
  loop) — and it misses B entirely.
- "Spill/regrowth copying is the cost": in-place ≥ growing at equal n.
- "The step machinery or fuel loop is slow": 252 ns/step; `stepFn` ≤ 0.6 %.
- "The race detector costs per step": a no-op for one thread; its only cost is (B).

## 5. What the C1 memory-module design must satisfy ([AGENT] proposals)

1. **Leaf writes cost O(path depth), never O(root size)**: normalize the INCOMING leaf at
   its declared type (descend the root's `Ty` along the path) and restate the normal-form
   invariant (`isNormalForTy`/`StateWf`: "every cell's value is normal at its declared
   type") per leaf, with the congruence lemma "a normal root updated at one leaf by a
   normal leaf is normal". What it is FOR: int kind-width masking, float bit
   canonicalization, the nil-channel canonical form, struct tag/field alignment — all leaf
   facts. Allocation should establish it too (the hole: `alloc` does not normalize,
   `State.lean:25-29`).
2. **Whole-value normalization, where still needed, is linear**: `normalizeListWith`/
   `normalizeFieldsWith` build with `push`/`mapM`, not `#[head] ++ tail` (10⁴× at m = 10⁴).
3. **Unique ownership of the state across a step and the driver** (the persistent-array
   discipline): no post-step use of the pre-step `ExecState`. The detector's pre-state
   inputs move into the step event or are computed before the step; `deliverS`'s rollback
   becomes validate-then-commit (provable: panic ⇒ store unchanged) or a per-cell undo
   log, never the whole state. Exploration (`EnumDedup`) that needs snapshots pays an
   explicit copy at the fork, not on every write. Acceptance: `alloc_new` linear; the (h)
   scalar phase flat in h.
4. **Cell granularity is a design choice** — slices already break the cost at cell
   boundaries, arrays do not (table (c)); per-element cells (or paths as first-class
   locations) make array writes O(1) but change the relation's footprint shape. PENDING [USER].
5. Maps: an index on the normalized key (O(log n)) keeping the B1 identity stamps;
   lower priority (45 µs/write at 4k entries).

Re-measurement after any of these lands: rerun the evidence dir's `run-probes.py --plan
full` (same points, 3 runs); require `write_fixed` flat in m, `alloc_new` linear,
`append_grow` linear amortized; then revisit BUG-090's corpus consequences (Builder rows
≤ 1 KB, fuzz 10×300, `repeat-bound-refused`, `issue24419`).
