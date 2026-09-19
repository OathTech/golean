# C1 completion — the memory module against its charter (lane `core/c1-memory-module-s3-0919`, 2026-09-19)

[AGENT] S3 worker. Charter `docs/2026-09-17_c1-memory-module-charter.md` (D1–D7, D9, D10 RATIFIED
[USER] 2026-09-18 «(1) agree, (2) agree. Go ahead», relayed); handoffs S0–S2b
`docs/2026-09-18_c1-memory-module-handoff.md`, S2c/BUG-111 `docs/2026-09-18_c1-memory-module-s2c-handoff.md`,
S3 `docs/2026-09-19_c1-memory-module-s3-handoff.md`. Numbers below are derivation-anchored in
`docs/evidence/2026-09-19_c1-memory-module-s3/` (S3) and the two predecessor evidence dirs.

## What C1 delivered against §1/§8

| charter item | state | where |
|---|---|---|
| (i) dense heap kept; cost A fixed in place — leaf-typed in-place `storeLoc`, linear normalizers, `alloc` normalizes, `HeapNormal` a `StateWf` conjunct with the congruence lemma (D1 (a), D2 (i), D3) | DONE (S1 `d7b32f59`) | `write_fixed` 21 µs→107 ms across m BEFORE, flat 12.6–16 µs after; `struct{a [10000]byte; x int}: s.x = i` 109 ms→5 µs |
| the trace: `Access := AccessKind × ShadowKey`; every user-memory access emitted BY the operation (`Mem.*`); `Step`/`StepM` labelled (D5 (a)); `accesses_eq_stepAccesses` then the table family deleted (D6 (c)); the module's peek list; the raw call-site inventory (fix round F7) | DONE (S2a–S2b) | `Race.lean:1-256` → the module docstring; `scripts/check-mem-callsites` (70 rows) |
| D9 — the synchronization emissions in the module; ONE fold (`raceUpdate` reads the label, no `sPre`/`tsPre`); BUG-111 fix (i) canonical keys | DONE (S2c `f1ad88c3`/`fc4e5d6b`, `a8e0cf95`) | fold audit 0 mismatches; detector-soundness HOLE 0 |
| cost B(b) — `deliverS`'s saved store: the validate/commit split (`Commit`/`runCommit`/`deliverV`), the per-family «panic ⇒ store unchanged» as `PlanNoPanic` theorems, the write path panic-free (`arrayIndexNatFormed`) | DONE for every user-memory-WRITING apply `stepFn` delivers (stmt ops, target stores, frame entries, unseq loads); the 4 synchronization applies still hand-held (§ owed) | S3 handoff §2–§4 |
| cost B — the drivers hold no pre-step store: `Thread.afterStep σ c c'` read AFTER the step → `boundaryFacts` read BEFORE it; `spawnStep`'s entry commit on the owned store | DONE (S3) | `Multi.lean` `stepThread` |
| cost B(c) — the enumerator's fork copies | NOT C1's: `EnumDedup`'s retained states are exploration's job by design (the charter's B(c) named it; the S3 census says where the boundary is) | S3 handoff §1 |

## The benchmark, BEFORE (main `0f114df6`, `da7bb837…`) / AFTER (S3 tree, `12ebb0e1…`) / AFTER-2 (committed, `ab355547…`)

Same runner/probes/box class as `docs/2026-09-11_bug090-rediagnosis.md` (3 runs, medians, net of the
empty probe; loads in `bench-compare.md`; «a miss is reported as a miss, never re-fitted»). The four S3
targets (charter §6):

| target | BEFORE | AFTER | AFTER-2 (confirmation, quiet box) | verdict |
|---|---|---|---|---|
| `alloc_new` linear; n = 32k < 1 s; ×4 ratios ≤ 4.4 | 0.039 / 0.263 / 3.66 / **14.12 s** (×6.8, ×13.9, ×3.9) | 0.025 / 0.099 / 0.429 / **0.844 s** (×3.9, ×4.3, ×2.0) | 0.025 / 0.097 / 0.434 / **0.865 s** (×3.8, **×4.49**, ×2.0) | MET on AFTER; AFTER-2 the 4k→16k step ×4.49 > 4.4 (a miss on that step by the letter; 32k < 1 s MET) |
| the (h) scalar phase within 1.2× of h = 0 (h = 40k) | 6.83 s vs 0.258 s (26×) | 0.289 s vs 0.257 s (1.12×) | 0.264 s vs 0.283 s (0.93×) | MET (both) |
| `append_grow` successive ×2 ratios ≤ 2.2 (OWED from S1: 2.5–2.8 then) | ×2.0, ×2.1, ×2.5, ×2.9 | ×1.93, ×2.02, ×1.84, ×1.97 | **×2.29**, ×2.04, ×2.17, ×1.97 | MET on AFTER; AFTER-2 the noise-floor 250→500 step ×2.29 > 2.2 (a miss on that step by the letter; the ≥ 0.1 s steps ≤ 2.17) |
| scalar step baseline within 10 % | 1.095 s / 80k×49 steps | 1.057 s (−3.5 %, ≈270 ns/step) | 1.036 s (−5.4 %) | MET (both) |

The 4.4 and 2.2 lines sit inside those two steps' run-to-run jitter (×4.34/×4.49; ×1.93/×2.29 with the
same code); the load-bearing points are stable. Every other probe: `bench-compare.md` (67 points; no probe
slower than 1.06× BEFORE — the map probes, not a C1 target, ±6 % noise; `alloc_make4` 16k 3.41 → 0.38 s;
`heap_then_append` 40k 18.9 → 0.82 s).

## Owed onward

- **To C4 (or the next hygiene slice of this module)**: the four synchronization applies
  (`applyChanOp`, `applySyncOp`, `applyAtomicOp`, `applySelect` + the pool's select interception)
  still deliver with the pre-apply store in hand — one heap copy per registry op that writes a
  channel/sync-word cell; and `applyStrictOp`'s three allocating conversions (`[]byte(s)`,
  `[]rune(s)`, slicing an array value) — one copy each. Not on any S3 target; measured cost owed
  at the next slice (S3 handoff §6 has the split recipe — it is the same seam).
- **To C4**: block-scoped reclamation (`free`), as the charter said; the map index (bug090 §5 item 5).
- **To P**: the wrapper-hop narrowing (charter §3), unchanged.
- **PENDING [USER]** (unchanged from S2c): the ratification of BUG-111 fix (i)'s WIDER scope
  (S2c handoff §6); D1–D7/D9/D10 were ratified 2026-09-18.
