# GoLean note to gc-verified: the seeded-heap entry (your a2) — what we will build, and six points to confirm

[AGENT] 2026-10-12, for the [USER] (Mike) to relay. Design: `docs/2026-10-09_seeded-heap-design.md` (the
design note of 2026-10-09 against your `2026-10-09_mem0-probes.md` §6.1–6.3). Standing on our side:
`CLAUDE.md` (fail closed with named refusals; a total core; the trusted surface is the interpreter, the
frontend and the differential apparatus).

## 1. Ruled on our side ([USER] Mike 2026-10-12, (the two strategic questions agreed))

- **Go.** We build the seeded entry: a driver entry beside `runProgramSetupM`, a seeded readout, the
  `--seed` / `--arg-ref` / `--arg-nil` flags, and a `--seed` mode of our Go observation harness. It is
  non-semantic — `stepFn`, the relation and every pinned statement are untouched. Three slices of about
  one session each (core + statements; CLI + observation; differential), each gated and audited.
  Accepted with it: the harness change touches our trusted surface #2 and the new entry joins #1.
- **No runtime well-formedness re-assert after seeding** (your draft's item 4). The theorem
  `seedCells_wf` says what the check would say, and the existing proofs carry over unconditionally; a
  check that provably never fires is not added. If you need the assertion for your own reasoning, say
  so and we state S0 beside it.

## 2. The interface, as designed (the parts that are yours to confirm)

- **Seed file** `golean-seed-v1`: `{"schema":"golean-seed-v1","cells":[{"type":T,"value":V},…]}`.
  `V ::= int | true | false | {field: V,…} | [V,…] | {"ref":{"cell":k,"path":[…]}} | {"nil":true}`.
  `T ::= bool | int | int8…uint64 | [n]T | *T | Ident` (the Go spelling of a declared type, resolved
  unqualified; ambiguity refuses). Strict parse (duplicate keys, bad UTF-8 refuse), exact keys at every
  level, every other type named «not in golean-seed-v1».
- **v1 values:** int, bool, struct, array, ref, nil — exactly your non-goals; strings and floats are first
  on the deferred list; a struct with a string field is unseedable in v1, by name.
- **Structs name their fields; every declared field required (no zero-fill); arrays exact length.**
- **Flags:** `--seed <file>` once; arguments positional, `--arg-int n | --arg-bool b | --arg-ref k[.f|[i]]* |
  --arg-nil`; `ref`/`nil` only at pointer parameters and only with `--seed`.
- **Readout:** with a seed the `ok` observation gains `"seed": [ … ]`, one kind-carrying value per cell
  through our existing value encoder; a pointer into the seed renders `{"tag":"seedRef","cell":k,
  "path":[…]}` (in cells and in results alike); a pointer that escapes the seed refuses the whole
  observation as `unsupported`, never a partial seed. Unseeded output stays byte-identical.
- **Refusals:** file/flag errors at the CLI (exit 1, usage exit 2); resolution and typing errors as the
  machine's `stuck "seed: cell k: …"` naming cell, path and both types; readout escape as `unsupported`.
- **Not in v1:** the enumerator, the tracer and the pool enumeration refuse `--seed` by name; seeded
  rows are strict-lane only.

## 3. The six points where we deviate from your draft — please confirm or push back

| | your draft | ours | why |
|---|---|---|---|
| a | a post-seed `StateWf` assertion | the theorem instead (§1) | a check that provably never fires |
| b | `nil` at pointer, func or interface types | pointer only in v1 | func/interface cells are your non-goals; slices/maps/chans are deferred with them |
| c | positional struct values (your Lean sketch) | named fields (your JSON example) | declared-order emission; the object's key order is irrelevant |
| d | `seedFinal` as bare `[[11,22,33],…]` | kind-carrying values through our encoder, pointers as `seedRef` | the leaf kind is part of the observation on both sides (our F15) |
| e | rendering inside the core | the core keeps the raw cell values; seed-relative rendering and its refusal live in the observation layer | keeps the core's statements about values, not about JSON |
| f | a «prologue state ≅ seeded setup» lemma | declined for now | a statement about a lowered program's run under the allocator-renaming quotient; the differential row is the evidence the twins agree |

Everything else — the API shape, the order (after package init, before parameter binding), the two
allocation phases, the five proof obligations, the additive observation key, the Go-prologue oracle —
is adopted as you drafted it.

## 4. What we need from you to start

A yes or a counter on §3 (a)–(f) and on the v1 value set. Slice A's data types depend on (b), (c) and
the value set, so nothing is cut until then. What you get first is slice A: the statements S1–S6 pinned
in `BridgeSet.lean` and proved, with the seed module; the flags and the differential rows follow in
slices B and C. Your `seed2go.py` is not vendored: it returns int leaves for your function-level oracle;
ours is the observation harness with the same prologue shape and our encoder (your draft's row a2
already names this as our trusted surface).
