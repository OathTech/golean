# The `golean` CLI, the wire, and the observation

Living reference, written 2026-10-12 ([AGENT], lane `docs/release-docs-1012`; release-readiness
items 6 and 13). This page describes the current code. Where it and the code disagree, the code
wins: `GoLean/CLI.lean` (the three core subcommands), `GoLean/ChoiceTrace.lean` (`choice-trace`,
dispatched from `Main.lean`), `GoLean/NativeToIR.lean` (the wire decoder) and
`tools/nativefrontend/` (the wire emitter). Please report any disagreement as a bug.

The pipeline:

```
Go package dir ──nativefrontend──▶ wire JSON (golean-native-v3) ──golean──▶ observation JSON (golean-observation-v1)
```

## 1. The frontend: `tools/nativefrontend`

```sh
GO111MODULE=off go build -o .tmp/nativefrontend ./tools/nativefrontend
.tmp/nativefrontend --dir <package-dir> [--out <wire.json>]      # default: stdout
.tmp/nativefrontend --subject --dir <package-dir> [--out <wire.json>]
```

The frontend type-checks the package in `--dir`, together with every case-local package it
imports, using gc's file selection for linux/amd64 (`fileselect.go`). It refuses a `go.mod`
whose `go` directive is not the pinned language version (`modfile.go`). It then emits one wire
for the whole program.

By default the package is a **program**: a `package main` that declares no `func main` refuses
as gc does (`nativefrontend: type-check: function main is undeclared in the main package (<dir>; …)`,
exit 1, no wire; `entrymode.go`, BUG-125). `--subject` is the differential corpus's mode: the
oracle harness supplies `main` around the subject function and the machine's entry is
`--function`, so the check is skipped; it changes nothing else, and is a no-op on a package that
declares `func main`. A non-`main` (library) package is not subject to the rule.

Exit codes:

- 0: a wire was written. **This does not mean every declaration lowered** (see §6.3).
- 1: refused. The first stderr line names the cause, and the second line points at
  `scripts/lower-diagnose <dir>` for the full blocker list.

Other flags (`--stdlib-src`, `--stdlib-pin`, `--stdlib-pin-manifest`, `--stdlib-register`,
`--stdlib-overlay-check`, `--unseq-census`) are apparatus modes used by the gate. They emit no
program. `--allow-hidden-dep-init-order` is an escape hatch (§6.2).

## 2. The subcommands

`golean --help` (or `-h`, or no arguments) prints the usage text and exits 0. An unknown
subcommand exits 2. In every subcommand, a malformed or unknown flag, or a missing
`--input`/`--function`, is a usage error: the message goes to stderr and the exit code is 2.

### 2.1 `native-json-run` — run one function

```
golean native-json-run --input <wire> --function <name> [--seed <file.json>]
    [--arg-int <n> | --arg-bool <true|false> | --arg-ref <k(.f|[i])*> | --arg-nil ...]
    [--fuel <n>] [--choices <n,n,...>] [--no-choice-report | --choice-report=full]
```

This decodes the wire, seeds the package-level variables, runs the package initializer, and then
runs `<name>` on the goroutine pool (`GoLean.GoCore.Machine.runProgramPoolOutM`). It prints
**one** observation JSON line on stdout.

- `--arg-int` / `--arg-bool` bind the entry function's parameters **positionally**, in
  command-line order, and the two flags may be interleaved. Each argument is checked against
  its parameter's underlying type before any step runs (`CLI.entryArgValues`). The run refuses
  by name, with status `error`, if the function is unknown, the arity is wrong, an `--arg-int`
  is passed for a non-integer parameter, an `--arg-int` value is out of range for its kind (it
  is never wrapped), or an `--arg-bool` is passed for a non-`bool` parameter. A malformed
  literal is a usage error (exit 2). One case is not checked here: a parameter of a
  frontend-quarantined function is handed to the machine, which refuses it as `unsupported`.
- `--seed <file.json>` (at most once; a second `--seed` is a usage error) runs the entry over a
  **seeded heap**: the cells of a `golean-seed-v1` file (§2.1.1) are allocated after the package
  initializer and before the entry's parameters, and the run is
  `GoLean.GoCore.Machine.runProgramPoolSeededOutM` (`GoLean/GoCore/SeedPool.lean`). `--arg-ref
  k(.f|[i])*` passes a pointer to cell `k` or to a component of it (`0`, `0.next`, `1[2]`,
  `0.a[3].b`), and `--arg-nil` passes a nil pointer. Both are checked against a **pointer**
  parameter before any step runs: the reference's target type, walked along its path through the
  cell's declared type, must be the parameter's pointee type. A mismatch, an unknown field, an
  out-of-range index or cell, an `--arg-ref`/`--arg-nil` at a non-pointer parameter, and an
  `--arg-int`/`--arg-bool` at a pointer parameter all refuse by name with status `error`. A
  malformed `--arg-ref`, or `--arg-ref`/`--arg-nil` without `--seed`, is a usage error (exit 2).
  The observation gains a `seed` key, and every pointer in it is written relative to the seed
  (§4). Without `--seed` nothing changes: the same driver and byte-identical output.
- `--fuel` is the step budget, counted in machine steps (default 10 000 000). Running out gives
  status `fuel-out`.
- `--choices` is the choice tape (§5, and the caveats in §6.1). It defaults to empty, which
  selects the canonical member at every choice site.
- **The choice report** (F1 of the 2026-10-13 fail-closed pass). When the run consulted a choice
  site (§5) with more than one option, its observation is **one member of a set**, not the
  program's only behaviour. `native-json-run` says so on **stderr**, after the observation. stdout
  is the same in every mode (byte-identical to `--no-choice-report`), and so is the exit code,
  except for the full pass's refusal below.
  - **Default: the count, with no replay.** The run itself is made on the given tape followed by
    K = 2^20 zeros, and the count is read off the tape the run leaves over: N = |tape| + K −
    |leftover|. A drawn 0 selects slot 0, the same as an exhausted tape, and a one-option consult
    draws nothing (`Choices.consumeAt`). So the padded run is the unpadded run: the eval tests pin
    this over the driver, and `CLI.runProgramPoolOutLeftoverM_fst` proves the wiring half. The
    count is exact while the leftover is non-empty. If all K zeros were used it is a lower bound,
    and the line says «at least». Lines:

    ```
    native-json-run: consulted 1 choice site(s); the observation is one member of a set — see coverage-observations (the certified set) and choice-trace (the sites)
    native-json-run: consulted 4 choice site(s); the observation is the member the stream [1] selects of a set — see coverage-observations (the certified set) and choice-trace (the sites) (stream exhausted at consultation #2; the rest drew the canonical 0)
    ```

    N counts consultations, not distinct sites (a site consulted twice counts twice). Nothing is
    printed when N = 0. For a status the enumerator does not certify (anything but `ok`, `panic`
    and `race`, e.g. a readout refusal `unsupported`), the pointer to the certified set becomes
    «no enumerator certificate for status X». The driver returns a leftover tape only when the run
    reaches main's exit. On every other ending (panic, deadlock, fuel-out, a refusal, a setup or
    `$pkginit` failure) the count is not available, and the line says so instead: «choice
    consultations not counted — the run ended with status X, for which the driver returns no
    leftover tape; …». A count-free line is never omitted on a MACHINE ending (a CLI-level refusal before the driver — arity, a wrong `--arg-*` kind, a bad seed file, a missing function — prints nothing: no step ran, zero is exact) on such an ending. Cost: one list of
    2^20 zeros, about 50 MB more peak memory and no measurable time.
  - **`--choice-report=full`**: also runs `choice-trace`'s accounting pass
    (`GoLean.ChoiceTrace.consumptionReport`, the same loop as §2.4) on the same wire, arguments,
    seed, fuel and tape. Its line names each site with its count and bound, for example
    `appendSpill=1 (bound 32)`, or `bounds lo–hi` when the bounds differed. The pass must agree
    with the run, or the run is **refused** (status `error`, «consumption accounting disagrees
    with the driver …», exit 1, the observation withheld). Agreement means the enumerator driver's
    observation equals the run's, the tracer's count equals the padded count (when exact), and
    there are no tracer alarms or menu-invariant violations. It also counts on endings where the
    default cannot. Cost: it steps the run twice more (tracer and enumerator driver). Measured on
    2026-10-13: a 200k-append run 17 s → 56 s (3.2×), sequential long runs about 4.6×, an
    8-goroutine probe 0.45 s → 2.0 s, and `goroutines/send-then-spin` 2.7 s → 342 s (about 125×;
    476 190 consultations). Memory is linear in steps, about 94 B/step, so about 1 GB at the
    default fuel.
  - **`--no-choice-report`**: no line, and the driver runs on the unpadded tape exactly as before.
    The differential runner passes it, because its depth guard accounts every strict row already.
    So do the tools that merge stderr into a captured observation (`scripts/gotest-triage`,
    `scripts/cedar-census`, `scripts/detector-soundness`) and the raft tools. At most one of the
    two flags may be given; a second is a usage error. The other subcommands refuse both flags.

Exit codes: **0** if the status is `ok`, **1** for every other status (including `error`),
**2** for a usage error. Before any step runs, these failures produce a `status:error` JSON on
stdout with exit 1: an unreadable input (`<path>: cannot read input: <OS error>`), a JSON parse
error (the strict parser refuses duplicate keys, unpaired surrogates and invalid UTF-8), a
decoder refusal, and an entry-argument refusal; with `--seed`, also an unreadable seed file and
a seed-file refusal (§2.1.1).

#### 2.1.1 The seed file: `golean-seed-v1`

```
{"schema":"golean-seed-v1","cells":[{"type":<TypeSpelling>,"value":<SeedJson>}, …]}
SeedJson     ::= <integer> | true | false | {<field>: SeedJson, …} | [SeedJson, …]
               | {"ref":{"cell":<nat>,"path":[PathElem, …]}} | {"nil":true}
PathElem     ::= "<field>" | <nat>
TypeSpelling ::= bool | int | int8 | … | uint64 | uint | [<nat>]T | *T | <Ident>
```

Example: two `Node` cells that point at each other (a cycle), then a `*int` cell pointing at
element 1 of an array field:

```json
{"schema":"golean-seed-v1","cells":[
  {"type":"Node","value":{"next":{"ref":{"cell":1,"path":[]}},"val":2}},
  {"type":"Node","value":{"next":{"ref":{"cell":0,"path":[]}},"val":3}},
  {"type":"Pair","value":{"a":[1,9,3],"b":true}},
  {"type":"*int","value":{"ref":{"cell":2,"path":["a",1]}}}]}
```

The CLI decodes the file's **shape** (`GoLean/SeedFile.lean`). The machine's resolver decides
the **typing**, once, at setup (`GoLean/GoCore/Seed.lean`). Both refuse by name.

- **At the CLI** (status `error`, exit 1, before any step): the file goes through the strict
  byte parser (duplicate keys, invalid UTF-8 and unpaired surrogates refuse). Every object needs
  exactly its keys. The schema must be the literal `golean-seed-v1`. A number with a fraction or
  an exponent refuses, even `1e2`, and so does the token `-0` (its sign would be lost). `null` and strings are not values. `{"nil": x}` needs
  `x = true`. A `ref` or `nil` object may carry nothing else, so **any** struct with a field
  named `ref` or `nil` cannot be written in v1; the refusal says so. A type spelling outside the grammar refuses as
  «not in golean-seed-v1», naming its class: `uintptr`, floats, complex, `string`, `byte`/`rune`
  (spell them `uint8`/`int32`), `[]T`, `map`, `chan`, `func`, `interface`/`any`/`error`, an
  anonymous `struct{…}`, `sync.*`, and any package-qualified name. A declared type whose name
  merely starts like a keyword (`channel`, `funcTable`, `structure`) is an ordinary `<Ident>`.
  An `<Ident>` is a declared type's **unqualified** Go name, as the observation spells it (`Node` for `main.Node`). It
  refuses if no declared type has that name, and it also refuses if more than one does (two local
  types `T` in different functions, say): it never picks one. A builtin spelling (`int`, or one
  outside v1 such as `float64`) that a declared type also uses refuses the same way. A refusal
  inside `*T` or `[n]T` names the whole spelling.
- **In the machine** (status `stuck`, message `seed: cell k: …` or `seed: argument i: …`): an
  int outside its kind's range (it is never wrapped), a struct missing a declared field or naming
  an unknown or duplicate one (every field is required and nothing is zero-filled), a blank `_`
  field (Go literals cannot set one), an array of the wrong length, a `ref` to a missing cell or
  along a bad path, a `ref` whose target type is not the pointer's element type, `nil` at a
  non-pointer type, and a value at any type outside v1 (a struct with a `string` field cannot be
  seeded).

All cells are allocated before any is filled, so sharing and cycles are ordinary. Sharing is
when two pointers name one cell; a cycle is when cells point at each other.

### 2.2 `observation-eq` — the comparator

```
golean observation-eq --left <json> --right <json>
```

Both arguments are observation JSON *strings*. Each is decoded strictly (§4), and the two are
compared by structural JSON equality. Exit codes: **0** if equal; **1** if they differ (both
are printed on stderr); **2** if either side fails to decode, which means the comparator did
not decide (the cause is printed on stderr). The differential harness (`scripts/diff-coverage`)
calls it once per row, with the Go side's observation (from `tools/coverageharness`) and the
Lean side's.

### 2.3 `coverage-observations` — enumerate the observation set

```
golean coverage-observations --input <wire> --function <name>
    [--arg-int <n> | --arg-bool <true|false> ...] [--fuel <n>] [--engine dedup]
    [--max-width <B>] [--max-sites <D>] [--cap <N>] [--work-cap <W>]
    [--expect-status <ok|panic|ok,panic|race>]
    [--allow-nonterm-iters <K>] [--backedge <full|k>]
```

This explores the whole choice tree of the run and prints every **distinct** observation, one
JSON per line on stdout, sorted. A summary line goes to stderr
(`coverage-observations: observations=… steps=… …`). The membership lane uses this command:
there, every `go run` sample must be a member of the printed set. On the default (DFS) engine
every cap fails loudly and never truncates: `--max-width` (default 16) caps each site's computed
bound, `--max-sites` (default 8) caps the number of consumption sites per run, `--cap` (default
64) caps the number of distinct observations, and `--work-cap` (default 200 000) caps exploration
steps. **With `--engine dedup` only `--work-cap` and `--expect-status` are read:** a dedup
certificate is about the whole state graph, not a budgeted exploration, so `--cap`, `--fuel`,
`--max-width`, `--max-sites` and `--backedge` have no meaning there and are refused by name (exit 2)
rather than accepted and ignored (release-readiness item 27, from the 2026-10-12 release-trust
review F3; the inert width/sites were known from the 2026-09-20 stage-D audit). The corpus manifest
and the runner refuse `width=`/`sites=`/`cap=`/`backedge=` on an `engine=dedup` row the same way.
`--expect-status` declares the allowed status set; a member outside it fails the run.
`--allow-nonterm-iters K` counts a branch that re-enters a loop more than K times as
non-terminating rather than as a member. `--backedge` sets the enumeration mode at loop
preemption points; if it is undeclared, a back-edge consult of bound ≥ 2 fails. With
`--engine dedup`, the state-graph engine runs and the result is checked by the verified
certificate checker (`Machine.checkCert`). It refuses, by name, programs with a `$pkginit`
phase, and it refuses `--allow-nonterm-iters`. `--seed`, `--arg-ref` and `--arg-nil` are refused
by name (exit 2): the enumerator does not seed in v1 (seeded corpus rows are strict-lane only).
`choice-trace` does seed (§2.4). The old flag `--allow-nonterm` is retired and
refused by name. Exit codes: **0** if the set was printed; **1** for a refusal, a setup failure
or a tripped cap (the message on stderr starts `coverage-observations:`); **2** for a usage
error.

### 2.4 `choice-trace` — the labelled-consumption tracer

```
golean choice-trace --input <wire> --function <name> [--seed <file.json>]
    [--arg-int <n> | --arg-bool <b> | --arg-ref <k(.f|[i])*> | --arg-nil ...]
    [--fuel <n>] [--stream <spec>]... [--trace]
golean choice-trace --batch <manifest.tsv> --out <results.tsv> [--dump <file>]
    [--fuel <n>] [--skip <k>] [--take <n>]
```

This replays one or more tapes (`--stream`: `default` (the empty tape), `n,n,...`, or
`rand:<seed>:<len>`). It records every consumption the machine makes (site, bound, the tape
value drawn or EXHAUSTED, and the realized pick) and checks the per-site menu invariants. Its
output is one TSV row per stream on stdout (columns: `id stream status consumed wide
exhaustedAt wideAfterExhaustion perSite maxBound violations firstViolation alarms firstAlarm
obsHash driverAgreement`). With `--trace`, every consumption is also printed on stderr. In
batch mode it reads a manifest (`id \t wire \t function \t args(csv|-) \t streams(;-separated)`)
and appends results to `--out`, resuming past ids already present. `golean choice-trace --help`
prints the full usage. `--seed`, `--arg-ref` and `--arg-nil` work as for `native-json-run`
(§2.1, §2.1.1): the seed is placed after the package initializer, so a seeded corpus row's depth
guard traces the seeded run itself. Its driver-agreement check then compares the tracer and the
enumerator driver (both seeded the same way) against the seeded pool entry
`runProgramPoolSeededOutM`, on the raw-id rendering of the results. The seed flags are refused in
batch mode (the manifest has no seed column), and `--arg-ref`/`--arg-nil` without `--seed` are a
usage error (exit 2). Exit codes: **0** if no violation, alarm or driver disagreement was
found; **1** otherwise, or on a refusal; **2** for a usage error. Known defect: a failed
*write* of the batch results or dump file escapes as the runtime's uncaught-exception message,
which is fail-closed but not in the subcommand's own refusal shape (BUG-122).

## 3. The wire: `golean-native-v3`

**The normative definition is the decoder**, `GoLean/NativeToIR.lean`, and in particular
`decodeProgram` and the allowed-key tables `tyAllowedKeys`, `exprAllowedKeys`,
`stmtAllowedKeys`, `targetAllowedKeys` and `rangeAllowedKeys`. The emitter
(`tools/nativefrontend/emit.go`, `wire.go`) is the only producer. This section is a map of the
decoder, not a replacement for it.

**Discipline.** The decoder enforces these rules throughout:

- Exact keys: an unknown key at any node is refused, naming the key and its path.
- Every key the decoder reads is required, unless the Go grammar makes it optional (`cond` on
  `for {}`, `cap` on `make(chan T)`).
- Duplicate type ids, function ids, globals, method-set records and promotion records are
  refused.
- The JSON is parsed from bytes by `StrictJsonParse.lean`, with a nesting limit of 1024.
- Older schemas are refused by name. `golean-native-v1` predates the 2026-09-28 promotion
  records, and `golean-native-v2` predates the 2026-09-30 numeric locals.

**Program object** (top level):

| key | | content |
|---|---|---|
| `schema` | required | `"golean-native-v3"` |
| `buildContext` | required | `{goos, goarch, compiler, cgoEnabled, buildTags}`. Must equal the pin `linux/amd64/gc`, cgo on, no tags (`pinnedSelectionTarget`), or the wire is refused (BUG-108). |
| `types` | required | the type table, in dependency order: `{name, display, pkg, def}`, where `def.kind` is `struct {fields:[{name,type,embedded}]}`, `defined {target}`, `interface {methods:[{id,params,results,variadic}]}` or `unsupported {feature}`. `alias` is refused. Two machine-reserved entries precede the table, so wire entry k is table index k+2. A forward reference or a cycle is refused (`TypeEnv.WellFounded`). |
| `funcs` | required | `{name, params, results, variadic, body, locals}`, or the quarantine stub `{name, unsupported, arity}` (§6.3) |
| `methods` | required | `{id, recvType, recv, params, results, variadic, interface, unsupported, body, locals}`, which covers declared methods, interface anchors and imported stubs. The old `wrapper` marker is refused. |
| `methodSets` | required | `[{type, coverage: "full"\|"exported"}]` |
| `promotions` | required | `[{type, member, inPtrSetOnly, path:[{owner,field,ptr}], adjust: "asIs"\|"deref"\|"addr", target, unsupported, sig}]`. These records are the only source of promoted method-set entries. |
| `globals` | optional | `[{name, type}]` in declaration order. Global i is seeded at `Loc.base ⟨i⟩`. |
| `package`, `fileOrder` | emitted, not read | metadata |

**Locals** (`locals`, per function or method): `[{name, kind, pos?, wire?}]`, where `kind` is one
of `recv`, `param`, `result`, `capture` or `local`. Every source local on the wire carries its
`local` index into this table. `$`-temporaries are interned by the decoder and never appear in
the table. **Params**: `{id, type, local}`.

**Type nodes** (`kind`): `bool`, `string`, `int {int: int|uint|int8…uint64|byte|rune|uintptr}`,
`float {float: float32|float64}`, `pointer {elem}`, `slice {elem}`, `array {len, elem}` (with a
length budget of 2^16, `arrayLenBudget`), `chan {dir: both|send|recv, elem}`,
`map {key, value}`, `sync {sync: Mutex|RWMutex|WaitGroup|Once}`, `named {name}`,
`interface {name}`, `func {params, results, variadic}`.

**Expression nodes** (`expr`; most also carry an optional `type`): `ident`, `func-value`, `int`,
`bool`, `float {num, den}`, `string {bytes}`, `nil`, `recover`, `bytes-from-string`,
`string-from-bytes`, `string-from-rune`, `runes-from-string`, `string-from-runes`, `float-bits`,
`min`, `max`, `ref`, `globaladdr`, `deref`, `addr-of-deref`, `field-get`, `field-addr`,
`index-get`, `index-addr`, `builtin-len`, `builtin-cap`, `map-get`, `slice`, `convert`,
`default`, `struct-lit`, `array-lit`, `unary`, `binary`, `to-interface`, `type-assert`. The
call-shaped nodes `call`, `call-value`, `atomic-op`, `rand-intn` and `sync-op` are accepted
only as the right-hand side of an `assign`/`expr` statement, because GoCore has no call
expression. In expression position they are refused by name.

**Statement nodes** (`stmt`): `block`, `breakable`, `defer`, `go`, `panic`, `return`, `assign`,
`type-assert`, `var`, `if`, `for {init, cond, post, condPre, body}`, `range` (per `kind`: `map`,
`chan`, `slice`, `array`, `int`, `array-pointer`, `string`), `incdec`, `compound-assign`,
`expr`, `new`, `make-slice`, `make-map`, `make-chan`, `chan-send`, `chan-recv`, `chan-close`,
`sync-op`, `select`, `map-delete`, `clear-map`, `clear-slice`, `print`, `append`, `copy`,
`unseq-probe`, `unseq`, `map-compound-assign`, `map-assign`, `slice-lit`, `map-lit`, `break`,
`continue`, `break-to`, `continue-to`, `labeled`. **Assignment targets** (`target`): `declare`,
`var`, `blank`, `addr`, `map`.

Known open defect: a range or discard temporary whose node lacks `type` is declared `int`
instead of being refused (`exprTypeOf`). This is release-readiness item 2, being fixed in the
lane `fix/release-runtime-1012`.

History, not normative: the schema's design rationale is spread over
`docs/2026-08-04_control-flow-design.md`, `docs/2026-08-05_init-design.md`,
`docs/2026-08-10_method-set-record-contract.md`, `docs/2026-08-18_multipackage-identity.md`,
`docs/2026-09-05_fr19-bug097-design.md` (type displays),
`docs/2026-09-28_gp-method-promotion-design.md` (v2) and
`docs/2026-09-30_numeric-locals-design.md` (v3).

## 4. The observation: `golean-observation-v1`

The encoder is `CLI.runJson` / `CLI.errorJson` / `CLI.goValueJson`. The strict decoder, which
is the contract both sides of the differential meet, is `CLI.decodeObservation`.

```json
{"output":"","schema":"golean-observation-v1","status":"ok","values":[{"kind":"int","tag":"int","value":6}]}
{"message":"runtime error: index out of range [2] with length 2","output":"","schema":"golean-observation-v1","status":"panic"}
```

- `status = "ok"`: the keys are exactly `output, schema, status, values`. `values` holds the
  entry function's results in order. A `--seed` run adds one key, `seed`: the final value of each
  seed cell, in cell order, rendered like `values`. No other key set decodes.
- Any other status: the keys are exactly `message, output, schema, status`.
- `output` is the bytes the program wrote with `print`/`println` (fd 2), folded in step order,
  and it is present on every status. Output that is not valid UTF-8 is emitted as an object,
  which the decoder refuses by name rather than comparing it lossily.
- A **CLI-level** `error` (unreadable file, parse or decode failure, bad entry arguments, a seed
  file refusal) is shaped like every other non-`ok` status, with `output` the empty string: no
  step ran, so the program wrote nothing. It decodes, and `observation-eq` compares it. (Since
  2026-10-12, release-readiness item 22; before, it had no `output` key and the decoder refused
  it. The change is additive, so the schema name stays `golean-observation-v1`; the decoder's
  exact-keys rule for `error` did not change.)
- The Go observer (`tools/coverageharness`) refuses a result it cannot observe as `status:error`
  naming the cause. It cannot see its own fd 2, so the runner (`scripts/diff-coverage`) splices
  `output` in before decoding; the compared Go observation therefore has the same key set.

**Statuses** (`Stop.status`, `GoLean/GoCore/Value.lean`):

| status | class | meaning |
|---|---|---|
| `ok` | Go | normal completion |
| `panic` | Go | an unrecovered run-time panic; `message` is gc's abort text |
| `fatal` | Go | an unrecoverable runtime throw (`fatal error: …`, e.g. sync misuse) |
| `deadlock` | Go | no runnable goroutine (gc's detector line) |
| `race` | Go (refused per run) | the happens-before detector found a data race; the oracle is `go run -race` |
| `unsupported` | refusal | a construct the model does not cover, named (the frontier) |
| `stuck` | refusal | the machine received a program outside the lowering contract, which means a frontend bug |
| `error` | refusal or CLI | a machine invariant broke (`Refusal.internal`), or a CLI-level failure (above) |
| `fuel-out` | apparatus | the step budget ran out; this is a model artifact, not a program behaviour |

A refusal never counts as a pass.

**Value tags** (`tag`, exact keys per tag):

| tag | keys | notes |
|---|---|---|
| `unit`, `nil` | `tag` | |
| `bool` | `value` | |
| `int` | `kind`, `value` | `kind` is one of the ten concrete integer kinds, and `value` is range-checked per kind (`uintptr` — a distinct kind on the machine since 2026-10-12, BUG-124 — is refused at this seam by name on both sides; the Go observer refuses `reflect.Uintptr` first) |
| `float` | `kind`, `bits` | the IEEE bit pattern; every NaN is canonicalized to the quiet NaN; signed zero is kept |
| `string` | `bytes` | an array of byte values |
| `interface` | `dynamic`, `value` | `dynamic` is the dynamic type's name, unqualified, as `reflect.Type.Name()` gives it |
| `struct` | `typeName`, `fields:[{name,value}]` | the anonymous empty struct's `typeName` is `""` |
| `array` | `values` | |
| `slice` | `base`, `offset`, `len`, `cap` | `base` is a location or `null` |
| `map`, `chan` | `base` | a location or `null` (reference identity) |
| `addr` / `fieldAddr` / `indexAddr` | `id` / `base, typeName, fieldName` / `base, index` | a location |
| `seedRef` | `cell`, `path` | a location relative to the seed, in a `--seed` observation only (below) |
| `func` | (none) | **never emitted**, and the decoder has no such tag. The rule is that a **func-typed position, static or dynamic, refuses by name on both sides**. A Go func value has no observable identity: it is not comparable, has no stable address, and a closure's captures are invisible. The machine checks two things. First, each result's declared type: a func type, a declared func type (`type Fn func(…)`), or a func reached through array elements or the fields of a declared struct. That check catches a nil func too. Second, the value itself: a func value, or an interface box whose dynamic type contains a func in the same way (for example `any(Fn(nil))`). Either way the readout refuses with status `unsupported` and the message `observation of result i, which has … / holds … : a Go func value has no observable identity …`. `native-json-run`, the enumerators («cannot certify the observation set») and `choice-trace` (status `unsupported`) all refuse the same way. The Go observer refuses `reflect.Func` by its static kind, nil or not, including inside an interface box. A seeded run applies the value check to the seed cells too (`seed cell k`). That is only a guard: no golean-seed-v1 file can place a func-typed position today |
| `syncData` | `state` | diagnostic only; the decoder refuses it |

**Seeded observations.** With `--seed`, every location in `values` and `seed`, whether a
pointer or the base of a slice, map or channel, is written relative to the seed as
`{"tag":"seedRef","cell":k,"path":[…]}`. The path is root-first: field names as strings,
indices as nats. A location outside the seed (a parameter, a result, a global or a cell
allocated by the run) has no such spelling. The **whole** observation then refuses with status
`unsupported`, `seed readout: result i holds a pointer outside the seed …` (or `cell k`); it is
never reported partially. The decoder accepts `seedRef` only inside an observation that has a
`seed` key, with `cell` below the seed's length and exactly the keys `cell, path, tag`. Without
`--seed` the observation is unchanged. Here is `next(&c0)` over the cycle example above, first
in the raw-id shape the seed mode replaces (not producible for this entry, which needs a
pointer argument) and then as the seeded run prints it:

```json
{"output":"","schema":"golean-observation-v1","status":"ok","values":[{"id":1,"tag":"addr"}]}
{"output":"","schema":"golean-observation-v1","seed":[{"fields":[{"name":"next","value":{"cell":1,"path":[],"tag":"seedRef"}},{"name":"val","value":{"kind":"int","tag":"int","value":2}}],"tag":"struct","typeName":"Node"},{"fields":[{"name":"next","value":{"cell":0,"path":[],"tag":"seedRef"}},{"name":"val","value":{"kind":"int","tag":"int","value":3}}],"tag":"struct","typeName":"Node"},…],"status":"ok","values":[{"cell":1,"path":[],"tag":"seedRef"}]}
```

Locations carry the machine's **raw allocation ids** (stated limit 5 of the 2026-10-03 offer).
Two runs agree on them only if they allocate in the same order, so the differential's comparable
surface for pointers is what the corpus rows pin, not address equality in general.

## 5. The choice tape, from the command line

Wherever Go permits several behaviours (map iteration order, append capacity, which goroutine
runs, which ready `select` clause commits, …), the machine consults a **choice site**
(`ChoiceSite`, `GoLean/GoCore/State.lean`). Each consult draws one entry from the tape via
`Choices.consumeAt`. Slot 0 is the site's canonical member (`ChoiceSite.canonicalSlot0`), so the
empty tape gives the default run. A consult with only one option (bound ≤ 1) draws nothing.
`--choices 1,0,2` supplies the tape to `native-json-run`. `choice-trace --trace` shows which
site drew which entry. The semantics of the tape is in `docs/semantics-overview.md` §6.

## 6. Three deliberate escape hatches

None of these is a bug. Each one makes a convenience silent, and you should know where it
applies.

### 6.1 The tape wraps, defaults, and is not checked for leftovers

`Choices.consume` (`GoLean/GoCore/State.lean`, the raw pop under `Choices.consumeAt`) takes an
entry **modulo the bound** (`c % b`). An out-of-range pick such as `--choices 7` at a two-way
site silently selects slot 1. An **exhausted** tape yields slot 0 at every later site. And
`native-json-run` never checks for **leftover** entries: extra entries, or entries meant for a
site the run never reached, are ignored.

- *Where it bites:* a hand-written tape that is too short, too long or out of range still runs,
  and reports an observation for a tape other than the one you meant.
- *Why it is deliberate:* it makes every list of naturals a valid tape (the enumerator and the
  proofs quantify over all of them), and it makes the empty tape the canonical run.
- *How to tell:* `native-json-run` itself now says on stderr how many choice consultations the
  run made, and where your tape ran out (the choice report, §2.1). On an ending without a
  leftover tape it says the count is unavailable, so a single run's observation is never silently
  a point answer. `--choice-report=full` adds the sites and bounds. For every consultation, run
  `golean choice-trace --input <wire> --function <f> --stream <your tape> --trace`. The row's `consumed` and `exhaustedAt` columns, and the per-consumption lines
  (bound, the tape value drawn, the realized pick), show exactly what was used, what wrapped,
  and where the tape ran out.

### 6.2 `--allow-hidden-dep-init-order` turns a refusal into a warning

The frontend refuses a program whose package-variable initialization depends on a hidden
dependency (latitude E7: our order follows go/types and is known to differ from gc's).
`--allow-hidden-dep-init-order` lets such a program lower anyway, printing
`nativefrontend: WARNING (E7 allow active): …` on stderr (`tools/nativefrontend/hiddendep.go`)
and exiting 0.

- *Where it bites:* the wire realizes an initialization order that gc does not.
- *Why it is deliberate:* the apparatus passes the flag for exactly one recorded deviation case,
  `init/hidden-dep-order`, keyed by id in `scripts/diff-coverage` and
  `scripts/check-frontend-pins`. It is not a user default.
- *How to tell:* the stderr WARNING line. Do not pass the flag yourself.

### 6.3 A wire is not a lowering certificate

When a single declaration cannot be lowered (an unsupported construct inside it), the frontend
**quarantines** that declaration instead of refusing the package. It emits a stub
(`{"name", "unsupported": <cause>, "arity"}` for a function; a method keeps its real signature
and carries `unsupported`) and **exits 0** (`tools/nativefrontend/emit.go`, the per-declaration
quarantine in `emitProgram`). Calling a stub at run time refuses with status `unsupported` and
the message `frontend-quarantined: <cause>`.

- *Where it bites:* exit 0 from the frontend says only that a wire was written. Functions you
  never call may be stubs, and so may functions you do call (you find out when the call happens).
- *Why it is deliberate:* one unsupported helper should not hide every other function in the
  package from the differential.
- *The materialization budgets too (BUG-078, since 2026-10-13):* an array type past the
  interpreter's budgets (`tools/nativefrontend/budgets.tsv`) or a constant-count `make` past the
  footprint budget quarantines the declaration that spells it, a package-level var of such a type
  is poisoned (its readers are stubs), and a declared type that reaches one ships as an
  existence-only `unsupported` TypeDef whose users are stubs. The decoder keeps the same checks
  as a whole-wire backstop, so a hand-built wire that carries such a type is still refused whole.
- *How to tell:* `jq '[.funcs[], .methods[] | select(has("unsupported")) | {name, id, unsupported}]' wire.json`
  lists every stub before you run anything. For the full blocker picture, run
  `scripts/lower-diagnose <dir>`.
