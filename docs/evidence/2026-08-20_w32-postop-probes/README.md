# Post-op boundary probes — the stage-C exhibition record (2026-08-20)

Evidence artifacts for W3.2 slice 1 stage C (B1 — the `.opDone`
post-op scheduling points; G1 ruling 2026-08-20, boundary-set note
`docs/2026-08-20_w32-boundary-set.md` §2/§6). Two exhibitions, both
run first-hand at this tree (branch `w32-re-envelope`, stage-C
surgery applied):

Toolchain: go1.26.5 linux/amd64; machine = `.lake/build/bin/golean`
built from this tree via `GOLEAN_MEM_MAX=24G scripts/capped lake
build`; wire JSON via `env GO111MODULE=off go run ./tools/nativefrontend
--dir <probe dir> --out <wire.json>`; runs via `golean native-json-run
--input <wire.json> --function <fn> [--choices <n,n,...>]`. GOCACHE
repo-local per the sandbox convention.

## 1. THE WEDGE FLIP — send-then-spin's completing member, exhibited

Probe source: `../2026-08-12_scheduler-wedge-probes/send-then-spin/`
(unchanged — the recorded `observed ∉ modeled` exhibit, register #1).

Machine at this tree:

    default stream        -> fuel-out   (the unfair member — in the
                                         envelope BY RIGHT: dossier §3.1,
                                         the spec allows starvation)
    --choices 0,0,1       -> ok, values [42]   (THE FLIP)
    --choices 0,0,1,0     -> ok, values [42]
    --choices 0,0,1,1     -> ok, values [42]
    --choices 0,1 / 1 / 1,1 / 0,1,1 / 0,0,0,1 -> fuel-out

The `[0,0,1]` trace is the boundary-set note §2 B1's predicted trace,
realized: spawn-completion boundary pick 0 (main, the `l1Sched`-tagged
default), main's recv-apply boundary pick 0 (main parks), worker's
send pairs and wakes main, the NEW `.opDone` postOp boundary pick 1
(= slot 1, main — the issuer-continues slot 0 is the worker), main
delivers 42 and reaches its terminal, L5 exit-now (default). gc's
observation (exit 0, "42" — 60/60 at the phase-A reproduction) is a
MEMBER again: `observed ∈ modeled` restored; the definitional bug
(register #1) is discharged. The dossier's §4.3 verdict — "the
portable model should include the completing execution and an unfair
execution" — is exactly this pair: `[0,0,1]` completes, the default
stream starves.

## 2. U-1 — wake-then-abort, the partner-progress member admitted

Probe source: `wake-then-abort/main.go` (the boundary-set note §6
probe, landed).

gc (200 runs this session, `./wta` built from the probe; println goes
to stderr — captured):

    exit 0:                          0/200
    "42" printed, then exit 2:      60/200
    exit 2, no output:             140/200

(The phase-A record measured 189/200 printed / 11/200 silent — the
dominance ratio is load-dependent; both members are stable gc
observations across sessions, exit-0 observed in neither.)

Machine at this tree (`--function wakeThenAbort`, the subject
observable):

    default stream  -> panic "worker abort in the private segment"
                       (the pre-B1 sole member, preserved as canonical)
    --choices 0,0,1 -> ok, values [42]   (main progresses between the
                       wake and the abort: postOp pick 1, then L5
                       exit-now — the partner-progress class)
    coverage-observations --expect-status ok,panic --max-width 4
      --max-sites 16
      -> observations=2 steps=373 probes=225 sites=75 leaves=76
         maxdepth=15 width=4
      -> {panic "worker abort in the private segment"} and {ok [42]}

Pre-B1 the machine was 127/127 panic over the mod-2 depth-6 sweep
(w32-log, phase A) — the partner-progress class was `observed ∉
modeled`. Post-B1 the class is admitted; gc's print-then-abort member
is the same class at the OUTPUT observable (main's println is main's
progress between wake and abort), with the print-vs-exit split being
L5-tail latitude inside the class. Exit-0 was never observed in gc yet
IS a machine member — the transfer-safe too-wide direction, argued
from spec#Program_execution's "It does not wait for other (non-main)
goroutines to complete" (boundary-set note §6). No observed member
requires post-RAISE partner progress — B3's deferral (G1) is
consistent with this record, which is its trigger baseline.

Corpus row: `Corpus/coverage/exec/goroutines/wake-then-abort/`
(membership, members=2, statuses=ok+panic).
