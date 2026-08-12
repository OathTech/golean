# Scheduler-wedge probes — the C2/C3 exhibit, recorded (2026-08-12)

Evidence artifacts for the essence-doctrine audit fix round: the audit's
one confirmed MAJOR was that the doctrine's "definitional bug" exhibit
was garbled — it described a REGISTRY-FREE spinner (probe (b) below),
whose gc observation is in fact IN the modeled set. The genuine
`observed ∉ modeled` exhibit is the SEND-THEN-SPIN shape (probe (a)):
one registry op, then a non-yielding tail. Both probes are recorded
here first-hand so the corrected doctrine text cites a measured record,
not a reconstruction.

Location note: this directory lives under `docs/evidence/`, which the
corpus manifest does NOT scan (`scripts/coverage-manifest` roots at
`Corpus/coverage/exec`; manifest count 1483 before and after adding
these files). These are evidence artifacts, not corpus cases — a corpus
case for shape (a) must wait until a lane can classify a
fuel-out-on-every-stream member honestly (today it would be
unconditionally red in every lane; see the audit's membership-lane
reproduction: `coverage-observations` fails closed on fuel-out
members).

Toolchain: go1.26.5 linux/amd64 (the CI-pinned oracle family);
machine = `.lake/build/bin/golean` built from this branch's tree
(docs-only over `ba6398ab`) via `GOLEAN_MEM_MAX=48G scripts/capped lake
build golean`; wire JSON via `go run ./tools/nativefrontend --dir <probe
dir> --out <wire.json>`; runs via `golean native-json-run --input
<wire.json> --function <fn> [--choices <stream>]`. GOCACHE repo-local
per the sandbox convention.

## Probe (a): send-then-spin — `observed ∉ modeled` (the definitional bug)

`send-then-spin/main.go`: main makes a cap-1 channel, spawns a worker
that sends 42 and then loops with no registry op, and receives.

gc (60 runs, plus 20 at GOMAXPROCS=1 — every run printed `42`, exit 0):

    send-then-spin: exit0-and-prints-42 60/60
    send-then-spin GOMAXPROCS=1: 20/20

Machine, default stream:

    {"message":"GoCore execution fuel exhausted","schema":"golean-observation-v1","status":"fuel-out"}

Machine, systematic stream sweep — ALL {0,1} streams of length ≤ 8
(511 streams including the empty/default stream):

    511 runs -> 511 fuel-out, 0 ok

Corroborating runs, verbatim (status field):

    sts [9,8,7,6,5,4,3,2,1,0] -> fuel-out
    sts [1,3,5,7,9,2,4,6,8,0] -> fuel-out
    sts [5,5,5,5,5,5,5,5] -> fuel-out
    sts [2] -> fuel-out
    sts [3] -> fuel-out
    sts [2,3,2,3] -> fuel-out
    sts default stream, fuel=100000000 -> fuel-out   (10,000x default — a wedge, not a fuel shortfall)

**Why the sweep is exhaustive for this program (the closed
reachable-set argument, [ANALYSIS])**: every `Choices.consume` site the
program can reach has bound ≤ 2 — L1 scheduler pick over ≤ 2 runnable
goroutines, the L5 main-exit window (width 2), the L4 waiter pick with
exactly one candidate (width 1, no consume); no map/append/select sites
exist in the program — and `consume` reduces the drawn value mod the
bound (`State.lean`), so every stream is behaviorally equivalent to its
mod-2 image. A run consumes picks only at pool boundaries with width
> 1; on every branch of this program's tree at most three such
boundaries occur before the wedge (the `.spawned` boundary, then at
most two more while both goroutines are runnable — after the worker's
send apply-position boundary its tail is registry-free, so the pool
never reaches another boundary), after which consumption stops. Hence
the depth-8 mod-2 sweep covers every reachable consumed prefix, and its
uniform fuel-out means **exit-0 is unreachable on EVERY stream**:
gc's observation (exit 0, `42`) ∉ modeled set. The mechanism is exactly
C3 (the fused effect boundary: no post-op scheduling point after the
send that wakes main) + C2 (forced continuation: the worker's
registry-free tail runs privately forever, and main — runnable and
woken — is never scheduled again).

## Probe (b): registry-free spinner — `observed ∈ modeled` (NOT the bug)

`registry-free-spinner/main.go`: main spawns a goroutine that loops
with no registry op at all, and returns 7.

gc (60 runs, plus 20 at GOMAXPROCS=1 — every run printed `7`, exit 0):

    registry-free-spinner: exit0-and-prints-7 60/60
    registry-free-spinner GOMAXPROCS=1: 20/20

Machine (verbatim, status/value):

    rfs [<empty>] -> ok/7          (default stream: gc's observation, produced)
    rfs [0] -> ok/7
    rfs [2] -> ok/7                (2 % 2 = 0 at the width-2 boundary)
    rfs [0,1] -> ok/7
    rfs [0,0,0,0] -> ok/7
    rfs [1] -> fuel-out
    rfs [1,0] -> fuel-out
    rfs [9,8,7,6,5,4,3,2,1,0] -> fuel-out
    rfs [5,5,5,5,5,5,5,5] -> fuel-out

gc's observation IS in the modeled set — the default stream (and every
stream that never picks the spinner at the `.spawned` boundary)
produces it, so the bug definition does not fire on this shape. What
the machine has that gc does not is an EXTRA non-terminating branch
(the streams that always pick the spinner): the too-WIDE,
transfer-safe direction — and possibly not over-wide at all, since the
spec has zero scheduling text (inventory C1) and a cooperative
non-preempting implementation could conformingly hang there. The
spinner is unpreemptible on those streams (that IS C2's pin), but no
observation gc can exhibit on this program lies outside the modeled
set. ∀-stream termination claims on this shape are the FAIRNESS
quantifier's territory (`docs/2026-08-07_fairness-precision-note.md`),
not the C2 re-envelope's: adding preemption points only ADDS streams,
and the never-yielding stream survives any boundary-set widening.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache" GO111MODULE=off
    D=docs/evidence/2026-08-12_scheduler-wedge-probes
    go build -o .tmp/probe-sts "$D/send-then-spin/main.go" && for i in $(seq 60); do timeout 10 ./.tmp/probe-sts; done
    go run ./tools/nativefrontend --dir "$D/send-then-spin" --out .tmp/sts-wire.json
    .lake/build/bin/golean native-json-run --input .tmp/sts-wire.json --function sendThenSpin [--choices "..."]
    # likewise for registry-free-spinner / registryFreeSpinner
