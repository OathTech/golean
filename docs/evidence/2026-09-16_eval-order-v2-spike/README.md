# Reference enumerator over evaluation-occurrence graphs — spike for the evaluation-order model v2.1 (2026-09-16)

[AGENT] Disposable spike for `docs/2026-09-16_evaluation-order-model-v2.md`
§1–§2 (lane `design/eval-order-model-v2-0916`, main `433e7490`). The v2
version of this spike (`9a8ed328`) was reviewed by the second Codex review
(`review/eval-order-model-v2-0916` @ `b788e582`,
`docs/2026-09-16_evaluation-order-model-v2-review.md`; its graph
experiments: `docs/evidence/2026-09-16_eval-order-v2-review/check.py`).
This version applies the review's R1 (the read-order reduction is refuted
and retired), R2 (guard entry + completion protocol; order prerequisites
apart from value dependencies; a skip discharges, never produces; the three
scheduler cases; static canonical rank), R6 (header producer split from
the checked access) and the X3 correction (a blocking receive is a
distinct `blocked` REFUSAL, not a `Panic`), and adds an R4 target-identity
witness. It validates the RELATION — a sweep as a dependency graph over
evaluation occurrences with guarded regions, legal executions = the
readiness-driven runs, the semantics = the SET of their results — and NOT
any lowering: no wire, no frontend, no machine run, no Lean build, no
baseline touched. The graphs are hand-encoded per witness; nothing here
proves that `tools/nativefrontend` or GoCore realizes them («reference
graph checks pass» is not «machine equals reference» — Stage C's exit).

- Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`); `python3` (3.12).
- Host: linux/amd64; nothing here is timing-sensitive.
- Consuming document: the v2.1 note above (§2, §4 witness column, §8 acceptance matrix).

## Inputs and outputs

- `enumerate.py` — the enumerator plus the encoded graphs. Per graph: the
  occurrence list (name, VALUE deps, ORDER prerequisites `after`, body),
  guard entries with their regions and completion node, an initial state,
  a phase-2 function (the stores / statement completion). It enumerates
  every legal execution — (i) nothing pending → phase 2; (ii) branch on
  every READY occurrence (deps produced, `after` done-or-skipped, in
  static rank order; slot 0 = least rank = the canonical draw, printed);
  (iii) pending but nothing ready → `Malformed`, refused by name — records
  the sweep result (status, value / first-failure text / refusal text,
  output, frozen state), prints each graph's MEMBER set with trajectory
  counts and its REFUSALS apart, and asserts the expected members, the
  absence of forbidden hybrids, the expected refusals and the expected
  named refusals of malformed graphs. Any mismatch exits 1 (fail closed).
- `witnesses/*.go` — the same programs as Go source for the oracle:
  `w1`–`w6` the first review's witnesses (F1–F6), `x1`–`x3` the rest of its
  item-2 fragment, `r1`/`r2a`/`r2b`/`r2c`/`r4`/`r6` the second review's
  witnesses (R1, R2 skip / completion / nested+earlier call, R4 slice
  replacement, R6 header), `x3e` the empty-channel branch.
- `outcomes.txt` — the enumerator's output (`RESULT: PASS (0 mismatch(es))`).
- `gc-draws.txt` — gc's draw per program, default flags and `-gcflags=-N -l`
  (one run each; identical). A draw is an OBSERVATION that lies in the set;
  it is not evidence that the other members are unreachable.

## Reproduction (repo root)

    python3 docs/evidence/2026-09-16_eval-order-v2-spike/enumerate.py
    export GO111MODULE=off GOCACHE=$PWD/.tmp/gocache
    for w in w1 w2 w3 w4 w5 w6 x1 x2 x3 r1 r2a r2b r2c r4 r6 x3e; do
      go run docs/evidence/2026-09-16_eval-order-v2-spike/witnesses/$w.go
      go run -gcflags='-N -l' docs/evidence/2026-09-16_eval-order-v2-spike/witnesses/$w.go
    done

## Conclusion (2026-09-16, v2.1)

| graph | relation set (members) | forbidden / refused, shown | gc's draw |
|---|---|---|---|
| W1 `v := mut() + a` | {1, 2} | — | 2 |
| W2 `v := a[b[0]] + mut()` | {10, 30, 40} | — | 40 |
| W3 `a[i] += mut()` | {[11 20], [10 21]} | [10 11] absent | 10 21 |
| W4 `_ = a[1] + b[2]` (both nil) | {`[1] with length 0`, `[2] with length 0`} | — | `[1] with length 0` |
| W5 loop `println(a[0] + mut())` ×2 | {print 7 then panic in iteration 2; panic in iteration 1} | any execution completing iteration 2 absent | panic in iteration 1 |
| W6 `v := x + inc() + inc()` | {0, 1, 2} | — | 2 |
| X1 `xs[ys[9]], b = zs[7], 2` | {`[9] with length 3`, `[7] with length 3`} | — | `[7] with length 3` |
| X2 `v := b2i(z ‖ h()) + x`, z false / true | {2, 3} / {2} | — | 3 / 2 |
| X3 `x[f()] += <-ch` (buffered) | {panic with len(ch)=0, panic with len(ch)=1} | — | len(ch)=0 |
| X3e same, EMPTY channel | {panic with len(ch)=0} | refused: `blocked` (5 trajectories), not a member | deadlock (`fatal error: all goroutines are asleep`) = the blocked branch |
| R1 `v := x + y + mut()` | {0, 1, 2, 3} | REDUCED graph (`R_x→R_y`) = {0, 2, 3}: loses 1 — the reduction is refuted | 3 |
| R2a `sink(z ‖ h(), k())`, z true / false | {`k, result true 7`} / {`h, k, result true 7`} | no stuck outcome; the INVALID join (k value-depends on skipped h) refused by name | as the sets (singletons) |
| R2b `sink(left ‖ b, change())` | {false} with E1 at the ‖ COMPLETION | entry-anchored graph = {false, true} — refuted | false |
| R2c `sink(g(), a ‖ (b && h()), k())`, b true / false | {`g k / 1 true 7`, `g h k / 1 true 7`} / {`g k / 1 true 7`, `g k / 1 false 7`} | `h g k …` absent (g before the ‖ operation) | `g k / 1 true 7` both |
| R4 `old := a; a[0] += mut()` (mut rebinds a) | {old [11 20] a [100 200], old [10 20] a [101 200]} | hybrids (read one array, store the other) absent | old 10 20 / a 101 200 |
| R6 `v := a[f()]` | {10, 20} split header/access | FUSED read = {20}: the narrowing | 20 |
| C1 `f(g())`, C2 `sink(a)` | singletons | — | — |
| C3 `sink(a, mut())` | {1, 2} — NOT a singleton (F9.5) | — | — |
| C4 cycle `A↔B` | — | refused by name: «no ready occurrence … malformed graph» | — |

Every set is exactly the one the reviews state; every gc draw is a member
(x3e's draw is the refusal). The enumerator is the reference the v2.1
note's §2 describes; its fragment is the note's certificate fragment (§7).
Delete or supersede with the generator of the note's §6 — nothing cites
these bytes beyond the v2.1 note.
