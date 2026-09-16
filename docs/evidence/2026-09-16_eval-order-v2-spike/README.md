# Reference enumerator over evaluation-occurrence graphs — spike for the evaluation-order model v2 (2026-09-16)

[AGENT] Disposable spike for `docs/2026-09-16_evaluation-order-model-v2.md`
§1–§2 (lane `design/eval-order-model-v2-0916`, main `433e7490`, tree clean).
It validates the RELATION — a sweep as a dependency graph over evaluation
occurrences with guarded regions, legal executions = the readiness-driven
linear extensions, the semantics = the set of their outcomes — and NOT any
lowering: no wire, no frontend, no machine run, no Lean build, no baseline
touched. The graphs are hand-encoded per witness; nothing here proves that
`tools/nativefrontend` or GoCore realizes them.

- Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`); `python3`.
- Host: linux/amd64; nothing here is timing-sensitive.
- Consuming document: the v2 note above (§2 «The reference enumerator», §4 witness column).

## Inputs and outputs

- `enumerate.py` — the enumerator plus the encoded graphs. Per graph: the
  occurrence list (name, dependency edges, body), guards with their regions,
  an initial state, a phase-2 function (the stores / statement completion).
  It enumerates every legal execution (pick any READY occurrence: producers
  done, region enabled; stop at the first failure; then phase 2), records the
  sweep result (status, value or first-failure text, output, frozen state),
  prints each graph's OUTCOME SET with the trajectory count per outcome, and
  asserts the expected set and the absence of the forbidden hybrids. Any
  mismatch makes it exit 1 (fail closed).
- `witnesses/*.go` — the same programs as Go source for the oracle:
  `w1`–`w6` are the review's six witnesses (F1–F6 of
  `docs/2026-09-15_evaluation-order-model-review.md`), `x1`–`x3` cover the
  rest of the review's item-2 fragment (assignment phases, a `||` region
  with an unexecuted case, a buffered receive).
- `outcomes.txt` — the enumerator's output (`RESULT: PASS (0 mismatch(es))`).
- `gc-draws.txt` — gc's draw per program, default flags and `-gcflags=-N -l`
  (one run each; identical). A draw is an OBSERVATION that lies in the set;
  it is not evidence that the other members are unreachable.

## Reproduction (repo root)

    python3 docs/evidence/2026-09-16_eval-order-v2-spike/enumerate.py
    export GO111MODULE=off GOCACHE=$PWD/.tmp/gocache
    for w in w1 w2 w3 w4 w5 w6 x1 x2 x3; do
      go run docs/evidence/2026-09-16_eval-order-v2-spike/witnesses/$w.go
      go run -gcflags='-N -l' docs/evidence/2026-09-16_eval-order-v2-spike/witnesses/$w.go
    done

## Conclusion (2026-09-16)

| graph | relation set | forbidden, shown absent | gc's draw |
|---|---|---|---|
| W1 `v := mut() + a` | {1, 2} | — | 2 |
| W2 `v := a[b[0]] + mut()` | {10, 30, 40} | — | 40 |
| W3 `a[i] += mut()` | {[11 20], [10 21]} | [10 11] | 10 21 |
| W4 `_ = a[1] + b[2]` (both nil) | {`[1] with length 0`, `[2] with length 0`} | — | `[1] with length 0` |
| W5 loop `println(a[0] + mut())` ×2 | {print 7 then panic in iteration 2; panic in iteration 1} | any execution completing iteration 2 | panic in iteration 1 |
| W6 `v := x + inc() + inc()` | {0, 1, 2} | — | 2 |
| X1 `xs[ys[9]], b = zs[7], 2` | {`[9] with length 3`, `[7] with length 3`} | — | `[7] with length 3` |
| X2 `v := b2i(z ‖ h()) + x`, z false / true | {2, 3} / {2} | — | 3 / 2 |
| X3 `x[f()] += <-ch` (buffered) | {panic with len(ch)=0, panic with len(ch)=1} | — | len(ch)=0 |
| C1 `f(g())`, C2 `sink(a)` | singletons (no unordered pair remains) | — | — |
| C3 `sink(a, mut())` | {1, 2} — NOT a singleton (review F9.5) | — | — |

Every set is exactly the one the review states; every gc draw is a member.
The enumerator is the reference the v2 note's §2 describes; its fragment is
the note's certificate fragment (§7). Delete or supersede with the generator
of the note's §6 — nothing cites these bytes beyond the v2 note.
