# Second-pass evaluation-order counterexamples — v2 review (2026-09-16)

[AGENT] Evidence for `docs/2026-09-16_evaluation-order-model-v2-review.md`.
Reviewed design/enumerator: `9a8ed328711969455bfe1d823c65e858cb919e3a`.
Review base: `433e7490`; these evidence files and the review were uncommitted
when run. Host: linux/amd64. Toolchains: Python 3.12.3;
`go version go1.26.5 linux/amd64` (matches `baselines/go-oracle-pin`).
No Lean build, frontend lowering or machine run.

## Reproduction (repository root)

```sh
python3 docs/evidence/2026-09-16_eval-order-v2-review/check.py
GO111MODULE=off GOCACHE="$PWD/artifacts/go-build-cache" go run docs/evidence/2026-09-16_eval-order-v2-review/probes.go
GO111MODULE=off GOCACHE="$PWD/artifacts/go-build-cache" go run -gcflags='-N -l' docs/evidence/2026-09-16_eval-order-v2-review/probes.go
```

`check.py` reads the reviewed enumerator directly from its git object and adds
four small graph experiments; it does not change the original script. Its exit 0 means
the documented gaps reproduced. The guard graph encodes E1 as an ordinary
dependency, as the proposed readiness rule currently does; a repaired
conditional-edge protocol is the recommended correction, not tested here.

The Go commands each run once. Their identical draws confirm that these source
programs compile and run at the pin; they do not establish the full allowed
sets. `results.txt` records the outputs, with command labels added by the
reviewer. All three commands exited 0 on 2026-09-16.
