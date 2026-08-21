# Spec-and-community sources — pin index (authoritative home)

Established 2026-08-17 by the spec-and-community truth campaign
(`docs/2026-08-17_spec-and-community-truth-campaign.md` §2/§5 P0).
This file is the authoritative home for the campaign's `scripts/setup-deps`
rows (per that script's derived-pins rule): **when a pin moves here, move
it in the script in the same change.** Everything under `deps/` is
gitignored; this index is what makes it replicable.

## The language-version pin

**GoCore models the Go 1.26 language.** The spec pin, the differential
oracle toolchain, and the corpus must agree on this (campaign doc §4.4):

- spec pin: `golang/go` @ tag `go1.26.5` = `c19862e5f8…` (the `go` row)
- oracle: `go version go1.26.5 linux/amd64` (the installed toolchain
  `go run` dispatches to; verified 2026-08-17)

Re-pin both together, deliberately, with the reason — never one side
alone. The Go 1.22 loop-variable change is the standing reminder that
language version is semantics, not packaging. (Third leg, recorded as
NOT YET EXISTING per the pre-landing audit: the corpus has no
`go.mod`, so "the corpus's `go` directive must agree" has no object
today — the agreement preflight gains that leg when P3/P4 give the
corpus one; until then the check is spec-pin ⟷ oracle only.)

## Repo pins (rows in `scripts/setup-deps`, tier `named`)

| name | rev | role |
|---|---|---|
| `go` | `c19862e5f8415b4f24b189d065ed739517c548ba` (= `go1.26.5`) | THE upper-bound text: `doc/go_spec.html`, `doc/go_mem.html`, `test/` (issue-tagged semantic tests), `src/go/types/testdata`, `src/internal/types/testdata`; release notes in git HISTORY only (23 `doc/go1.*.html` files, all removed from `doc/` before the pin — delta-review nit). Full clone on purpose — P4 mines `git log --follow doc/go_spec.html` and `git log --all` for the release notes. PROMOTED to setup-deps' default tier when `scripts/check-spec-anchors` landed (P2): gate dependencies bootstrap by default, per the goose/verbatim-gate precedent; use `--from` to keep worktree bootstraps local. |
| `covmap` | `2978393a4aed26b9562f5cd040e74507b2a53812` | Candidate 4.1 mechanism (campaign doc §8). Internal repo, no public URL — `--from` only. |
| `go101` | `c13b00435002a00f574430b61eb65ec5a268acfe` | Community corner-case catalog; divergence-ledger *seed only*, every claim independently verified. Shallow reading copy (depth 50). |
| `spectec` | `acc6e834ff403c82554d081237f327346190ad96` | Wasm SpecTec reading copy (P1). Shallow. |
| `esmeta` | `7d237fd1680f473e674320cc97932702d950fa98` | ESMeta/JISET-line reading copy (P1). Shallow. |
| `gofrontend`, `tinygo` | floating (`-`) | Cross-implementation lane, only if P5 green-lights it (§4.5); pin at first real use. |
| `proposal` | `0be13090fdb0cbae0d71641bb676d924bc1c94de` | golang/proposal — design docs behind language changes; committee-intent reconstruction for P4's archaeology (pinned 2026-08-17, closing a P0 gap before the first landing). |

Replicate: `scripts/setup-deps --only go,covmap,go101,spectec,esmeta,proposal`
(covmap needs `--from <checkout-with-deps/covmap>`). NOTE the shallow
caveat: go101/spectec/esmeta here are depth-50 clones; setup-deps
`--from` a shallow copy fails closed (by design) — reclone from the
public URL instead. (This command did not work as written between
2026-08-21's Lake-packages change and its audit fix round the same day:
the new section ran regardless of `--only` and failed on Lake packages
nobody had asked for. `--only` now scopes it — add the pseudo-name
`lake`, or `lake:<pkg>`, when you DO want the Lake checkouts.)

## Papers (`deps/papers/`, fetched 2026-08-17)

Fetched and content-verified (title text extracted and checked):

| file | sha256 (first 16) | what |
|---|---|---|
| `spectec-pldi24.pdf` | `d10fea81655c7b4e` | Youn et al., *Bringing the WebAssembly Standard up to Speed with SpecTec*, PLDI 2024 (doi 10.1145/3656440). https://conrad-watt.github.io/papers/youn2024.pdf |
| `jest-icse21.pdf` | `6036934910e6a1e6` | Park et al., *JEST: N+1-version Differential Testing of Both JavaScript Engines and Specification*, ICSE 2021 (doi 10.1109/ICSE43902.2021.00015). arXiv:2102.07498 |
| `ch2o-krebbers-thesis.pdf` | `dd9afe5b77eab8fb` | Krebbers, *The C standard formalized in Coq*, PhD thesis, Radboud 2015. https://robbertkrebbers.nl/research/thesis.pdf |
| `cerberus-pldi16.pdf` | `396cb0279ce821c9` | Memarian et al., *Into the Depths of C: Elaborating the De Facto Standards*, PLDI 2016. https://www.cl.cam.ac.uk/~pes20/cerberus/pldi16.pdf |
| `featherweight-go-oopsla20.pdf` | `0cfc460cfe22a9e5` | Griesemer et al., *Featherweight Go*, OOPSLA 2020. arXiv:2005.11710 |
| `fg-dictionary-passing.pdf` | `dba5be6423fe5bbd` | *A Dictionary-Passing Translation of Featherweight Go*. arXiv:2106.14586 |
| `fg-semantic-preservation.pdf` | `9d3fb7f9ca2cd0a5` | Sulzmann & Wehr, *Semantic preservation for a type directed translation scheme of Featherweight Go*. arXiv:2206.09980 |

Pending (no open PDF found; paywalled or unlocated — read via the code
checkouts / DOI when needed, or add here when a legitimate copy turns up):

- JISET, ASE 2020 — doi 10.1145/3324884.3416632 (code: `deps/esmeta`,
  legacy kaist-plrg/jiset)
- JSTAR, ASE 2021 — doi 10.1109/ASE51524.2021.9678781
- JSAVER, ESEC/FSE 2022 — doi 10.1145/3540250.3549097 (artifact:
  10.5281/zenodo.6906415)
- Feature-sensitive coverage, PLDI 2023 — doi 10.1145/3591240
- JSCert, POPL 2014 — doi 10.1145/2535838.2535876
- Fava/Steffen/Stolz, *Operational semantics of a weak memory model
  with channel synchronization*, JLAMP 2018 — doi 10.1016/j.jlamp.2018.03.002

## P0 probe results (recorded here because they calibrate the tooling)

**Anchor stability, go1.25.13 → go1.26.5:** the `id="…"` anchor sets of
`doc/go_spec.html` are IDENTICAL (158 anchors, zero added, zero
removed). Anchor-keyed segment names (`@name` = anchor) are safe to
treat as stable across a re-pin; anchor removal is rare enough to be a
loud, investigated event, not routine churn.

**Text churn per release cycle:** 92 insertions / 78 deletions across
that same pair; 13 commits touched the spec over the 1.24→1.26.5 span.
So a re-pin's drift report is expected to touch a handful of sections,
not the whole document — the §8.2 covmap workflow is sized right.
Sample of what the history mining (P4) will find, from the last five
spec commits before the pin: "remove restriction on channel element
types for close built-in (bug fix)" — a spec bug, fixed; exactly a
divergence-ledger seed.
