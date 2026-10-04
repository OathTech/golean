# Changelog after the offer commit `20d3946d` (the post-offer changelog: changes that land on `main` after the window's offer)

For the logic team (`~/projects/golean-logic`) and raft-proofs. The offer itself — the cumulative `61958f2e` → `20d3946d`
move — is `docs/changelog/61958f2e-WINDOW.md`, FROZEN at the offer. This file lists, per landing train, every change after
`20d3946d` that a consumer of GoCore programs, the wire or the raft subject can observe, with its authority. Rows are
appended by the landing train; earlier rows are kept as written. Opened [AGENT] train worker r65, 2026-10-04, closing the
route A S1 adversarial audit's Minor-2 (the consumer-visible init pick had no consumer-facing changelog line).

| Train | Line |
|---|---|
| r65 | route A S1 (train r65): every program linking the subject `proto` consumes ONE `ChoiceSite.intn` pick (bound 2) at package init before `main` (protobuf-go's per-binary error-prefix spelling; slot 0 = U+0020); default tape → slot 0, the twin default-stream observation byte-identical; a positional pre-S1 `--choices` record shifts by one; ∀-stream statements unaffected; twin wire `d5186f43…` → `661022b9…`; subject deltas U-1/U-2/U-3, D-4 retired, D-1/D-3 narrowed; no core/wire-schema/register change. Logic team acknowledged 2026-10-04 (their closed-program theorems assume no package initializer — their planned package-init support); raft-proofs notified 2026-10-04 by the coordinator at the [USER]'s request. Design and build record: `docs/2026-10-04_route-a-protobuf-design.md` §7–§8; merge sign-off [USER] Mike 2026-10-04 «merge it and share» (relayed). |
| r64 | tooling only, no semantic effect: `tools/lowerdiag` (the untrusted lowering-diagnosis tool) now judges the `rand-intn` primitive (`math/rand.Intn`, `math/rand/v2.IntN`) and the float-bits primitive (`math.Float64bits` & siblings) SUPPLIED rather than refused/unmodeled — its static view now agrees with the wire the offer already shipped (row 5b). Commits `ef8dc23d`, `77c5e5dd`; [USER] Mike 2026-10-04 «Yes, approve 1 / 2» (relayed). |
