# Synthetic sampling acknowledgement correction

[AGENT] `typed-preflight`, 2026-09-06 UTC. **Bounded source PASS** for
the four added lines in `scripts/test-lane-validation`, frozen by
`source.sha256`; exact source and diff are retained.

The S1–S6 fake oracle supplies an empty crash report and the exact
`registered\n` acknowledgement expected of a successfully registered real
subject. Its A/B/X observations, mode selection, draw logging, budgets and
expected statuses remain unchanged. This repairs stale mock apparatus;
it does not change the production observer or the sampling rule.

The simulated killed draw still exits 137 and must refuse even with those
files. My separately sealed diagnostic review independently exercised
non-verdict exits with otherwise valid complete panic evidence. Production
and diagnostic negative controls still reject missing registration; this
fixture correction is not a relaxation of that boundary.

The author's full initial CI failure remains real historical evidence;
its affected `--with-go` lane gate was still running at this source review.
I did not rerun it or claim terminal CI/full-corpus success. Final focused
gate completion and ordinary CI after this source change remain owed.
