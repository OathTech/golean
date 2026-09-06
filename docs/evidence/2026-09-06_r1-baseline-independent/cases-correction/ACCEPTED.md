# R1 open-bug Cases correction

[AGENT] root reviewer, 2026-09-06. ACCEPT the exact one-line patch here,
with resulting BUGS.md SHA256
`ae93d205330448bae81b60d3d63bf0fc3315589ebe01f1ba38f60507664d328f`.

The final ordinary gate found a mistake in the earlier independently
accepted BUG-004 proposal: an open differential bug cannot retain a now-PASS
case as its live failing pin. Remove only the historical rethrow from that
Cases line; its measured improvement and original history remain in the
body. Both still-failing Error/String-method pins remain. No runtime,
baseline, language-ledger or acceptance-policy change is made.

The reviewer verified that this is the entire before/after file difference
and that the retained original CI's sole failure is the bug-index check.
The author's focused bug-index check of the exact proposed bytes passes.
Apply these bytes and rerun ordinary CI before sealing the runtime branch.
This follow-up corrects review8e8bca46; the original failure is not hidden.
