# Evidence — adversarial audit of the Stage B `unseq` scheduler (2026-09-16)

[AGENT] Auditor, branch `review/unseq-stage-b-0916` at the candidate tip `ba8767da`. The report is `docs/2026-09-16_unseq-stage-b-audit.md`. Everything here is scratch that IMPORTS the candidate (no candidate source copied); `.lean.txt`/`.py.txt` are the scratch sources (renamed so no build glob picks them up), `.out.txt` their captured outputs with exit codes. Regenerate any `.out.txt` with `scripts/capped lake env lean <file>.lean` from a copy under `.tmp/` (the files end in `#eval …main []`; `--run` cannot be used because the imported test module already declares `main`).

| file | what |
|---|---|
| `AuditA.lean.txt` / `AuditA.out.txt` | items (a) edge sorts and the skip protocol (A1, A3, A4, A5), (b) the source-scope cell idiom (B1, B3a–d, B4, B5), (c) atoms and frozen identity (C1, C1b, C2, C3, C4), (j) J2 one-pick consumption, (k) K1 legacy mixture. 21 expectations met, 4 «unmet» = the auditor's own arithmetic on J1 (g returns x+1; corrected in J) and on K1's set (the probe's own two members; corrected in J) — the findings F1 (A4/A5), F2 (C1), F3 (B4) are the MET lines whose expected member is the fail-open outcome |
| `AuditI.lean.txt` / `AuditI.out.txt` | item (i): I1–I4b, six exact sets |
| `AuditJ.lean.txt` / `AuditJ.out.txt` | item (j) J1 corrected (tape untouched; straight-line control), K1 corrected, A6 invoke arity, A8 skipped TARGET store refused |
| `AuditK.lean.txt` / `AuditK.out.txt` | R5: `x := e` via `.initialization` in `thenB` (K2 mid-block, K3 loop); N3 mistyped completion cell (refused, generic text — the «unmet» line is the auditor's needle) |
| `enum_audit.py.txt` / `enum_audit.out.txt` | the scratch extension of the tracked reference enumerator (imported unchanged): A1, A3, I1–I4b; `RESULT: PASS`, EXIT=0 |
| `axioms.txt` | `#print axioms` for the 22 exported theorems: classical trio or a subset; EXIT=0 |
| `budgets-reproduced.tsv` | route-β N=1…8, printing and silent, `time -v` wall and max RSS, all EXIT=0 |
| `e13-prefix-vs-candidate.txt` | six E13 membership rows enumerated with the pre-fix binary (`44c8ed60…`) and the candidate (`62adb8ec…`): byte-identical |
| `gate-reproductions.txt` | `check-unseq-scheduler` EXIT=0 (1:13 wall, 1.68 GB), warm build EXIT=0, setup-deps EXIT=0 |
| `ci-diff-drift.txt` | the audit's own `scripts/ci --diff` under the box-wide lock: summary block, drift block, EXIT (item l) |
