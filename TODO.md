# TODO

Tactical backlog for the SEMANTICS product. The pre-split TODO (which
interleaved reasoning-track items) is preserved on branch
`park/reasoning-2026-08-31`; reasoning items live there and migrate
with that product (the repo split, 2026-08-31 —
`docs/2026-08-31_repo-split-plan.md`).

## Owed from the split (tracked in the split plan)

- GoCore relational-module extraction slice (Machine/MachineSound/
  Multi-soundness/NPDRF/Race → the reasoning side; needs a design
  slice + full --diff revalidation). [USER]-ruled destination.
- `docs/architecture.md` and `docs/roadmap.md` semantics-scoped
  rewrites (currently carrying split banners).
- Migration stage (all [USER] decisions): new repo
  name/location/dependency mechanism/history strategy;
  `raft-proof-campaign` branch disposition.

## Standing semantics backlog

- The W3.2 concurrency re-envelope line (see `docs/w32-log.md` and
  the boundary set / POR design notes) — sequential frontier is
  SUPPORT-complete; concurrency rows are design-gated.
- Coverage ledgers: consume-on-demand growth per
  `docs/coverage-suite-structure.md`; BUGS.md triage per
  `docs/bugfix-arc-log.md`.
- Spec-truth follow-ups (covmap CIPs held for sign-off:
  `docs/covmap-cips/`).
