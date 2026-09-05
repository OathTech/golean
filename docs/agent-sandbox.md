# Agent Sandbox Notes

This repo is usually edited from a managed Codex sandbox. Source edits belong
in the checked-out repository and should be made with `apply_patch`. Temporary
scratch files are different: create them with normal shell tooling under an
approved writable temporary root.

Sandbox permissions and approval requirements are separate. A path can be
writable while a command still needs approval because it is destructive, uses
the network, or otherwise crosses the approval policy. Do not bundle cleanup
commands with probes.

Prefer the session's permitted `$TMPDIR` for scratch directories. Use
`/private/tmp` only on a platform/session where that path is available and
granted:

```sh
mktemp -d "${TMPDIR%/}/golean-sandbox.XXXXXX"
# macOS, when /private/tmp is granted:
mktemp -d /private/tmp/golean-sandbox.XXXXXX
```

On macOS, `/tmp` is a symlink to `/private/tmp`; prefer `/private/tmp` in
commands so the path matches the sandbox writable root exactly. The Darwin
`$TMPDIR` path under `/private/var/folders/.../T` is also writable when it is
listed in the session permissions.

Do not use `apply_patch` to create or edit absolute temporary files outside the
repo. `apply_patch` is for tracked workspace edits and can trigger approval or
hang on paths outside the checkout. For throwaway probes, create a scratch
directory with `mktemp` and put generated files there with the relevant tool.

Do not run `rm`, `rm -r`, or `rm -rf` on scratch paths without explicit
approval. Those commands are destructive even when the target is under
`/private/tmp`. Prefer unique scratch directories and leave them for OS temp
cleanup, or ask for approval before deleting them.

For direct Go probes, use the current worktree's artifact cache, matching
`scripts/diff-coverage`, instead of the user-level cache. Run these commands
from the worktree root:

```sh
GOCACHE="$PWD/artifacts/go-build-cache" go run ./path/to/package
GO111MODULE=off GOCACHE="$PWD/artifacts/go-build-cache" go run ./path/to/package
```

The differential runner already does this for normal coverage runs by setting
`GOCACHE` internally. This note is only for ad hoc probes outside
`scripts/coverage`, `scripts/diff-coverage`, and `scripts/diff-one`.

### Linux/nono cache-path denial (2026-09-05)

The previous `/private/tmp/go-build` recommendation came from macOS.
In this Linux nono session, an optional direct Go probe failed with
`failed to initialize build cache at /private/tmp/go-build: mkdir /private:
permission denied`. `nono why --path /private/tmp/go-build --op write`
confirmed `path_not_granted`. The differential harness's worktree-local
`artifacts/go-build-cache` was permitted and its runs succeeded. The [USER]
authorized documenting this correction so other agents use that cache.

Use the worktree-local cache above and the session's permitted `$TMPDIR`.
Do not create `/private` or change filesystem permissions to repair this
policy denial. If another path is required, diagnose it with
`nono why --path <path> --op write`. Either pre-create the required directory
outside the sandbox and add a narrow `--allow <path>` grant to the next
`nono run`, or use a derived profile draft and have it reviewed/applied with
`nono profile promote` before restarting. Do not edit the active profile
from inside the sandbox. Approval inside Codex cannot enlarge nono's outer
OS sandbox.

If a command fails because the sandbox blocked network access, rerun that exact
needed command with an explicit escalation request and a narrow justification.
Do not preemptively request broad network or filesystem access.

## Kernel-evaluation experiments: contain OOM (2026-08-03)

Kernel/elaborator reduction of interpreter runs (`Terminates` discharge,
`decide +kernel`, `with_unfolding_all rfl`) can explode memory FAST — an
uncapped run ate through system RAM in seconds and the OOM killer took the
whole zellij → sandbox → agent stack down with it (sem-adequacy arc,
2026-08-03; user directive: OOMs must become LEAN failures, not
stack-killers). Standing convention for ANY reduction-heavy `lake env lean`
invocation:

- run it under `ulimit -v` in a subshell — 16 GiB (`ulimit -v 16777216`)
  is the default cap; below ~8 GiB Lean fails at startup ("failed to
  create thread"). (User ruling 2026-08-08: the convention stays as-is;
  where the thread-VA reservation makes the `-v` cap misfire even at
  16 GiB — observed intermittently on multi-decide pin modules at
  ~1 GiB actual RSS — an RSS-based fallback measurement
  (`/usr/bin/time -v`, judge against the 16 GiB intent) may be used and
  the substitution documented at the site; keep jobs short per the
  user's avoid-long-jobs preference.)
- add a `timeout`, and run it as a BACKGROUND task so a blowup kills the
  capped process, never the session;
- one experiment per invocation (a stuck reduction reports per-file, and
  isolation keeps the blast radius one example).
