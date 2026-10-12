# BUG-061 — the by-name exclusion (design note, 2026-10-12)

[AGENT] lane `fix/bug061-refuse-1012`, under [USER] Mike 2026-10-12, verbatim
(`docs/2026-10-12_release-readiness.md` §5): «D1: I think this should probably be
refused, if it's easy to exclude.» Record only; the living statement is the
BUG-061 entry in `docs/BUGS.md` and the header of
`tools/nativefrontend/staticinit.go`.

## 1. The mechanism

gc schedules only the packages with residual initialization WORK
(`pkginit.MakeTask`: no `..inittask` record for a package with no work and no
inittask-bearing import), and "residual" is what survives
`cmd/compile/internal/staticinit`. The frontend's rule (`sourceHasInitWork`)
calls every non-constant package-level initializer work. `StaticAssign` folds
strictly more than go/types' constants: array/slice/struct literals of static
elements, `&global`, same-package copies of static globals, func values,
`[]byte("lit")`, conversions to interface of static values, and — with the
inliner on — calls whose inlined body is one `return <static>` (`errors.New`).
So the frontend can keep a node gc deleted; a spurious node keeps a spurious
EDGE; an edge can delay an importer past a package it should have beaten. The
witness `multipkg/init-order-staticinit/seq`: `zq`'s only initializer is
`var A = [3]int{1, 2, 3}`; `la` blank-imports `zq`; `la < lb < zq` by schedule
key. gc prunes `zq`, `la` is ready at step one and wins the tie: 12. The
frontend holds `la` behind `zq`, `lb` goes first: 21. The under-approximation
bites exactly when (i) a package's only work is of a shape staticinit may fold,
(ii) some importer waits on it, and (iii) a competitor that sorts between the
importer and the uncertain package is ready meanwhile.

## 2. The exclusion

Two parts, both in `staticinit.go`, the emitted schedule unchanged:

1. **Classify** each non-constant initializer of a source package: WORK where
   `StaticAssign` has no case and inlining cannot rescue (map literals,
   arithmetic, indexing, field reads, method values, receives, non-NOP
   conversions, builtins, calls through interfaces or func values, calls whose
   body — as gc's writer and reader shape it — is not a single return,
   foreign-package and string-typed copies), else MAYBE-STATIC. Each WORK arm
   cites its gc reading (the header of `staticinit.go` lists them: `StaticAssign`,
   `staticAssignInlinedCall`, `tryStaticInit`; the writer's `terminates`
   dead-code omission and its silent const/type declarations; the reader's
   block, loop and static-`if` shaping; `stringtoruneslit`; the OCONVIFACE
   unwrap of nested interface conversions). The classifier errs toward
   MAYBE-STATIC (an error there adds a refusal, never a silent order). A
   package is UNCERTAIN iff it has no init body, no WORK initializer and at
   least one MAYBE-STATIC one.

   **The standard is gc's own verdict, recorded** (the fix round of 2026-10-12,
   after the pre-merge review found four WORK arms gc folds — BLOCKER-1: the
   writer's dead-code and declaration rules, so `if true { return 1 }; return 2`
   and `const c = 7; return c` fold; BLOCKER-2: `[]rune("lit")` and
   `any(I(T{}))` fold — and HIGH: the unit table was the classifier's own
   expectations). `tools/nativefrontend/testdata/staticinit-shapes.go` is the
   shape table (79 shapes); `scripts/test-staticinit-oracle`
   (`tools/staticinitoracle`) builds each shape with the pinned toolchain as
   bases + one spec in GOPATH mode and reads the package's `..inittask` record
   with `go tool nm -size` (none, or the 8-byte header alone = folded; longer =
   work); `testdata/staticinit-oracle.tsv` is the record; `staticinit_test.go`
   asserts no `none` shape is WORK (soundness) and every `work` shape is WORK
   unless listed conservative with its reason (precision) — at the fix round's
   tip, 79/79 with an empty conservative list. The self-test is run by hand
   when the shapes or the oracle change (the charter: not a gate). Shapes the
   fix round moved WORK → MAYBE-STATIC: `CallC`, `CallCE`, `CallCN`, `CallCA`,
   `CallDA`, `CallTR`, `CallNI`, `CallCD`, `CallTD`, `CallCTD` (body rules),
   `Runes`, `RunesN`, `RunesS` (`stringtoruneslit`), `ConvAnyNested` (nested
   OCONVIFACE), `UP = uintptr(unsafe.Pointer(&C))` (both OCONVNOP — the
   review's NIT, fixed rather than recorded as a gap; unreachable today while
   FR-22 refuses user `unsafe.Pointer` initializers); moved MAYBE-STATIC → WORK
   for precision, gc-measured: `_ = Arr[0]` (an index is not effect-free for
   the blank discard) and `I(T{}).M()` (devirtualized through a type assertion
   the inlined-call fold refuses to move).

   **Second fix round** (the re-audit of `d70a67b0`; three more WORK-where-gc-
   folds classes). (i) The static-`if` rule counted the reader's `_ = cond`
   statement from the ORIGINAL condition, but `writer.staticBool` rewrites the
   written condition in place (`false && g()` is written as `false`, a literal
   the reader does not keep): `if false && g() { return 1 }; return 2` folds.
   Option taken, [AGENT] per the coordinator's standing instruction («prefer the
   COARSER rule that errs toward MAYBE-STATIC … unless the exact mirror is a
   few lines AND the oracle pins both directions»): the COARSE rule — the
   `_ = cond` statement is never counted. Dropping a statement can only make a
   body look more like a single return, so the loss is precision alone, on
   shapes where gc keeps the rewritten non-literal condition (`g() && false`,
   `g() || true`): pinned both ways (`CallFG`, `CallTG`, `CallTFG` fold;
   `CallGF`, `CallGT` are work and listed conservative; `CallFOG` is work and
   classifies WORK because the condition stays undecided). The exact mirror
   was a few lines too; coarse was chosen because the exact rule's benefit is
   confined to those two contrived shapes. (ii) `isSideEffect` has NO effect
   for `make` of a chan or map with no size or a constant zero (`var _ =
   make(chan int)` is discarded): mirrored. (iii) The effect walk descended
   into TYPE positions (`(*T)(p)`, `[]*T{…}`), claiming dereferences gc has no
   node for: type positions are skipped. The table grew to 101 shapes; the
   conservative entries (gc work, classified MAYBE-STATIC, each with its
   reason in `staticinit_test.go`): `CallGF`, `CallGT` (the coarse rule),
   `CallBN` (bare named return), `CallNoI` (`//go:noinline` not read),
   `CopyInl` (staticcopy has no OINLCALL case), `CallClo` (a closure capturing
   a parameter), `SlAny` (an interface element implicitly converted), `_4`
   (a blank method value). The oracle reads the compile ARCHIVE, where a
   deps-only record survives (the linker drops it from a binary).
2. **Enumerate** every pruning of the uncertain packages (cap 12 → 4096 walks;
   beyond it refuse by name), recompute the node set and the two-pass walk,
   and REFUSE iff some pruning orders the packages WITH work differently from
   the emitted walk. The message names BUG-061, the package(s), the
   initializer(s) with positions, and both orders. Lowerdiag cause
   `staticinit-uncertain-order` (a (c)-pin, ledger §5.1 C2).

Why not the blunt rule «refuse any uncertain package»? It is not "without
refusing programs the model gets right": a MAYBE-STATIC package nobody but
main imports, or one that is a node anyway through a node import, cannot move
another package. Why enumerate rather than compare the two extremes? With two
uncertain packages the extremes can agree while a middle assignment differs
(`X < Y < W1 < W3`, X→W1, Y→W3: neither and both give X,Y; W1 alone gives
Y,X). The enumeration is exact for the classification it is given.

## 3. Measured corpus impact

Frontend run over the 28 multi-package corpus roots (`multipkg/*` ×25,
`generics/qualified-instantiation`, `fmt/formatter-box-crosspkg`,
`channels/select-multi-ready`), `init/hidden-dep-order` (with its allow) and the
raft twin assembly (`scripts/check-frontend-pins`' `twin-prog`), before and
after:

| rule | refuses | baseline rows moved |
|---|---|---|
| this exclusion (classify + enumerate) | `multipkg/init-order-staticinit` only | 1: the witness, FAIL/differential → FAIL/frontend-export; twin wire byte-identical |
| blunt «any uncertain package» (measured with a throwaway patched copy) | `multipkg/errors-new` (`liberr`), `multipkg/wire-codec` (`wirepb`), the witness, the raft twin (`quorum`, `raft`, `tracker`) | 33 PASSing rows (3 + 29 + 1) plus the twin pin — rejected |

No PASS → non-PASS flip; 3939 = 3706 PASS / 233 FAIL unchanged (the branch's
figure after the runtime lane's three born rows). Re-measured identically at
the fix round's tip (the same 28 roots + the twin: the witness alone refuses,
the twin wire byte-identical). Unit tests (`staticinit_test.go`): the witness
refuses with the named text; init-body, map-literal, multi-statement-call,
arithmetic, constant and empty controls lower; an uncertain package imported
only by main or a node through its imports lowers; the 101-shape table against
the recorded gc verdicts (§2; 8 conservative, 0 soundness misses); the node
fact unchanged.

## 4. Still owed

The staticinit model itself — L-011's decision at a point where gc is not
single-valued (`callinit` flips between `go run` and `-gcflags=all='-N -l'`).
Until then the row stays red by name and the guard is the release's answer to
item 1 for BUG-061. The latitude-inventory entry L-011 (c) owes is untouched
here.
