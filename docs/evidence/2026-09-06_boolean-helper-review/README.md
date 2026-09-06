# Independent Boolean storage/setup review

[AGENT], 2026-09-06; reviewer lane `typed-preflight`, independently of the
implementation lane. **PASS within the advertised bounded helper scope; no
blocking finding.** This is not acceptance of the complete O1 contract.

The reviewed source was the frozen, uncommitted helper increment over
integration revision `a392fab02b72f7edc4035fb103cf2285d7f5b9a1`.
`provenance.json` binds the exact helper, regression, facade, audit and claim
ledger bytes, relevant underlying semantics, and the implementer's gate logs.
All review writes and fresh probes were confined to this reviewer's worktree.

## What was assessed

The review followed `BooleanStore.lean` and `BooleanSetup.lean` through the
actual `Machine` helpers and `runProgramSetupM`, checked
`Tests/BooleanRuntime.lean`, and compared the facade and
`docs/2026-09-06_boolean-storage-setup.md` claims with their formal statements.
It also checked the expanded semantic interface/A1/A2 dependency audits and
the interface gate's private/trailing-declaration poison construction.

`BoolRoot` inspects an actual Boolean value at Boolean cell type, so a
declared Boolean cell holding nil cannot satisfy it. `EnvRoots` quantifies
every binding occurrence, including hidden outer and same-scope bindings;
successful visible lookup is derived from that stronger premise. The
regressions retain both hiding counterexamples and address-bounded but
ill-typed storage. Store lemmas preserve root typedness under aliases; they
do not preserve an aliased old value.

The Boolean binding/allocation lemmas derive actual helper success from
structural inputs. Their supporting shape lemmas separately assume success
and establish exact cell growth and equality of all nonheap fields. The
entry proof uses those facts to derive the real driver's successful setup,
empty driver barrier, external result pins, and unchanged complete choice
stream. Its arbitrary fuel premise is justified by the profile's exclusion
of globals and package initialization. No premise assumes a successful
future execution. Readout requires currently valid pinned roots, permits
aliasing, and establishes Boolean values and length, without a reachability
or termination premise.

The audits select imported `GoLean` and `Tests` declarations by module
origin, including private/generated/unused declarations, and recursively
restrict their axioms to the classical trio. Existing customer modules are
included in their respective gates. The checked interface gate supplies six
compiled negative controls, including unused private helper axioms and a
trailing runtime-test theorem using `sorry`. This materially strengthens the
previous restricted-module sweep. It remains an audit of the imported API
closure rather than a claim that every repository declaration is imported.

## Independent adversarial probes

`Adversarial.lean` was freshly elaborated against the frozen integration
build, using its read-only imports and no requested `.olean` output. Exact
command and working directory are in `provenance.json`; the command ran via
`scripts/capped`, `GOLEAN_MEM_MAX=16G`, and `LEAN_NUM_THREADS=3`.
`probes.log`/`probes.exit` retain the successful result. All six theorem
dependencies are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

- A3a admits the old unbound-variable body, and its actual setup succeeds
  with fuel zero and arbitrary choices. This challenges any inference from
  setup to body progress; the current ledger explicitly makes no such claim.
- A3a permits duplicate result names. The actual driver allocates two cells
  but returns the same final cell as both result pins. Typed roots and
  exact allocation count therefore do not entail distinct pins or ownership.
- False-valued aliased readout succeeds with both values false. A write of
  false through the shared cell changes both readout positions. Typed-root
  preservation therefore cannot be mistaken for value or separation facts.

`probes-initial.log`/`.exit` preserve an initial reviewer script error: the
parameterized `checkBoolean_iff` theorem needed explicit arguments before
`.mp`. That failed elaboration is not proof evidence; it was corrected and
the final file freshly elaborated successfully. No model change resulted.

## Verdict limits and remaining work

The current claim ledger explicitly distinguishes `NamesPresent` from an
exact name/location/value correspondence, and its existential storage
theorems from distinct roots and exposed initial zeros. The concrete native
setup test is a useful regression, not a generic initialization theorem.
Those stronger initialization facts are required next for useful functional
and ownership proofs. The announced scratch initialization follow-on was
outside this review.

O1 still requires the stronger admission-to-control invariant, preservation
for every relational successor, terminal-aware progress, and reachable
typed driver readout. No helper in this review supplies Iris resources.
O2, B7/I1, and final integrated source validation remain mandatory. These
limits match the current public documentation; they are not scope reductions
introduced by the reviewer.

The implementer reports passing ordinary CI, standalone interface, A1 and
A2 gates; their exact log hashes are preserved. The reviewer inspected that
evidence and did not rerun the full corpus. The ordinary CI's full executable
and negative records were explicitly cached from the fresh `10fefeb3`
preflight; this helper increment does not change runtime semantics.

Check `SHA256SUMS` from this directory before consuming this review.
