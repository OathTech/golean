# Independent review of the recovery storage foundation

[AGENT] coordinator, 2026-09-06. **Bounded PASS** for the six frozen helper
modules from `typed-recovery-runtime`, based on committed `212842a9`.
The author did not perform this review. The coordinator independently
authored entry/setup against the first three helpers; that separate setup
work is not reviewed or approved by this report.

The reviewer read every helper, the twelve supplied regressions, dedicated
audit and compiled-poison runner. Exact source bodies were concatenated
into `ReviewedStorage.lean` with their six internal imports removed and
their existing external imports retained. Fresh elaboration therefore does
not rely on the author's helper oleans. A separate importing file adds eleven
new kernel challenges and audits every declaration from that frozen module,
the imported GoLean/Tests modules and the review file: 6,780 declarations,
the classical trio only. Both final commands exited 0 and were warning-free.
The earlier review-probe elaboration failure (an unqualified byte-string
type) is retained separately and is not a passing check.

The challenges reject an address schema without its heap, a Boolean schema
covering a nil cell, address-sort remapping and dropping a live world slot.
They distinguish normalization from value typing, prohibit incompatible
static contexts sharing the same actual lookup, retain bare-initialization
placement constraints, and show that the runtime judgment's deliberate
freshness erasure is not stronger static admission. Actual binder and strict
operator equations independently check a capture's separate pointer slot,
its original pointee, arbitrary-byte boxing and current-cell dereference.

No vacuous future-success predicate or unchecked pointer-liveness assumption
was found. `HeapTyped` connects every world slot to an actual cell;
`ValueTyped.root` requires a Boolean pointee slot, and the heap supplies its
contents. `EnvTyped` checks all hidden bindings separately from first-match
lookup. Store preserves the same schema; allocation extends it. `Included`
preserves sorts, and declarations update both contexts. The compatible-union
lemma derives compatibility from the same real environment; it does not
preserve arbitrary old heterogeneous types across a new declaration.

The public meaning is limited: helper normalization is intentionally broader
than typing; strict payload comparison is broader than admitted source
nil-comparison; `ControlStmt` erases freshness only for runtime proof use.
None is advertised as proving whole-program admission, call/unwind safety,
termination, rendering or Iris ownership. The immutable-context premises
remain explicit until the separate B7 representation change.

The review inspected the author's completed focused gate and ordinary CI,
including eight fresh modules, 32 required exports, 6,789 audited constants,
and all eight independently compiled poison rejections. The audit selects
all imported local origins, including unused/private/trailing declarations;
compilation failure cannot satisfy a poison control. Ordinary CI's 3,607/394
runtime records are explicitly cached renderer evidence, not a fresh corpus
run. The reviewer did not repeat those expensive gates. `author-sources.sha256`
was verified against the author's still-frozen source at review closure;
`SHA256SUMS` seals this report, complete review sources and logs.

Acceptance covers this supporting increment. All-successor preservation,
actual setup/control composition, terminal-aware readout, both reusable Iris
customers, representation migration and final integration remain required.
