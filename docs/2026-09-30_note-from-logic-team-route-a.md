<!-- VERBATIM COPY for GoLean's records. Source: golean-logic (~/projects/golean-logic, read-only), branch docs/golean-route-a-0930, commit 7866af1dce15d896895e9324b7a054acaa69752e, file docs/2026-09-30_note-to-golean-route-a.md, sha256 367de8e3e39160873b0fce39580907e97eb71d4737314f8d12080e593ef3101d (80 lines). Relayed by the [USER] 2026-09-30; copied unchanged by the [AGENT] design writer, lane docs/bug004-item4-design-0930. It answers docs/2026-09-30_protobuf-route-a.md §7. The [USER]'s dispositions on it: docs/2026-08-31_qrow-rulings.md, «The logic team's route-A reply (2026-09-30) — dispositions»; the BUG-004 item 4 design it asks for (§4): docs/2026-09-30_bug004-item4-design.md. -->

# golean-logic note to GoLean: protobuf route A is workable for us

2026-09-30. To the GoLean team, answering the question in
`docs/2026-09-30_protobuf-route-a.md` §7 (branch `records/raft-deltas-0930`
@ `61b15acd`). **[USER]** Asked for this reply. **[AGENT]** Technical
input to the user's choice between routes A and B. It authorizes nothing,
and our estimates are ±50%.

## 1. Short answer

Yes. Proving raft's ConfChange paths against a lowered Go `Unmarshal` is
workable, and we now prefer route A. There is one caveat, about your C3
(§4).

## 2. How we would prove it

- **Contracts, not symbolic execution.** Each codec function gets a
  contract, discharged once against its lowered body. That is how our logic
  treats every callee. Symbolic execution of the body does not help:
  `Unmarshal`'s input bytes are arbitrary, so its loop needs an invariant
  either way.
- **A natural contract target.** The lowered codec refines raft-proofs'
  functional decoder (`packages/etcd-model/EtcdModel/Mirror/ConfChangeDecode.lean`),
  through our planned refinement combinator. Being raft-specific, these
  proofs belong downstream in the bridge. golean-logic supplies the generic
  rules.

## 3. Why our "route B is likely cheaper" no longer holds

That view assumed native definitions would spare us GoCore-level loop
invariants, byte-slice ownership, shifts and width conversions. Our
`cluster3` census (golean-logic `docs/2026-09-30_cluster3-census.md`) has
since shown that raft itself needs all of them. Raft needs:

- loops;
- slices;
- integer kinds and shifts;
- recursion;
- error interfaces;
- package-level globals with an initializer.

Route A therefore adds only codec-specific invariants: varint decoding,
field dispatch, unknown-field retention and group skipping. Our estimate
is 3–6 sessions on top of stages we must build anyway. Route A also keeps
GoCore uniform, with no intrinsic step rules and no extra re-pin surface.
That is better for executability and for us.

## 4. The caveat: C3, the abort line of `panic(err)`

Your §3 and C3 record that the machine refuses to render the abort line
for an error-typed payload (BUG-004 item 4). In our logic, a refusal is a
fault on every choice tape. So a program that can reach `panic(err)` gets
no outcome theorem, unless the panic is proved unreachable.

For the end-to-end theorem this may be acceptable. If raft-proofs'
precondition excludes malformed conf-change data, and the codec contract
proves that valid bytes decode with a nil error, then the panic is
unreachable and nothing is refused. Covering malformed proposals as panic
outcomes would need two things:

- BUG-004 item 4 to land;
- on our side, error-payload panics. Stage 1 covers string payloads only.
  Our census estimate for this is 1–3 sessions.

We would ask for BUG-004 item 4's plan and, when it lands, rendering
equations for error payloads, like the existing `StringPanic` lemmas.

## 5. What we would need from you

| Offer in your §7 | Needed? |
| --- | --- |
| Pinned equation set for the codec's functions | No. We prove from the lowered bodies with our general rules. The general per-arm `stepFn` equations (packet D), already requested, are what matter. |
| Named `FuncId` list | Yes. We would also like deterministic, hash-pinned generator output, so that regeneration does not churn proofs. |
| Purity statement | Not as a trusted input, since we prove footprints ourselves. A documented footprint would help planning. It would help more if the generated code kept to forms we will support: plain indexed loops, `break`/`continue` only, recursion bounded by a depth counter, and no reflection. |
| Init-time pick as a labelled choice | Yes. The `mapIter` idiom is fine, but please fix its exact shape, so one lemma covers it. It should appear as an ordinary choice consumed before `main`. Our closed theorems currently assume no globals and no package initializer, so this depends on our globals/initialization stage. |

Your C4 residue (a subject-local error type) is invisible to our proofs,
and we record nothing for it. Your C2 membership view of the prefix spelling
matches how we would state it: an outcome theorem quantified over both
spellings.
