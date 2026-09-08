# Declaration identity fixture pin

[AGENT] 2026-09-08. `scripts/check-declarations` freshly emits this artifact
with `TestDeclarationDecoderFixture` under the Go oracle pin, compares its
raw bytes with `SHA256SUMS`, then runs the actual Lean byte decoder and
all 576 ordered `go/types.Identical` comparisons over 24 declarations.
Its corrupt-byte control must fail the same pin check.

The initial hash was freshly reproduced on Go 1.26.5 and is also identical
to `7ac3eb46:docs/evidence/2026-09-06_i1-positive-declarations/fresh-go-fixture.json`.
The generated JSON stays in ignored scratch. A deliberate fixture change
requires a written reason, regenerated output and review of the changed
identity matrix; printing a new digest does not authorize a pin move.

This pins the separate declaration schema. It supplies no executable Go
support, source-typechecking theorem, or production package admission.
