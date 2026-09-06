# Abort observation author evidence

The four semantic modules, test module and post-import audit freshly
elaborated from source on base `f160d7ca`. The dedicated gate exited 0:
43 required theorem exports, 14,529 declarations across all imported local
GoLean/Tests origins, classical trio only. Six compiled poisons were rejected:
an unused private axiom in each semantic module, an unused private axiom in
the audit module and a trailing test `sorry`.

The 21 kernel regressions cover byte/flag/order retention, nonstring-tail
rejection, transient unwinding, zero fuel, wrong event/thread/tombstone/text,
preexisting tombstones, actual abort transitions and differing main-exit
choices. Actual program wrapper probes exercise checked nullary admission,
same-fuel panic/fuel outcomes, an untyped integer entry that still runs, and
the fact that this broader entry does not gain profile admission.

Command: `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 bash scripts/check-abort-observation`.
`gate.log` records hashes and fresh elaborations; `source.sha256` pins all
ten semantic/test/audit/gate/build inputs. The complete source is retained
in the accompanying repository increment. `poison-logs/` contains compiled
negative-control logs. No source from the later R1 renderer or its temporary
olean was used: the gate's Machine source hash is recorded in
`dependencies.sha256`, matching the committed base.

Ordinary CI exited 0, including 202 evaluator tests and all affected gates.
The 3,607 executable and 394 negative records were reused from sealed
renderer integration evidence; `runtime-reuse.json` verifies their hashes
and classifies all source differences. This is cached differential evidence,
not a fresh corpus or a claim of rebuilt executable hash identity.

Independent bounded review PASS is sealed in parent commit `ad961e41`.
The reviewer freshly compiled all six exact modules plus ten additional
kernel probes, and audited 14,549 local-origin declarations. Challenges
covered actual byte output, broader integer/string execution, nonstring-tail
refusal, detector and missing-main refusals, positive fuel and real-driver
witnesses. All ten frozen source inputs matched. The implementation remains
limited to exact observer erasure/provenance; final R1 membership, complete
O2 safety and Iris adequacy review are separately required.
