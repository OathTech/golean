# Backlog: Verdi theorem-parity via differential embedding (user idea, 2026-08-08)

To validate that GoLean proves the same theorem CLASS as Verdi (the Coq
framework whose raft proof is the classic prior art for our north star):
build an embedding of Verdi's system model (network semantics, message/
timeout events, node step functions) by the SAME means used for Go — an
executable deep embedding, differentially tested against Verdi's own
extracted/reference implementations, with the statement idiom held to
the deletion test. Then the parity question ("are we proving what Verdi
proved?") becomes comparable statements over two differentially-
validated embeddings rather than an informal reading of two formalisms.
Fits after/alongside the raft arc; large; needs its own scoping study
(Verdi's network semantics family — reordering/duplication/drop layers —
maps naturally onto a Choices-site envelope structure). Record in
TODO.md on the next work branch (main-direct commits forbidden).
