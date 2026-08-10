(* Rocq oracle leg of the differential harness (lane log
   `docs/2026-08-09_verdi-p1-lane.md`, P1b second half; design note §3
   path 2). Instantiates verdi-raft's Raft handlers with the SAME N=3
   counter machine as the Lean side's `VerdiCompat.Examples.counterBase`
   (`compat/verdi/VerdiCompat/Examples.lean:20-35`):

     data = input = output = nat,  init = 0,
     handler i d = (d + i, d + i),  N = 3,  clientId = nat.

   Node names: Coq `fin 3` values correspond to Lean `Fin 3` via
   `fin_to_nat` (StructTact `Fin.v:69-77`; `all_fin 3` enumerates
   0,1,2 in the same order as the Lean port's `allFin`), and
   `ExtrOcamlFinInt` extracts `fin` to `int`, so the OCaml driver sees
   names as the same decimals the fixture grammar uses.

   Extraction directives follow the house pattern
   (`deps/verdi-raft/extraction/vard/coq/ExtractVarDRaft.v`): nat -> int,
   fin -> int, Coq list/bool/option -> OCaml's. `seq` is extracted
   because `ExtrOcamlFinInt` realizes `all_fin` as `seq 0 n`.

   Instances are applied with explicit `@` (never typeclass search):
   Raft.v declares its own generic `base_params`/`multi_params`
   instances, and resolution against those could pick the wrong
   BaseParams silently. Explicit application fails loud instead. *)

From VerdiRaft Require Import Raft.
From Coq Require Import Arith.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt.
From Verdi Require Import ExtrOcamlBasicExt ExtrOcamlNatIntExt.
From Verdi Require Import ExtrOcamlBool ExtrOcamlList ExtrOcamlFinInt.

(* Explicit Build_* constructors, not `{| ... |}` record notation: the
   notation's field elaboration opens BaseParams typeclass goals, and
   Raft.v's generic `base_params` instance sends that search into a
   loop (observed: coqc stack overflow). Constructors keep it loud and
   first-order. *)

Definition counter_base : BaseParams :=
  Build_BaseParams nat nat nat.

Definition counter_one : OneNodeParams counter_base :=
  Build_OneNodeParams counter_base 0 (fun i d => (d + i, d + i)).

Definition counter_raft : RaftParams counter_base :=
  @Build_RaftParams counter_base 3 Nat.eq_dec Nat.eq_dec nat Nat.eq_dec.

(* Monomorphic wrappers, one per fixture kind. (counter_init_handlers
   was extracted-but-dead at first — audit finding 2026-08-10; the
   `init` fixture kind now replays it, so the initial-state record is
   compared end-to-end.) Implicit-argument order checked against
   `Check @...`: the four message handlers and reboot take
   (base, raft); the two composed handlers and init_handlers take
   (base, one, raft). *)

Definition counter_handleAppendEntries :=
  @handleAppendEntries counter_base counter_raft.        (* kind hAE  *)
Definition counter_handleAppendEntriesReply :=
  @handleAppendEntriesReply counter_base counter_raft.   (* kind hAER *)
Definition counter_handleRequestVote :=
  @handleRequestVote counter_base counter_raft.          (* kind hRV  *)
Definition counter_handleRequestVoteReply :=
  @handleRequestVoteReply counter_base counter_raft.     (* kind hRVR *)
Definition counter_RaftNetHandler :=
  @RaftNetHandler counter_base counter_one counter_raft.     (* kind net *)
Definition counter_RaftInputHandler :=
  @RaftInputHandler counter_base counter_one counter_raft.   (* kind inp *)
Definition counter_reboot :=
  @reboot counter_base counter_raft.                     (* kind reboot *)
Definition counter_init_handlers :=
  @init_handlers counter_base counter_one counter_raft.  (* kind init *)

Extraction "RaftHandlers.ml"
  seq
  counter_handleAppendEntries
  counter_handleAppendEntriesReply
  counter_handleRequestVote
  counter_handleRequestVoteReply
  counter_RaftNetHandler
  counter_RaftInputHandler
  counter_reboot
  counter_init_handlers.
