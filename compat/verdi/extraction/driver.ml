(* Rocq-oracle driver for the differential harness (lane log
   `docs/2026-08-09_verdi-p1-lane.md`).

   Reads `fixtures/handlers-n3.tsv` (grammar: the docstring of
   `compat/verdi/DiffHarness.lean` — transcribed here, not invented),
   replays every recorded input through the EXTRACTED verdi-raft
   handlers (`RaftHandlers.ml`, from `ExtractRaftHandlers.v`), and
   compares the serialized result byte-for-byte against the fixture's
   output column (the Lean port's answer).

   FAIL CLOSED: any row whose input does not parse (including a
   grammar-valid decimal exceeding OCaml's int range — audit fix
   2026-08-10: previously an uncaught Failure abort), whose kind is
   unknown, whose parsed input does not round-trip to the exact input
   column (parser/serializer drift is an infra failure, never a pass),
   or whose result the grammar cannot serialize (e.g. a negative int)
   is a visible per-row INFRA failure; any INFRA or DIVERGE row, or an
   empty case set, exits nonzero. A run that checked nothing must not
   pass. COMPLETENESS (audit fix 2026-08-10: a truncated fixture used
   to pass green): the fixture header's `cases-per-kind=N kinds=...`
   declaration is parsed and enforced — exactly N judged rows per
   declared kind, no undeclared kinds; a fixture without the
   declaration is refused.

   Verdicts: MATCH / DIVERGE (oracle disagrees with the Lean output —
   a finding, port bug or instantiation mismatch) / INFRA. *)

open RaftHandlers

exception Infra of string

let infra fmt = Printf.ksprintf (fun s -> raise (Infra s)) fmt

(* ---------- s-expressions ---------- *)

type sexp = Atom of string | L of sexp list

let tokenize (s : string) : string list =
  let n = String.length s in
  let toks = ref [] in
  let buf = Buffer.create 16 in
  let flush () =
    if Buffer.length buf > 0 then begin
      toks := Buffer.contents buf :: !toks; Buffer.clear buf
    end in
  for i = 0 to n - 1 do
    match s.[i] with
    | '(' -> flush (); toks := "(" :: !toks
    | ')' -> flush (); toks := ")" :: !toks
    | ' ' -> flush ()
    | c -> Buffer.add_char buf c
  done;
  flush ();
  List.rev !toks

let parse_sexp (s : string) : sexp =
  let rec parse_one = function
    | [] -> infra "unexpected end of input in s-expr"
    | "(" :: rest ->
      let elts, rest = parse_list rest in
      (L elts, rest)
    | ")" :: _ -> infra "unexpected ')'"
    | a :: rest -> (Atom a, rest)
  and parse_list = function
    | ")" :: rest -> ([], rest)
    | [] -> infra "unclosed '(' in s-expr"
    | toks ->
      let x, rest = parse_one toks in
      let xs, rest = parse_list rest in
      (x :: xs, rest)
  in
  match parse_one (tokenize s) with
  | x, [] -> x
  | _, t :: _ -> infra "trailing tokens in s-expr starting at '%s'" t

(* ---------- parsing grammar values ---------- *)

let p_nat = function
  | Atom a ->
    if a = "" then infra "empty atom where nat expected";
    String.iter (fun c -> if c < '0' || c > '9' then
                   infra "non-decimal atom '%s' where nat expected" a) a;
    (* grammar-valid but oversized decimals must be a per-row INFRA,
       not an uncaught Failure abort *)
    (try int_of_string a
     with Failure _ -> infra "decimal '%s' exceeds the driver's int range" a)
  | L _ -> infra "list where nat expected"

(* names are Fin 3 decimals; the extracted fin is int (ExtrOcamlFinInt) *)
let p_name x =
  let n = p_nat x in
  if n > 2 then infra "name %d out of range for N=3" n;
  n

let p_bool = function
  | Atom "true" -> true
  | Atom "false" -> false
  | Atom a -> infra "bad bool atom '%s'" a
  | L _ -> infra "list where bool expected"

let p_opt f = function
  | L [Atom "none"] -> None
  | L [Atom "some"; x] -> Some (f x)
  | _ -> infra "bad option s-expr"

let p_list f = function
  | L xs -> List.map f xs
  | Atom a -> infra "atom '%s' where list expected" a

let p_pair f g = function
  | L [x; y] -> (f x, g y)
  | _ -> infra "bad pair s-expr"

let p_entry = function
  | L [Atom "entry"; a; c; id; idx; t; inp] ->
    { eAt = p_name a; eClient = Obj.magic (p_nat c); eId = p_nat id;
      eIndex = p_nat idx; eTerm = p_nat t; eInput = Obj.magic (p_nat inp) }
  | _ -> infra "bad entry s-expr"

let p_msg = function
  | L [Atom "RequestVote"; t; c; lli; llt] ->
    RequestVote (p_nat t, p_name c, p_nat lli, p_nat llt)
  | L [Atom "RequestVoteReply"; t; g] ->
    RequestVoteReply (p_nat t, p_bool g)
  | L [Atom "AppendEntries"; t; lid; pli; plt; es; lc] ->
    AppendEntries (p_nat t, p_name lid, p_nat pli, p_nat plt,
                   p_list p_entry es, p_nat lc)
  | L [Atom "AppendEntriesReply"; t; es; r] ->
    AppendEntriesReply (p_nat t, p_list p_entry es, p_bool r)
  | _ -> infra "bad msg s-expr"

let p_input = function
  | L [Atom "Timeout"] -> Timeout
  | L [Atom "ClientRequest"; c; id; i] ->
    ClientRequest (Obj.magic (p_nat c), p_nat id, Obj.magic (p_nat i))
  | _ -> infra "bad raft_input s-expr"

let p_server_type = function
  | Atom "Follower" -> Follower
  | Atom "Candidate" -> Candidate
  | Atom "Leader" -> Leader
  | _ -> infra "bad serverType s-expr"

let p_cache_entry = function
  | L [c; id; o] -> (Obj.magic (p_nat c), (p_nat id, Obj.magic (p_nat o)))
  | _ -> infra "bad clientCache entry s-expr"

(* victory (t (names) (entries)) ; extracted type is left-nested
   ((term * name list) * entry list) *)
let p_victory = function
  | L [t; ns; es] -> ((p_nat t, p_list p_name ns), p_list p_entry es)
  | _ -> infra "bad electoralVictories entry s-expr"

let p_state = function
  | L (Atom "state" :: [ct; vf; lid; log; ci; la; sm; ni; mi; ss; vr; ty; cc; ev]) ->
    { currentTerm = p_nat ct; votedFor = p_opt p_name vf;
      leaderId = p_opt p_name lid; log = p_list p_entry log;
      commitIndex = p_nat ci; lastApplied = p_nat la;
      stateMachine = Obj.magic (p_nat sm);
      nextIndex = p_list (p_pair p_name p_nat) ni;
      matchIndex = p_list (p_pair p_name p_nat) mi;
      shouldSend = p_bool ss; votesReceived = p_list p_name vr;
      type0 = p_server_type ty; clientCache = p_list p_cache_entry cc;
      electoralVictories = p_list p_victory ev }
  | _ -> infra "bad state s-expr (want (state ...) with 14 fields)"

(* ---------- serialization (must mirror DiffHarness.lean exactly) ---------- *)

let ser_nat (n : int) : string =
  if n < 0 then infra "negative int %d — not serializable as Nat" n;
  string_of_int n

let ser_name (n : int) : string =
  if n < 0 || n > 2 then infra "name %d out of range on output" n;
  string_of_int n

let ser_bool b = if b then "true" else "false"

let ser_list f l = "(" ^ String.concat " " (List.map f l) ^ ")"

let ser_opt f = function
  | None -> "(none)"
  | Some x -> "(some " ^ f x ^ ")"

let ser_entry (e : entry) : string =
  Printf.sprintf "(entry %s %s %s %s %s %s)"
    (ser_name e.eAt) (ser_nat (Obj.magic e.eClient)) (ser_nat e.eId)
    (ser_nat e.eIndex) (ser_nat e.eTerm) (ser_nat (Obj.magic e.eInput))

let ser_msg = function
  | RequestVote (t, c, lli, llt) ->
    Printf.sprintf "(RequestVote %s %s %s %s)"
      (ser_nat t) (ser_name c) (ser_nat lli) (ser_nat llt)
  | RequestVoteReply (t, g) ->
    Printf.sprintf "(RequestVoteReply %s %s)" (ser_nat t) (ser_bool g)
  | AppendEntries (t, lid, pli, plt, es, lc) ->
    Printf.sprintf "(AppendEntries %s %s %s %s %s %s)"
      (ser_nat t) (ser_name lid) (ser_nat pli) (ser_nat plt)
      (ser_list ser_entry es) (ser_nat lc)
  | AppendEntriesReply (t, es, r) ->
    Printf.sprintf "(AppendEntriesReply %s %s %s)"
      (ser_nat t) (ser_list ser_entry es) (ser_bool r)

let ser_input = function
  | Timeout -> "(Timeout)"
  | ClientRequest (c, id, i) ->
    Printf.sprintf "(ClientRequest %s %s %s)"
      (ser_nat (Obj.magic c)) (ser_nat id) (ser_nat (Obj.magic i))

let ser_output = function
  | NotLeader (c, id) ->
    Printf.sprintf "(NotLeader %s %s)" (ser_nat (Obj.magic c)) (ser_nat id)
  | ClientResponse (c, id, o) ->
    Printf.sprintf "(ClientResponse %s %s %s)"
      (ser_nat (Obj.magic c)) (ser_nat id) (ser_nat (Obj.magic o))

let ser_server_type = function
  | Follower -> "Follower"
  | Candidate -> "Candidate"
  | Leader -> "Leader"

let ser_nat_pair (n, v) =
  Printf.sprintf "(%s %s)" (ser_name n) (ser_nat v)

let ser_cache_entry (c, (id, o)) =
  Printf.sprintf "(%s %s %s)"
    (ser_nat (Obj.magic c)) (ser_nat id) (ser_nat (Obj.magic o))

let ser_victory ((t, ns), es) =
  Printf.sprintf "(%s %s %s)"
    (ser_nat t) (ser_list ser_name ns) (ser_list ser_entry es)

let ser_state (st : raft_data0) : string =
  Printf.sprintf "(state %s %s %s %s %s %s %s %s %s %s %s %s %s %s)"
    (ser_nat st.currentTerm)
    (ser_opt ser_name st.votedFor)
    (ser_opt ser_name st.leaderId)
    (ser_list ser_entry st.log)
    (ser_nat st.commitIndex)
    (ser_nat st.lastApplied)
    (ser_nat (Obj.magic st.stateMachine))
    (ser_list ser_nat_pair st.nextIndex)
    (ser_list ser_nat_pair st.matchIndex)
    (ser_bool st.shouldSend)
    (ser_list ser_name st.votesReceived)
    (ser_server_type st.type0)
    (ser_list ser_cache_entry st.clientCache)
    (ser_list ser_victory st.electoralVictories)

let ser_packet (dst, m) =
  Printf.sprintf "(%s %s)" (ser_name dst) (ser_msg m)

(* Coq `list raft_output * raft_data * list (name * msg)` extracts
   left-nested: ((outs, st), pkts). *)
let ser_handler_result ((outs, st), pkts) =
  Printf.sprintf "(%s %s %s)"
    (ser_list ser_output outs) (ser_state st) (ser_list ser_packet pkts)

(* ---------- per-kind dispatch ---------- *)

(* Returns (input-roundtrip, oracle-output). Input shapes and output
   shapes per kind: DiffHarness.lean docstring. *)
let run_case (kind : string) (inp : sexp) : string * string =
  match kind, inp with
  | "hAE", L [me; st; t; lid; pli; plt; es; lc] ->
    let me = p_name me and st = p_state st and t = p_nat t
    and lid = p_name lid and pli = p_nat pli and plt = p_nat plt
    and es = p_list p_entry es and lc = p_nat lc in
    let rt = Printf.sprintf "(%s %s %s %s %s %s %s %s)"
        (ser_name me) (ser_state st) (ser_nat t) (ser_name lid)
        (ser_nat pli) (ser_nat plt) (ser_list ser_entry es) (ser_nat lc) in
    let st', m = counter_handleAppendEntries me st t lid pli plt es lc in
    (rt, Printf.sprintf "(%s %s)" (ser_state st') (ser_msg m))
  | "hAER", L [me; st; src; t; es; res] ->
    let me = p_name me and st = p_state st and src = p_name src
    and t = p_nat t and es = p_list p_entry es and res = p_bool res in
    let rt = Printf.sprintf "(%s %s %s %s %s %s)"
        (ser_name me) (ser_state st) (ser_name src) (ser_nat t)
        (ser_list ser_entry es) (ser_bool res) in
    let st', pkts = counter_handleAppendEntriesReply me st src t es res in
    (rt, Printf.sprintf "(%s %s)" (ser_state st') (ser_list ser_packet pkts))
  | "hRV", L [me; st; t; cand; lli; llt] ->
    let me = p_name me and st = p_state st and t = p_nat t
    and cand = p_name cand and lli = p_nat lli and llt = p_nat llt in
    let rt = Printf.sprintf "(%s %s %s %s %s %s)"
        (ser_name me) (ser_state st) (ser_nat t) (ser_name cand)
        (ser_nat lli) (ser_nat llt) in
    let st', m = counter_handleRequestVote me st t cand lli llt in
    (rt, Printf.sprintf "(%s %s)" (ser_state st') (ser_msg m))
  | "hRVR", L [me; st; src; t; g] ->
    let me = p_name me and st = p_state st and src = p_name src
    and t = p_nat t and g = p_bool g in
    let rt = Printf.sprintf "(%s %s %s %s %s)"
        (ser_name me) (ser_state st) (ser_name src) (ser_nat t) (ser_bool g) in
    let st' = counter_handleRequestVoteReply me st src t g in
    (rt, Printf.sprintf "(%s)" (ser_state st'))
  | "net", L [me; src; m; st] ->
    let me = p_name me and src = p_name src and m = p_msg m
    and st = p_state st in
    let rt = Printf.sprintf "(%s %s %s %s)"
        (ser_name me) (ser_name src) (ser_msg m) (ser_state st) in
    let r = counter_RaftNetHandler me src m st in
    (rt, ser_handler_result r)
  | "inp", L [me; i; st] ->
    let me = p_name me and i = p_input i and st = p_state st in
    let rt = Printf.sprintf "(%s %s %s)"
        (ser_name me) (ser_input i) (ser_state st) in
    let r = counter_RaftInputHandler me i st in
    (rt, ser_handler_result r)
  | "reboot", L [st] ->
    let st = p_state st in
    let rt = Printf.sprintf "(%s)" (ser_state st) in
    let st' = counter_reboot st in
    (rt, Printf.sprintf "(%s)" (ser_state st'))
  | "init", L [me] ->
    let me = p_name me in
    let rt = Printf.sprintf "(%s)" (ser_name me) in
    let st = counter_init_handlers me in
    (rt, Printf.sprintf "(%s)" (ser_state st))
  | ("hAE" | "hAER" | "hRV" | "hRVR" | "net" | "inp" | "reboot" | "init"), _ ->
    infra "input arity/shape does not match kind '%s'" kind
  | k, _ -> infra "unknown kind '%s' — refusing to judge" k

(* ---------- main ---------- *)

let split_tabs (s : string) : string list = String.split_on_char '\t' s

(* Parse the header's completeness declaration, e.g.
   `# machine=... cases-per-kind=40 kinds=hAE hAER ... reboot`
   -> Some (40, ["hAE"; ...]). The declaration is REQUIRED (see the
   contract above): without it a truncated fixture is undetectable. *)
let parse_decl (line : string) : (int * string list) option =
  let toks = String.split_on_char ' ' line in
  let pref p t =
    let lp = String.length p in
    if String.length t >= lp && String.sub t 0 lp = p
    then Some (String.sub t lp (String.length t - lp)) else None in
  let cpk = List.find_map (pref "cases-per-kind=") toks in
  let rec after_kinds = function
    | [] -> None
    | t :: rest ->
      (match pref "kinds=" t with
       | Some k -> Some (k :: rest)
       | None -> after_kinds rest) in
  match cpk, after_kinds toks with
  | Some n, Some kinds ->
    (try Some (int_of_string n, kinds) with Failure _ -> None)
  | _ -> None

let () =
  if Array.length Sys.argv <> 2 then begin
    prerr_endline "usage: driver <fixture.tsv>   (fail closed: exactly one argument)";
    exit 2
  end;
  let path = Sys.argv.(1) in
  let ic = try open_in path with Sys_error e -> prerr_endline e; exit 2 in
  let n_match = ref 0 and n_diverge = ref 0 and n_infra = ref 0 in
  let decl : (int * string list) option ref = ref None in
  let seen : (string, int) Hashtbl.t = Hashtbl.create 8 in
  let count_kind k =
    Hashtbl.replace seen k (1 + (try Hashtbl.find seen k with Not_found -> 0)) in
  (try
     while true do
       let line = input_line ic in
       if line = "" || line.[0] = '#' then begin
         if !decl = None then decl := parse_decl line
       end
       else begin
         let verdict =
           match split_tabs line with
           | [id; kind; inp; expected] ->
             count_kind kind;
             (try
                let rt, got = run_case kind (parse_sexp inp) in
                if rt <> inp then begin
                  incr n_infra;
                  Printf.printf "%s\t%s\tINFRA\tinput did not round-trip through the driver's grammar\n" id kind;
                  Printf.printf "  fixture input: %s\n  round-tripped: %s\n" inp rt;
                  `Bad
                end else if got = expected then begin
                  incr n_match;
                  Printf.printf "%s\t%s\tMATCH\n" id kind;
                  `Ok
                end else begin
                  incr n_diverge;
                  Printf.printf "%s\t%s\tDIVERGE\n" id kind;
                  Printf.printf "  lean: %s\n  rocq: %s\n" expected got;
                  `Bad
                end
              with Infra msg ->
                incr n_infra;
                Printf.printf "%s\t%s\tINFRA\t%s\n" id kind msg;
                `Bad)
           | _ ->
             incr n_infra;
             Printf.printf "?\t?\tINFRA\trow does not have exactly 4 tab-separated columns: %s\n" line;
             `Bad
         in
         ignore verdict
       end
     done
   with End_of_file -> ());
  close_in ic;
  let total = !n_match + !n_diverge + !n_infra in
  Printf.printf "oracle: %d cases: %d match, %d diverge, %d infra\n"
    total !n_match !n_diverge !n_infra;
  if total = 0 then begin
    prerr_endline "oracle: FAIL: zero cases judged — a run that checked nothing must not pass";
    exit 1
  end;
  (* completeness against the header's declaration (fail closed: a
     fixture without one is refused — a truncated fixture must not
     pass green) *)
  let complete =
    match !decl with
    | None ->
      prerr_endline "oracle: FAIL: fixture header carries no cases-per-kind=/kinds= declaration — cannot verify completeness, refusing";
      false
    | Some (cpk, kinds) ->
      let ok = ref true in
      List.iter (fun k ->
          let n = try Hashtbl.find seen k with Not_found -> 0 in
          if n <> cpk then begin
            Printf.eprintf "oracle: FAIL: kind %s: %d rows judged, header declares %d\n" k n cpk;
            ok := false
          end) kinds;
      Hashtbl.iter (fun k _ ->
          if not (List.mem k kinds) then begin
            Printf.eprintf "oracle: FAIL: rows of kind %s not declared in the header\n" k;
            ok := false
          end) seen;
      !ok
  in
  if !n_diverge > 0 || !n_infra > 0 || not complete then exit 1;
  print_endline "oracle: OK: Rocq extraction leg matches the Lean fixture on every case";
  exit 0
