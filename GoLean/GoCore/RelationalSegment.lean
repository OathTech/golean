import GoLean.GoCore.RelationalStorePath

/-! Finite segments expose every actual step. Their destination is a boundary,
not whole-program termination: an arbitrary saved tail can run forever. -/
namespace GoLean.GoCore.Relational
open Machine

/-- Totality at one admitted source, including unsuccessful alternatives.
The executable witness is discharged by local correspondence laws; clients
do not need the evaluator's equation catalogue. -/
def TotalStep (ctx : ProgramCtx) (a : State) : Prop :=
  ∀ ch, ∃ b : State, ∃ tail l, stepFn ctx a.store a.control ch = .ok (b.control, b.store, tail, l)

/-- A finite all-successor derivation to a designated boundary. `allowed`
retains a client observation contract at every real step. No atomic segment
step is introduced. This carrier alone is not a sequentialization theorem. -/
inductive SafeUntil (ctx : ProgramCtx) (allowed : State → StepLabel → State → Prop)
    (post : State → Prop) : State → Prop where
  | done {a} : post a → SafeUntil ctx allowed post a
  | step {a} : StepAdmission a.control → TotalStep ctx a →
      (∀ l b, Transition ctx a l b → allowed a l b) →
      (∀ l b, Transition ctx a l b → SafeUntil ctx allowed post b) →
      SafeUntil ctx allowed post a

/-- Prefixes of a segment stop at its boundary rather than executing the
arbitrary following program. The ordinary labelled run is retained. -/
inductive SegmentPrefix (ctx : ProgramCtx) (post : State → Prop) :
    State → List StepLabel → State → Prop where
  | refl {a} : SegmentPrefix ctx post a [] a
  | step {a b c l ls} : ¬ post a → Transition ctx a l b →
      SegmentPrefix ctx post b ls c → SegmentPrefix ctx post a (l :: ls) c

theorem SegmentPrefix.run {ctx post a b ls} (h : SegmentPrefix ctx post a ls b) :
    Run ctx a ls b := by
  induction h with
  | refl => exact .refl
  | step _ ht _ ih => exact .cons ht ih

theorem SegmentPrefix.append {ctx post a b c xs ys}
    (left : SegmentPrefix ctx post a xs b) (right : SegmentPrefix ctx post b ys c) :
    SegmentPrefix ctx post a (xs ++ ys) c := by
  induction left with
  | refl => exact right
  | step hn ht _ ih => exact .step hn ht (ih right)

theorem SafeUntil.after_prefix {ctx allowed post a b ls}
    (safe : SafeUntil ctx allowed post a) (pre : SegmentPrefix ctx post a ls b) :
    SafeUntil ctx allowed post b := by
  induction pre with
  | refl => exact safe
  | step hn ht _ ih =>
    cases safe with
    | done hp => exact False.elim (hn hp)
    | step _ _ _ next => exact ih (next _ _ ht)

theorem SafeUntil.progress {ctx allowed post a}
    (safe : SafeUntil ctx allowed post a) (notDone : ¬ post a) :
    StepAdmission a.control ∧ TotalStep ctx a ∧
      ∀ l b, Transition ctx a l b → allowed a l b ∧ SafeUntil ctx allowed post b := by
  cases safe with
  | done h => exact False.elim (notDone h)
  | step admission total labels next => exact ⟨admission, total, fun l b h => ⟨labels l b h, next l b h⟩⟩

theorem SafeUntil.realizes {ctx allowed post a} (safe : SafeUntil ctx allowed post a) :
    ∃ labels b, Run ctx a labels b ∧ post b := by
  induction safe with
  | done hp => exact ⟨[], _, .refl, hp⟩
  | step _ total _ _ ih =>
    obtain ⟨b, tail, l, he⟩ := total []
    have hs : Transition _ _ l b := stepFn_sound he
    obtain ⟨ls, c, hr, hp⟩ := ih l b hs
    exact ⟨l :: ls, c, .cons hs hr, hp⟩

theorem SafeUntil.deterministic_step {ctx allowed post a b l}
    (admission : StepAdmission a.control) (step : Transition ctx a l b)
    (pickFree : l.picks = []) (label : allowed a l b)
    (rest : SafeUntil ctx allowed post b) : SafeUntil ctx allowed post a := by
  refine .step admission (fun ch => ⟨b, ch, l, step.on_any_tape pickFree ch⟩) ?_ ?_
  · intro m c hs
    obtain ⟨rfl, rfl⟩ := step.unique_of_no_picks pickFree hs
    exact label
  · intro m c hs
    obtain ⟨rfl, rfl⟩ := step.unique_of_no_picks pickFree hs
    exact rest

/-- Existing compositional expression paths supply intermediate admission,
preservation, progress on every tape and all-successor closure. Observation
silence is a separate premise and is never inferred from race-trace silence. -/
theorem StorePath.safeUntil {ctx fact c d} (path : StorePath ctx fact c d)
    {post : State → Prop} (s : Store) (holds : fact s)
    (finish : SafeUntil ctx (fun _ _ _ => True) post ⟨d, s⟩) :
    SafeUntil ctx (fun _ _ _ => True) post ⟨c, s⟩ := by
  induction path with
  | refl => exact finish
  | step transition admission _ ih =>
    obtain ⟨l, hs, hp⟩ := transition s holds
    exact .deterministic_step admission hs hp trivial (ih finish)

theorem StorePath.safeUntil_with {ctx fact c d} (path : StorePath ctx fact c d)
    {allowed : State → StepLabel → State → Prop} {post : State → Prop}
    (s : Store) (holds : fact s)
    (labels : ∀ c d l, Transition ctx ⟨c, s⟩ l ⟨d, s⟩ → allowed ⟨c, s⟩ l ⟨d, s⟩)
    (finish : SafeUntil ctx allowed post ⟨d, s⟩) : SafeUntil ctx allowed post ⟨c, s⟩ := by
  induction path with
  | refl => exact finish
  | step transition admission _ ih =>
    obtain ⟨l, hs, hp⟩ := transition s holds
    exact .deterministic_step admission hs hp (labels _ _ _ hs) (ih finish)

private theorem delivered_silent {α : Type} {s t : Store} {k c}
    {next : α → Config × Store × StepLabel} {r : Result α} {chain ps l}
    (h : deliver s k next r chain ps = (c, t, l))
    (quiet : ∀ x, (next x).2.2.out = []) : l.out = [] := by
  cases r with
  | ok x => exact (congrArg (fun x => x.2.2.out) h).symm.trans (quiet x)
  | panic msg => exact (congrArg (fun x => x.2.2.out) h).symm

/-- Admission's initialization guard excludes the actual print output, not
just an access event. This does not imply silence of a control-sensitive
client observation. -/
theorem Transition.output_quiet {ctx a b l} (h : Transition ctx a l b)
    (ad : StepAdmission a.control) : l.out = [] := by
  rcases a with ⟨c,s⟩; rcases b with ⟨d,t⟩
  cases h <;> try rfl
  all_goals first
    | apply delivered_silent (by assumption); intros; rfl
    | skip
  rename_i op nt done v r env k ch hres hdel
  apply delivered_silent hdel
  intro x
  have hp : printOut? (.retV v (.stmtOpK op nt done [] env k)) = none := by
    have ha := ad.initializes
    unfold initPrintRefusal? at ha
    split at ha
    · contradiction
    · assumption
  have ho : stmtOpOut op (v :: done).reverse = [] := by
    rw [← printOut?_toList (nt := nt) (env := env) (k := k), hp]
    rfl
  simp only [ho]

/-- Supply the observation's actual per-step requirement. Output-only
observations discharge it via `Transition.output_quiet`; projections observing
control boundaries need their own proof, as with `PureFor`. -/
theorem SafeUntil.observe {Event : Type} {ctx allowed post a}
    (safe : SafeUntil ctx allowed post a)
    (observe : State → StepLabel → State → List Event)
    (silent : ∀ a l b, StepAdmission a.control → Transition ctx a l b →
      allowed a l b → observe a l b = []) :
    SafeUntil ctx (fun a l b => allowed a l b ∧ observe a l b = []) post a := by
  induction safe with
  | done h => exact .done h
  | step ad total labels _ ih =>
    exact .step ad total (fun l b ht => ⟨labels l b ht, silent _ _ _ ad ht (labels l b ht)⟩) ih

theorem SafeUntil.output {ctx allowed post a} (safe : SafeUntil ctx allowed post a) :
    SafeUntil ctx (fun a l b => allowed a l b ∧ l.out = []) post a :=
  safe.observe (fun _ l _ => l.out) (fun _ _ _ ad ht _ => ht.output_quiet ad)

/-- A projection need only be silent at reachable pre-boundary controls.
Unlike the uniform `observe` lemma this does not ask about unrelated
transitions satisfying the same heap invariant. -/
theorem SafeUntil.observe_prefix {Event : Type} {ctx allowed post source}
    (safe : SafeUntil ctx allowed post source)
    (observe : State → StepLabel → State → List Event)
    (silent : ∀ ls a l b, SegmentPrefix ctx post source ls a → ¬ post a →
      Transition ctx a l b → observe a l b = []) :
    SafeUntil ctx (fun a l b => allowed a l b ∧ observe a l b = []) post source := by
  have lift : ∀ {a}, SafeUntil ctx allowed post a → ∀ {ls},
      SegmentPrefix ctx post source ls a →
      SafeUntil ctx (fun a l b => allowed a l b ∧ observe a l b = []) post a := by
    intro a h
    induction h with
    | done hp => intro _ _; exact .done hp
    | @step current ad total labels _ ih =>
      intro ls pre
      by_cases hp : post current
      · exact .done hp
      · exact .step ad total
          (fun l b ht => ⟨labels l b ht, silent ls _ l b pre hp ht⟩)
          (fun l b ht => ih l b ht (pre.append (.step hp ht .refl)))
  exact lift safe .refl

theorem SafeUntil.prefix_fact {ctx allowed post a b ls} {fact : State → Prop}
    (safe : SafeUntil ctx allowed post a) (initial : fact a)
    (labels : ∀ a l b, allowed a l b → fact b)
    (pre : SegmentPrefix ctx post a ls b) : fact b := by
  induction pre with
  | refl => exact initial
  | step hn ht _ ih =>
    obtain ⟨_, _, next⟩ := safe.progress hn
    exact ih (next _ _ ht).2 (labels _ _ _ (next _ _ ht).1)

theorem SafeUntil.weaken {ctx allowed allowed' post a}
    (safe : SafeUntil ctx allowed post a)
    (imp : ∀ a l b, allowed a l b → allowed' a l b) :
    SafeUntil ctx allowed' post a := by
  induction safe with
  | done h => exact .done h
  | step ad total labels _ ih =>
    exact .step ad total (fun l b ht => imp _ _ _ (labels l b ht)) ih

/-- No infinite execution can remain inside a safe segment. This places no
restriction on the continuation after the boundary, including an infinite one. -/
theorem SafeUntil.eventually {ctx allowed post a}
    (safe : SafeUntil ctx allowed post a)
    (states : Nat → State) (labels : Nat → StepLabel) (start : states 0 = a)
    (steps : ∀ n, ¬ post (states n) → Transition ctx (states n) (labels n) (states (n+1))) :
    ∃ n, post (states n) := by
  induction safe generalizing states labels with
  | done h => exact ⟨0, start ▸ h⟩
  | @step source _ _ _ _ ih =>
    by_cases h : post (states 0)
    · exact ⟨0, h⟩
    have ht : Transition ctx source (labels 0) (states 1) := by simpa only [start] using steps 0 h
    obtain ⟨n, hn⟩ := ih _ _ ht (fun n => states (n+1)) (fun n => labels (n+1))
      rfl (fun n => steps (n+1))
    exact ⟨n+1, hn⟩

end GoLean.GoCore.Relational
