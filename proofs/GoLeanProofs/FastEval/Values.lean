import GoLeanProofs.FastEval.Shared

/-!
# FastEval — `applyStrictOpF` (campaign Arc 2, U4, wave worker A)

The mirror of `applyStrictOp` (`GoLean/GoCore/Machine.lean:262`) over
the trie state, one-directional (`.ok` transports; every arm the
witness run does not exercise is a FAIL-CLOSED STUB — probe D census,
`docs/campaign-arc2-probes/records/probeD-armcensus.out`), plus the
sim `applyStrictOpF_ok`.

UNTRUSTED METHOD — no name in this file may appear in any headline
statement's closure (the Sym position; design note
`docs/2026-08-22_fasteval-design.md`).

Census notes: `defaultValueOf` and `nilLit` are NULLARY strict ops —
they never surface as `strictK` census rows (the classifier's known
blind spot: nullary strict plans apply without a `strictK`
configuration) but their `evalE` rows (`defaultValueE` 1273, `nilE`
6683) prove them exercised, so they are mirrored, not stubbed.
-/

namespace GoLean.FastEval

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- `applySlice`, fast (only the `.addr` arm reads the heap). -/
def applySliceF (σF : ExecStateF) (b : GoValue) (lowValue highValue : Int)
    (maxValue : Option Int) : Except GoError (GoValue × ExecStateF) := do
  match b with
  | .string value => return ((← stringSlice value lowValue highValue maxValue), σF)
  | .slice slice => return ((← sliceFromSlice slice lowValue highValue maxValue), σF)
  | .addr baseLoc =>
      match ← loadLocF σF baseLoc with
      | .array values =>
          return ((← sliceFromArray baseLoc values.size lowValue highValue maxValue), σF)
      | .slice slice => return ((← sliceFromSlice slice lowValue highValue maxValue), σF)
      | other => stuck s!"expected array or slice base for slice expression, got {repr other}"
  | .array values =>
      unsupported s!"slice expression over non-addressable array value of length {values.size}"
  | other => stuck s!"expected array or slice value for slice expression, got {repr other}"

/-! ## P2R arm helpers (unit P2R, slice 4): each closes a former
`fastEval-stub` arm the probe_and_replicate replay exercises. Each is a
SEPARATE def called from its top-level alternative so
`applyStrictOpF_ok`'s split structure stays stable (one alternative =
one bullet), with its own `_ok` transport below. Mirrors are verbatim
from `applyStrictOp`'s arms (state-free helpers unchanged; `s.alloc` →
`allocF`, `loadLoc` → `loadLocF`, pure helpers at `ctxF`). -/

def mulArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [l, r] =>
      match l, r with
      | .float .., .float .. => do
          return ((← floatBinaryResult "*" FloatBits.fmul64 FloatBits.fmul32 l r), σF)
      | _, _ => do return ((← intBinaryResult "*" (· * ·) l r), σF)
  | _ => stuck "malformed strict-operator application: mul"

def shiftLeftArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [l, r] => do return ((← intShiftLeftResult l r), σF)
  | _ => stuck "malformed strict-operator application: shiftLeft"

def bitOrArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [l, r] => do return ((← intBitwiseBinaryResult "|" Nat.lor l r), σF)
  | _ => stuck "malformed strict-operator application: bitOr"

def bitXorArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [l, r] => do return ((← intBitwiseBinaryResult "^" Nat.xor l r), σF)
  | _ => stuck "malformed strict-operator application: bitXor"

def bitClearArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [l, r] => do return ((← intBitClearResult l r), σF)
  | _ => stuck "malformed strict-operator application: bitClear"

def bitNegArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [v] => do return ((← intBitNegResult v), σF)
  | _ => stuck "malformed strict-operator application: bitNeg"

def negArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [v] =>
      match v with
      | .int value kind => return (.int (kind.normalize (0 - value)) kind, σF)
      | .float bits kind => return (.float (kind.normalizeBits (kind.negBits bits)) kind, σF)
      | other => stuck s!"mismatched unary - operand: {repr other}"
  | _ => stuck "malformed strict-operator application: neg"

def floatLitArmF (σF : ExecStateF) (num : Int) (den : Nat) (kind : FloatKind) :
    List GoValue → Except GoError (GoValue × ExecStateF)
  | [] =>
      if den == 0 then stuck "malformed float literal: zero denominator"
      else return (.float (kind.normalizeBits (kind.ratToBits num den)) kind, σF)
  | _ => stuck "malformed strict-operator application: floatLit"

def bytesFromStringArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [v] =>
      match v with
      | .string value =>
          let bytes := value.bytes.map (fun b => GoValue.int (Int.ofNat b.toNat) .uint8)
          let (base, σF') := allocF σF (.array bytes) (some (.array bytes.size (.int .uint8)))
          .ok (.slice { base := some base, offset := 0, len := bytes.size, cap := bytes.size }, σF')
      | other => stuck s!"expected string operand for []byte conversion, got {repr other}"
  | _ => stuck "malformed strict-operator application: bytesFromString"

def addrOfDerefArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [v] => do return (.addr (← valueAsLoc v), σF)
  | _ => stuck "malformed strict-operator application: addrOfDeref"

def indexAddrArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [b, i] => do return (.addr (← indexTargetLocF σF b i), σF)
  | _ => stuck "malformed strict-operator application: indexAddr"

def capacityOfArmF (σF : ExecStateF) (typ : Option Ty) :
    List GoValue → Except GoError (GoValue × ExecStateF)
  | [v] => do
      match typ with
      | some (.pointer (.array n _)) => return (.int n, σF)
      | _ =>
          match v with
          | .array values => return (.int values.size, σF)
          | .addr baseLoc =>
              match ← loadLocF σF baseLoc with
              | .array values => return (.int values.size, σF)
              | other => unsupported s!"cap for non-array pointer value {repr other}"
          | .slice slice =>
              validateSlice slice *> return (.int slice.cap, σF)
          | .chan _ => stuck "fastEval-stub: applyStrictOp.capacityOf.chan"
          | other => unsupported s!"cap for non-array/slice value {repr other}"
  | _ => stuck "malformed strict-operator application: capacityOf"

def runeAtArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [sv, ov] => do
      match sv with
      | .string str => do
          let off ← valueAsInt ov
          if off < 0 then
            stuck s!"negative rune-decode offset {off}"
          return (.int (decodeRuneAt str off.toNat).1 .int32, σF)
      | other => stuck s!"expected string operand for rune decode, got {repr other}"
  | _ => stuck "malformed strict-operator application: runeAt"

def runeSizeAtArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [sv, ov] => do
      match sv with
      | .string str => do
          let off ← valueAsInt ov
          if off < 0 then
            stuck s!"negative rune-decode offset {off}"
          return (.int (Int.ofNat (decodeRuneAt str off.toNat).2) .int, σF)
      | other => stuck s!"expected string operand for rune decode, got {repr other}"
  | _ => stuck "malformed strict-operator application: runeSizeAt"

def runesFromStringArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [v] =>
      match v with
      | .string value =>
          let runes := (runesOfString value).map
            (fun r => GoValue.int r .int32)
          let (base, σF') := allocF σF (.array runes)
            (some (.array runes.size (.int .int32)))
          .ok (.slice { base := some base, offset := 0,
                        len := runes.size, cap := runes.size }, σF')
      | other => stuck s!"expected string operand for []rune conversion, got {repr other}"
  | _ => stuck "malformed strict-operator application: runesFromString"

def stringFromRuneSliceArmF (σF : ExecStateF) : List GoValue → Except GoError (GoValue × ExecStateF)
  | [v] => do
      let slice ← valueAsSlice v
      let values ← sliceVisibleValuesF σF slice
      let mut str := GoString.empty
      for value in values.toList do
        match value with
        | .int r .int32 => str := str.append (GoString.fromCodePoint r)
        | other => stuck s!"expected rune element in string conversion, got {repr other}"
      return (.string str, σF)
  | _ => stuck "malformed strict-operator application: stringFromRuneSlice"

/-- The mirror. Arm-for-arm with `applyStrictOp`; census-stubbed arms
refuse (`fastEval-stub`), pure helpers run at the O(1) `ctxF σF`
context image, heap reads go through `loadLocF`. -/
def applyStrictOpF (σF : ExecStateF) : StrictOp → List GoValue →
    Except GoError (GoValue × ExecStateF)
  | .add, [l, r] =>
      match l, r with
      | .int .., .int .. => do return ((← intBinaryResult "+" (· + ·) l r), σF)
      | .float .., .float .. => do
          return ((← floatBinaryResult "+" FloatBits.fadd64 FloatBits.fadd32 l r), σF)
      | .string lv, .string rv => return (.string (GoString.append lv rv), σF)
      | _, _ => stuck s!"mismatched + operands: {repr l} and {repr r}"
  | .sub, [l, r] =>
      match l, r with
      | .float .., .float .. => do
          return ((← floatBinaryResult "-" FloatBits.fsub64 FloatBits.fsub32 l r), σF)
      | _, _ => do return ((← intBinaryResult "-" (· - ·) l r), σF)
  | .mul, args => mulArmF σF args
  | .div, [l, r] =>
      match l, r with
      | .float .., .float .. => do
          return ((← floatBinaryResult "/" FloatBits.fdiv64 FloatBits.fdiv32 l r), σF)
      | _, _ => do
          let divisor ← valueAsInt r
          if divisor == 0 then
            GoCore.panic "runtime error: integer divide by zero"
          return ((← intBinaryResult "/" Int.tdiv l r), σF)
  | .mod, [l, r] => do
      let divisor ← valueAsInt r
      if divisor == 0 then
        GoCore.panic "runtime error: integer divide by zero"
      return ((← intBinaryResult "%" Int.tmod l r), σF)
  | .shiftLeft, args => shiftLeftArmF σF args
  | .shiftRight, [l, r] => do return ((← intShiftRightResult l r), σF)
  | .bitAnd, [l, r] => do return ((← intBitwiseBinaryResult "&" Nat.land l r), σF)
  | .bitOr, args => bitOrArmF σF args
  | .bitXor, args => bitXorArmF σF args
  | .bitClear, args => bitClearArmF σF args
  | .bitNeg, args => bitNegArmF σF args
  | .neg, args => negArmF σF args
  | .floatLit num den kind, args => floatLitArmF σF num den kind args
  | .not, [v] => do return (.bool (!(← valueAsBool v)), σF)
  | .eqCmp ty, [l, r] => do return (.bool (← valueEq (ctxF σF) ty l r), σF)
  | .neqCmp ty, [l, r] => do return (.bool (!(← valueEq (ctxF σF) ty l r)), σF)
  | .atMostCmp, [l, r] => do return (.bool (← valueAtMost l r), σF)
  | .atLeastCmp, [l, r] => do return (.bool (← valueAtLeast l r), σF)
  | .lessCmp, [l, r] => do return (.bool (← valueLess l r), σF)
  | .greaterCmp, [l, r] => do return (.bool (← valueGreater l r), σF)
  | .convert ty, [v] => do return ((← convertValueToTy (ctxF σF) ty v), σF)
  | .bytesFromString, args => bytesFromStringArmF σF args
  | .stringFromByteSlice, [v] => do
      let slice ← valueAsSlice v
      let values ← sliceVisibleValuesF σF slice
      let bytes ← forIn values.toList (#[] : Array UInt8) (fun value bytes => do
        match value with
        | .int byte .uint8 =>
            if byte < 0 || byte > 255 then
              stuck s!"malformed uint8 byte value in string conversion: {byte}"
            pure (ForInStep.yield (bytes.push (UInt8.ofNat byte.toNat)))
        | other => stuck s!"expected uint8 element in string conversion, got {repr other}")
      return (.string { bytes := bytes }, σF)
  | .stringFromRune, [v] => do
      return (.string (GoString.fromCodePoint (← valueAsInt v)), σF)
  | .deref _, [v] => do return ((← loadLocF σF (← valueAsLoc v)), σF)
  | .addrOfDeref, args => addrOfDerefArmF σF args
  | .fieldGet typeId fieldName, [v] => do
      match v with
      | .struct actualType fields =>
          if actualType != typeId && !structTagCompatible (ctxF σF) actualType typeId then
            stuck s!"expected struct {typeId.key}, got struct {actualType.key}"
          match StructFields.lookup fields fieldName with
          | some value => return (value, σF)
          | none => stuck s!"unknown GoCore struct field: {fieldName}"
      | other => stuck s!"expected struct value for field access, got {repr other}"
  | .fieldAddr typeId fieldName, [v] => do
      return (.addr (.field (← valueAsLoc v) typeId fieldName), σF)
  | .structLit ty, vs => do return ((← buildStructValue (ctxF σF) ty vs.toArray), σF)
  | .arrayLit n elem keys, vs => do
      if keys.length != vs.length then
        stuck s!"array literal expected {keys.length} element value(s), got {vs.length}"
      return ((← buildArrayValue (ctxF σF) n elem (keys.zip vs).toArray), σF)
  | .toInterface _ dynamic, [v] => do
      let dynTy ← canonicalDynamicTy (ctxF σF) dynamic
      match dynTy with
      | .interface _ => return (v, σF)
      | _ => return (.interface dynTy v, σF)
  | .typeAssert targetTy sourceTy, [v] => do
      let result ← typeAssertValue (ctxF σF) v targetTy
      if result.2 then
        return (result.1, σF)
      else
        -- one-directional stub: the slow side panics here too, but the
        -- message computation is not mirrored (a failing assert never
        -- returns `.ok`, so the sim case is vacuous either way)
        GoCore.panic "fastEval-stub: typeAssert failure path"
  | .indexGet, [b, i] => do
      let indexValue ← valueAsInt i
      match b with
      | .array values => return ((← arrayGet values indexValue), σF)
      | .string value => return ((← stringByteGet value indexValue), σF)
      | .slice slice =>
          return ((← loadLocF σF (← sliceIndexLoc slice indexValue)), σF)
      | .addr baseLoc =>
          match ← loadLocF σF baseLoc with
          | .array values => return ((← arrayGet values indexValue), σF)
          | other => stuck s!"expected array pointee for index access, got {repr other}"
      | .nil => GoCore.panic "runtime error: invalid memory address or nil pointer dereference"
      | other => stuck s!"expected array, slice, or string value for index access, got {repr other}"
  | .indexAddr, args => indexAddrArmF σF args
  | .mapGet keyTy valueTy, [b, i] => do
      let map ← valueAsMap b
      let key ← normalizeValueForTy (ctxF σF) keyTy i
      match map.base with
      | none => do
          checkKeyHashable (ctxF σF) key (isInsert := false) (nonEmpty := false)
          return ((← defaultValue (ctxF σF) valueTy), σF)
      | some baseLoc =>
          match ← loadLocF σF baseLoc with
          | .mapData entries =>
              match ← mapEntryIndex? (ctxF σF) keyTy entries key with
              | some idx =>
                  match entries[idx]? with
                  | some (_, value) => return (value, σF)
                  | none => stuck s!"missing map entry at index {idx}"
              | none => return ((← defaultValue (ctxF σF) valueTy), σF)
          | other => stuck s!"expected map data, got {repr other}"
  | .sliceExpr false, [b, lo, hi] => do
      applySliceF σF b (← valueAsInt lo) (← valueAsInt hi) none
  | .sliceExpr true, [b, lo, hi, m] => do
      applySliceF σF b (← valueAsInt lo) (← valueAsInt hi) (some (← valueAsInt m))
  | .lengthOf typ, [v] => do
      match typ with
      | some (.pointer (.array n _)) => return (.int n, σF)
      | _ =>
          match v with
          | .array values => return (.int values.size, σF)
          | .addr baseLoc =>
              match ← loadLocF σF baseLoc with
              | .array values => return (.int values.size, σF)
              | other => unsupported s!"len for non-array pointer value {repr other}"
          | .string value => return (.int value.length, σF)
          | .slice slice =>
              validateSlice slice *> return (.int slice.len, σF)
          | .map map =>
              match map.base with
              | none => return (.int 0, σF)
              | some baseLoc =>
                  match ← loadLocF σF baseLoc with
                  | .mapData entries => return (.int entries.size, σF)
                  | other => stuck s!"expected map data, got {repr other}"
          | .chan _ => stuck "fastEval-stub: applyStrictOp.lengthOf.chan"
          | other => unsupported s!"len for non-array/slice/map value {repr other}"
  | .capacityOf typ, args => capacityOfArmF σF typ args
  | .funcValOf fid, vs => return (.funcVal fid vs, σF)
  | .minOf, v :: vs =>
      if anyFloatOperand (v :: vs) then do
        let mut best := v
        for w in vs do
          best ← floatMinMax true best w
        return (best, σF)
      else do
        let mut best := v
        for w in vs do
          if ← valueLess w best then
            best := w
        return (best, σF)
  | .maxOf, v :: vs =>
      if anyFloatOperand (v :: vs) then do
        let mut best := v
        for w in vs do
          best ← floatMinMax false best w
        return (best, σF)
      else do
        let mut best := v
        for w in vs do
          if ← valueLess best w then
            best := w
        return (best, σF)
  | .runeAt, args => runeAtArmF σF args
  | .runeSizeAt, args => runeSizeAtArmF σF args
  | .defaultValueOf ty, [] => do return ((← defaultValue (ctxF σF) ty), σF)
  | .nilLit typ, [] =>
      match typ with
      | none => return (.nil, σF)
      | some ty =>
          match ty with
          | .slice _ => do return ((← defaultValue (ctxF σF) ty), σF)
          | .map _ _ => do return ((← defaultValue (ctxF σF) ty), σF)
          | .chan _ _ => do return ((← defaultValue (ctxF σF) ty), σF)
          | .pointer _ => return (.nil, σF)
          | .unsupported feature => unsupported s!"nil literal for {feature}"
          | other => stuck s!"nil literal for non-nilable type {repr other}"
  | .runesFromString, args => runesFromStringArmF σF args
  | .stringFromRuneSlice, args => stringFromRuneSliceArmF σF args
  | op, vs => stuck s!"malformed strict-operator application: {repr op} on {vs.length} operand(s)"

/-! ## The sims -/

/-- The pure-arm transport: a computation shared verbatim by both
sides (the lazy view), followed by the state-passing tuple. `comp` and
`g` are found by unification — no per-arm spelling (this also carries
whole `let mut`/`for` loops when they mention no state: minOf/maxOf).
PROMOTION NOTE: lift to a shared FastEval module on the second
wave-consumer. -/
theorem pureArm_sim {α : Type} {σF σF' : ExecStateF} {comp : Except GoError α}
    {g : α → GoValue} {v : GoValue}
    (h : (do let x ← comp; pure (g x, σF) : Except GoError (GoValue × ExecStateF)) = .ok (v, σF')) :
    (do let x ← comp; pure (g x, γF σF) : Except GoError (GoValue × ExecState)) = .ok (v, γF σF') := by
  cases comp with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok x =>
      simp only [Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩

/-- Value-only arms with NO leading computation. -/
theorem constArm_sim {σF σF' : ExecStateF} {w v : GoValue}
    (h : (pure (w, σF) : Except GoError (GoValue × ExecStateF)) = .ok (v, σF')) :
    (pure (w, γF σF) : Except GoError (GoValue × ExecState)) = .ok (v, γF σF') := by
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, by rw [h.2]⟩

theorem applySliceF_ok {σF : ExecStateF} {b : GoValue} {lo hi : Int}
    {m : Option Int} {v : GoValue} {σF' : ExecStateF}
    (h : applySliceF σF b lo hi m = .ok (v, σF')) :
    applySlice (γF σF) b lo hi m = .ok (v, γF σF') := by
  unfold applySliceF at h
  split at h
  · simp only [applySlice]; exact pureArm_sim h
  · simp only [applySlice]; exact pureArm_sim h
  · rename_i baseLoc
    simp only [applySlice]
    cases hl : loadLocF σF baseLoc with
    | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok bv =>
        rw [hl] at h
        rw [loadLocF_ok hl]
        simp only [Bind.bind, Except.bind] at h ⊢
        cases bv
        case array values => exact pureArm_sim h
        case slice slice => exact pureArm_sim h
        all_goals simp at h
  · simp at h
  · simp at h

/-- Close a fully-reduced tuple step: goal `pure (w, γF σF) = .ok (v, γF σF')`
from `h : pure (w, σF) = .ok (v, σF')` (possibly still behind
reducible bind-of-ok matches on both sides). PROMOTION NOTE: lift to a
shared FastEval tactics module on the second wave-consumer. -/
macro "tuple_close" h:ident : tactic =>
  `(tactic| simp only [Bind.bind, Except.bind, pure, Except.pure,
      SeqRight.seqRight, Except.map, Except.ok.injEq, Prod.mk.injEq]
        at $h:ident ⊢ <;>
      (first | exact ⟨($h).1, by rw [($h).2]⟩ | (obtain ⟨h1, h2⟩ := $h; subst h2; exact ⟨h1, rfl⟩) | exact $h | simp [$h:ident]))

/-- Close an absurd fast-side hypothesis (an error-headed computation
equated to `.ok`), through stuck/unsupported/panic and bind plumbing.
PROMOTION NOTE: lift to a shared FastEval tactics module on the second
wave-consumer. -/
macro "absurd_h" h:ident : tactic =>
  `(tactic| first
      | injection $h
      | simp [stuck, unsupported, GoCore.panic, throw, throwThe,
          MonadExceptOf.throw, Bind.bind, Except.bind, pure,
          Except.pure] at $h:ident)


/-! ### P2R arm transports (one per helper; bullets stay 1:1) -/

theorem mulArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : mulArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .mul args = .ok (v, γF σF') := by
  unfold mulArmF at h
  split at h
  · rename_i l r
    simp only [applyStrictOp]
    split at h
    · exact pureArm_sim h
    · split
      · simp [intBinaryResult, valueAsIntValue, stuck, Bind.bind,
          Except.bind] at h
      · exact pureArm_sim h
  · simp [stuck] at h

theorem shiftLeftArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : shiftLeftArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .shiftLeft args = .ok (v, γF σF') := by
  unfold shiftLeftArmF at h
  split at h
  · simp only [applyStrictOp]; exact pureArm_sim h
  · simp [stuck] at h

theorem bitOrArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : bitOrArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .bitOr args = .ok (v, γF σF') := by
  unfold bitOrArmF at h
  split at h
  · simp only [applyStrictOp]; exact pureArm_sim h
  · simp [stuck] at h

theorem bitXorArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : bitXorArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .bitXor args = .ok (v, γF σF') := by
  unfold bitXorArmF at h
  split at h
  · simp only [applyStrictOp]; exact pureArm_sim h
  · simp [stuck] at h

theorem bitClearArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : bitClearArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .bitClear args = .ok (v, γF σF') := by
  unfold bitClearArmF at h
  split at h
  · simp only [applyStrictOp]; exact pureArm_sim h
  · simp [stuck] at h

theorem bitNegArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : bitNegArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .bitNeg args = .ok (v, γF σF') := by
  unfold bitNegArmF at h
  split at h
  · simp only [applyStrictOp]; exact pureArm_sim h
  · simp [stuck] at h

theorem negArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : negArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .neg args = .ok (v, γF σF') := by
  unfold negArmF at h
  split at h
  · split at h
    · simp only [applyStrictOp]; tuple_close h
    · simp only [applyStrictOp]; tuple_close h
    · absurd_h h
  · simp [stuck] at h

theorem floatLitArmF_ok {σF σF' : ExecStateF} {num : Int} {den : Nat}
    {kind : FloatKind} {args : List GoValue} {v : GoValue}
    (h : floatLitArmF σF num den kind args = .ok (v, σF')) :
    applyStrictOp (γF σF) (.floatLit num den kind) args = .ok (v, γF σF') := by
  unfold floatLitArmF at h
  split at h
  · simp only [applyStrictOp]
    split at h
    · absurd_h h
    · rename_i hden
      rw [if_neg hden]
      tuple_close h
  · simp [stuck] at h

theorem bytesFromStringArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : bytesFromStringArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .bytesFromString args = .ok (v, γF σF') := by
  unfold bytesFromStringArmF at h
  split at h
  · split at h
    · rename_i value
      simp only [applyStrictOp]
      rw [← allocF_loc, ← allocF_state]
      injection h with h1
      injection h1 with hv hs
      subst hv
      subst hs
      rfl
    · absurd_h h
  · simp [stuck] at h

theorem addrOfDerefArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : addrOfDerefArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .addrOfDeref args = .ok (v, γF σF') := by
  unfold addrOfDerefArmF at h
  split at h
  · simp only [applyStrictOp]; exact pureArm_sim h
  · simp [stuck] at h

theorem indexAddrArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : indexAddrArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .indexAddr args = .ok (v, γF σF') := by
  unfold indexAddrArmF at h
  split at h
  · rename_i b i
    simp only [applyStrictOp]
    cases hl : indexTargetLocF σF b i with
    | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
    | ok loc =>
        rw [hl] at h
        simp only [indexTargetLocF_ok hl]
        tuple_close h
  · simp [stuck] at h

theorem capacityOfArmF_ok {σF σF' : ExecStateF} {typ : Option Ty}
    {args : List GoValue} {v : GoValue}
    (h : capacityOfArmF σF typ args = .ok (v, σF')) :
    applyStrictOp (γF σF) (.capacityOf typ) args = .ok (v, γF σF') := by
  unfold capacityOfArmF at h
  split at h
  · simp only [applyStrictOp]
    split at h
    · tuple_close h
    · split at h
      · tuple_close h
      · rename_i baseLoc
        cases hl : loadLocF σF baseLoc with
        | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
        | ok bv =>
            rw [hl] at h
            simp only [loadLocF_ok hl]
            simp only [Bind.bind, Except.bind] at h ⊢
            cases bv <;> try (simp [unsupported] at h)
            case array values => tuple_close h
      · rename_i slice
        cases hv : validateSlice slice with
        | error e =>
            rw [hv] at h
            simp [Bind.bind, Except.bind, SeqRight.seqRight, Except.map] at h
        | ok u =>
            rw [hv] at h
            simp only [Bind.bind, Except.bind, SeqRight.seqRight, pure,
              Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h
            subst h2
            simp [hv, h1]
            rfl
      · simp [stuck] at h
      · simp [unsupported] at h
  · simp [stuck] at h

theorem runeAtArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : runeAtArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .runeAt args = .ok (v, γF σF') := by
  unfold runeAtArmF at h
  split at h
  · split at h
    · rename_i str
      simp only [applyStrictOp]
      cases ho : valueAsInt _ with
      | error e => rw [ho] at h; simp [Bind.bind, Except.bind] at h
      | ok off =>
          rw [ho] at h
          simp only [Bind.bind, Except.bind] at h ⊢
          split at h <;> rename_i hneg
          · simp [stuck, Bind.bind, Except.bind, throw, throwThe,
              MonadExceptOf.throw] at h
          · rw [if_neg hneg]
            tuple_close h
    · absurd_h h
  · simp [stuck] at h

theorem runeSizeAtArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : runeSizeAtArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .runeSizeAt args = .ok (v, γF σF') := by
  unfold runeSizeAtArmF at h
  split at h
  · split at h
    · rename_i str
      simp only [applyStrictOp]
      cases ho : valueAsInt _ with
      | error e => rw [ho] at h; simp [Bind.bind, Except.bind] at h
      | ok off =>
          rw [ho] at h
          simp only [Bind.bind, Except.bind] at h ⊢
          split at h <;> rename_i hneg
          · simp [stuck, Bind.bind, Except.bind, throw, throwThe,
              MonadExceptOf.throw] at h
          · rw [if_neg hneg]
            tuple_close h
    · absurd_h h
  · simp [stuck] at h

theorem runesFromStringArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : runesFromStringArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .runesFromString args = .ok (v, γF σF') := by
  unfold runesFromStringArmF at h
  split at h
  · split at h
    · rename_i value
      simp only [applyStrictOp]
      rw [← allocF_loc, ← allocF_state]
      injection h with h1
      injection h1 with hv hs
      subst hv
      subst hs
      rfl
    · absurd_h h
  · simp [stuck] at h

theorem stringFromRuneSliceArmF_ok {σF σF' : ExecStateF} {args : List GoValue} {v : GoValue}
    (h : stringFromRuneSliceArmF σF args = .ok (v, σF')) :
    applyStrictOp (γF σF) .stringFromRuneSlice args = .ok (v, γF σF') := by
  unfold stringFromRuneSliceArmF at h
  split at h
  · rename_i v0
    simp only [applyStrictOp]
    cases hsl : valueAsSlice v0 with
    | error e => rw [hsl] at h; simp [Bind.bind, Except.bind] at h
    | ok slice =>
        rw [hsl] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        cases hsv : sliceVisibleValuesF σF slice with
        | error e => rw [hsv] at h; simp at h
        | ok values =>
            rw [hsv] at h
            simp only [sliceVisibleValuesF_ok hsv]
            rw [← Array.forIn_toList]
            exact pureArm_sim h
  · simp [stuck] at h

theorem applyStrictOpF_ok {σF : ExecStateF} {op : StrictOp}
    {args : List GoValue} {v : GoValue} {σF' : ExecStateF} :
    applyStrictOpF σF op args = .ok (v, σF') →
    applyStrictOp (γF σF) op args = .ok (v, γF σF') := by
  intro h
  unfold applyStrictOpF at h
  simp only [valueEq_ctx, convertValueToTy_ctx, structTagCompatible_ctx,
    buildStructValue_ctx, buildArrayValue_ctx, canonicalDynamicTy_ctx,
    typeAssertValue_ctx, normalizeValueForTy_ctx, checkKeyHashable_ctx,
    defaultValue_ctx, mapEntryIndex?_ctx] at h
  split at h
  -- .add
  · rename_i l r
    simp only [applyStrictOp]
    split at h
    · exact pureArm_sim h
    · exact pureArm_sim h
    · tuple_close h
    · -- fast catch: pair against the goal's own match; impossible
      -- pairings die on the operand shape
      split
      · simp [stuck] at h
      · simp [stuck] at h
      · simp [stuck] at h
      · simp [stuck] at h
  -- .sub
  · rename_i l r
    simp only [applyStrictOp]
    split at h
    · exact pureArm_sim h
    · split
      · -- goal float branch under fast catch: the int computation
        -- refuses float operands
        simp [intBinaryResult, valueAsIntValue, stuck, Bind.bind,
          Except.bind] at h
      · exact pureArm_sim h
  -- .mul (P2R)
  · exact mulArmF_ok h
  -- .div
  · rename_i l r
    simp only [applyStrictOp]
    split at h
    · exact pureArm_sim h
    · split
      · -- goal float branch under fast catch: valueAsInt refuses floats
        simp [valueAsInt, stuck, Bind.bind, Except.bind] at h
      · cases hd : valueAsInt r with
        | error e => rw [hd] at h; simp [Bind.bind, Except.bind] at h
        | ok d =>
            rw [hd] at h
            simp only [hd, Bind.bind, Except.bind] at h ⊢
            split at h <;> rename_i hz
            · simp [GoCore.panic] at h
            · simp only [pure, Except.pure] at h
              simp only [hz, Bool.false_eq_true, if_false, pure, Except.pure]
              split at h <;> rename_i hx
              · injection h
              · tuple_close h
  -- .mod
  · rename_i l r
    simp only [applyStrictOp]
    cases hd : valueAsInt r with
    | error e => rw [hd] at h; simp [Bind.bind, Except.bind] at h
    | ok d =>
        rw [hd] at h
        simp only [hd, Bind.bind, Except.bind] at h ⊢
        split at h <;> rename_i hz
        · simp [GoCore.panic] at h
        · simp only [pure, Except.pure] at h
          simp only [hz, Bool.false_eq_true, if_false, pure, Except.pure]
          split at h <;> rename_i hx
          · injection h
          · tuple_close h
  -- .shiftLeft (P2R)
  · exact shiftLeftArmF_ok h
  -- .shiftRight
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .bitAnd
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- bitOr bitXor bitClear bitNeg neg floatLit (P2R)
  · exact bitOrArmF_ok h
  · exact bitXorArmF_ok h
  · exact bitClearArmF_ok h
  · exact bitNegArmF_ok h
  · exact negArmF_ok h
  · exact floatLitArmF_ok h
  -- .not
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .eqCmp
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .neqCmp
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .atMostCmp
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .atLeastCmp
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .lessCmp
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .greaterCmp
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .convert
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .bytesFromString (P2R)
  · exact bytesFromStringArmF_ok h
  -- .stringFromByteSlice
  · rename_i v0
    simp only [applyStrictOp]
    cases hsl : valueAsSlice v0 with
    | error e => rw [hsl] at h; simp [Bind.bind, Except.bind] at h
    | ok slice =>
        rw [hsl] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        cases hsv : sliceVisibleValuesF σF slice with
        | error e => rw [hsv] at h; simp at h
        | ok values =>
            rw [hsv] at h
            simp only [sliceVisibleValuesF_ok hsv]
            rw [← Array.forIn_toList]
            exact pureArm_sim h
  -- .stringFromRune
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .deref
  · rename_i v0
    simp only [applyStrictOp]
    cases hvl : valueAsLoc v0 with
    | error e => rw [hvl] at h; simp [Bind.bind, Except.bind] at h
    | ok loc =>
        rw [hvl] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        cases hl : loadLocF σF loc with
        | error e => rw [hl] at h; simp at h
        | ok lv =>
            rw [hl] at h
            simp only [loadLocF_ok hl]
            tuple_close h
  -- .addrOfDeref (P2R)
  · exact addrOfDerefArmF_ok h
  -- .fieldGet
  · rename_i typeId fieldName v0
    simp only [applyStrictOp]
    cases v0 <;> try (simp [stuck] at h)
    case struct actualType fields =>
      simp only [] at h ⊢
      split at h <;> rename_i hguard
      · absurd_h h
      · split
        · rename_i hg2
          exact absurd hg2 (by simpa using hguard)
        · split at h <;> rename_i hlk
          · try rw [hlk]
            tuple_close h
          · absurd_h h
  -- .fieldAddr
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .structLit
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .arrayLit
  · rename_i n elem keys
    simp only [applyStrictOp]
    split at h <;> rename_i hlen
    · absurd_h h
    · rw [if_neg hlen]
      exact pureArm_sim h
  -- .toInterface
  · rename_i dynamic v0
    simp only [applyStrictOp]
    cases hdyn : canonicalDynamicTy (γF σF) dynamic with
    | error e => rw [hdyn] at h; simp [Bind.bind, Except.bind] at h
    | ok dynTy =>
        rw [hdyn] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        split at h
        · tuple_close h
        · rename_i hne
          split
          · exact (hne _ rfl).elim
          · tuple_close h
  -- .typeAssert
  · rename_i targetTy sourceTy v0
    simp only [applyStrictOp]
    cases hta : typeAssertValue (γF σF) v0 targetTy with
    | error e => rw [hta] at h; simp [Bind.bind, Except.bind] at h
    | ok result =>
        rw [hta] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        split at h <;> rename_i hcond
        · rw [if_pos hcond]
          tuple_close h
        · absurd_h h
  -- .indexGet
  · rename_i b i
    simp only [applyStrictOp]
    cases hi : valueAsInt i with
    | error e => rw [hi] at h; simp [Bind.bind, Except.bind] at h
    | ok indexValue =>
        rw [hi] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        cases b <;> try (simp [stuck, GoCore.panic] at h)
        case array values => exact pureArm_sim h
        case string value => exact pureArm_sim h
        case slice slice =>
          cases hloc : sliceIndexLoc slice indexValue with
          | error e => rw [hloc] at h; simp [Bind.bind, Except.bind] at h
          | ok loc =>
              rw [hloc] at h
              simp only [Bind.bind, Except.bind] at h ⊢
              cases hl : loadLocF σF loc with
              | error e => rw [hl] at h; simp at h
              | ok lv =>
                  rw [hl] at h
                  simp only [Bind.bind, Except.bind, pure, Except.pure,
                    Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨h1, h2⟩ := h
                  subst h2
                  simp [hloc, loadLocF_ok hl, h1]
        case addr baseLoc =>
          cases hl : loadLocF σF baseLoc with
          | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
          | ok bv =>
              rw [hl] at h
              simp only [loadLocF_ok hl]
              simp only [Bind.bind, Except.bind] at h ⊢
              cases bv <;> try (simp [stuck] at h)
              case array values => exact pureArm_sim h
  -- .indexAddr (P2R)
  · exact indexAddrArmF_ok h
  -- .mapGet
  · rename_i keyTy valueTy b i
    simp only [applyStrictOp]
    cases hb : valueAsMap b with
    | error e => rw [hb] at h; simp [Bind.bind, Except.bind] at h
    | ok map =>
        rw [hb] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        cases hk : normalizeValueForTy (γF σF) keyTy i with
        | error e => rw [hk] at h; simp at h
        | ok key =>
            rw [hk] at h
            simp only [Bind.bind, Except.bind] at h ⊢
            split at h <;> rename_i hbase
            · rw [hbase]
              cases hh : checkKeyHashable (γF σF) key (isInsert := false) (nonEmpty := false) with
              | error e => rw [hh] at h; simp [Bind.bind, Except.bind] at h
              | ok u =>
                  rw [hh] at h
                  simp only [hh, Bind.bind, Except.bind] at h ⊢
                  exact pureArm_sim h
            · rename_i baseLoc
              rw [hbase]
              cases hl : loadLocF σF baseLoc with
              | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
              | ok bv =>
                  rw [hl] at h
                  simp only [loadLocF_ok hl]
                  simp only [Bind.bind, Except.bind] at h ⊢
                  cases bv <;> try (simp [stuck] at h)
                  case mapData entries =>
                    simp only [] at h ⊢
                    cases hidx : mapEntryIndex? (γF σF) keyTy entries key with
                    | error e => rw [hidx] at h; simp [Bind.bind, Except.bind] at h
                    | ok idxOpt =>
                        rw [hidx] at h
                        simp only [Bind.bind, Except.bind] at h ⊢
                        cases idxOpt with
                        | none => exact pureArm_sim h
                        | some idx =>
                            simp only [] at h ⊢
                            split at h <;> rename_i hent
                            · rw [hent]
                              tuple_close h
                            · simp [stuck] at h
  -- .sliceExpr false
  · rename_i b lo hi
    simp only [applyStrictOp]
    cases hlo : valueAsInt lo with
    | error e => rw [hlo] at h; simp [Bind.bind, Except.bind] at h
    | ok lov =>
        rw [hlo] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        cases hhi : valueAsInt hi with
        | error e => rw [hhi] at h; simp [Bind.bind, Except.bind] at h
        | ok hiv =>
            rw [hhi] at h
            simp only [Bind.bind, Except.bind] at h ⊢
            exact applySliceF_ok h
  -- .sliceExpr true
  · rename_i b lo hi m
    simp only [applyStrictOp]
    cases hlo : valueAsInt lo with
    | error e => rw [hlo] at h; simp [Bind.bind, Except.bind] at h
    | ok lov =>
        rw [hlo] at h
        simp only [Bind.bind, Except.bind] at h ⊢
        cases hhi : valueAsInt hi with
        | error e => rw [hhi] at h; simp [Bind.bind, Except.bind] at h
        | ok hiv =>
            rw [hhi] at h
            simp only [Bind.bind, Except.bind] at h ⊢
            cases hm2 : valueAsInt m with
            | error e => rw [hm2] at h; simp [Bind.bind, Except.bind] at h
            | ok mv =>
                rw [hm2] at h
                simp only [Bind.bind, Except.bind] at h ⊢
                exact applySliceF_ok h
  -- .lengthOf
  · rename_i typ v0
    simp only [applyStrictOp]
    split at h
    · tuple_close h
    · split at h
      · tuple_close h
      · rename_i baseLoc
        cases hl : loadLocF σF baseLoc with
        | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
        | ok bv =>
            rw [hl] at h
            simp only [loadLocF_ok hl]
            simp only [Bind.bind, Except.bind] at h ⊢
            cases bv <;> try (simp [unsupported] at h)
            case array values => tuple_close h
      · tuple_close h
      · rename_i slice
        cases hv : validateSlice slice with
        | error e =>
            rw [hv] at h
            simp [Bind.bind, Except.bind, SeqRight.seqRight, Except.map] at h
        | ok u =>
            rw [hv] at h
            simp only [Bind.bind, Except.bind, SeqRight.seqRight, pure,
              Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, h2⟩ := h
            subst h2
            simp [hv, h1]
            rfl
      · rename_i map
        split at h <;> rename_i hbase
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h2
          simp [hbase, h1]
        · rename_i baseLoc
          cases hl : loadLocF σF baseLoc with
          | error e => rw [hl] at h; simp [Bind.bind, Except.bind] at h
          | ok bv =>
              rw [hl] at h
              simp only [Bind.bind, Except.bind] at h
              cases bv <;> try (simp [stuck] at h)
              case mapData entries =>
                try simp only [pure, Except.pure, Except.ok.injEq,
                  Prod.mk.injEq] at h
                obtain ⟨h1, h2⟩ := h
                subst h2
                simp [hbase, loadLocF_ok hl, h1, Bind.bind, Except.bind]
      · simp [stuck] at h
      · simp [unsupported] at h
  -- .capacityOf (P2R)
  · exact capacityOfArmF_ok h
  -- .funcValOf
  · simp only [applyStrictOp]; tuple_close h
  -- .minOf
  · rename_i v0 vs
    simp only [applyStrictOp]
    split at h <;> rename_i hfl
    · rw [if_pos hfl]; exact pureArm_sim h
    · rw [if_neg hfl]; exact pureArm_sim h
  -- .maxOf
  · rename_i v0 vs
    simp only [applyStrictOp]
    split at h <;> rename_i hfl
    · rw [if_pos hfl]; exact pureArm_sim h
    · rw [if_neg hfl]; exact pureArm_sim h
  -- .runeAt / .runeSizeAt (P2R)
  · exact runeAtArmF_ok h
  · exact runeSizeAtArmF_ok h
  -- .defaultValueOf
  · simp only [applyStrictOp]; exact pureArm_sim h
  -- .nilLit
  · rename_i typ
    simp only [applyStrictOp]
    split at h
    · tuple_close h
    · rename_i ty
      split at h
      · exact pureArm_sim h
      · exact pureArm_sim h
      · exact pureArm_sim h
      · tuple_close h
      · simp [unsupported] at h
      · simp [stuck] at h
  -- .runesFromString / .stringFromRuneSlice (P2R)
  · exact runesFromStringArmF_ok h
  · exact stringFromRuneSliceArmF_ok h
  -- catch-all
  · simp [stuck] at h

end GoLean.FastEval
