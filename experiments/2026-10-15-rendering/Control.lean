import GoLean.GoCore.Multi
open Std GoLean GoLean.GoCore GoLean.GoCore.Machine
namespace RendererControl
local instance : Inhabited GoValue := ⟨.unit⟩
local instance : Inhabited Loc := ⟨.base ⟨0⟩⟩
local instance : Inhabited SliceValue := ⟨⟨none, 0, 0, 0⟩⟩
local instance : Inhabited MapValue := ⟨⟨none⟩⟩
local instance : Inhabited ChanValue := ⟨⟨none⟩⟩
local instance : Inhabited GoString := ⟨GoString.empty⟩

def tyConstructors : List Ty := [
  .bool ,
  .int default,
  .float default,
  .string ,
  .array default default,
  .slice default,
  .map default default,
  .chan default default,
  .pointer default,
  .funcType default default default,
  .interface default,
  .defined default,
  .unsupported default,
  .sync default
]

def govalueConstructors : List GoValue := [
  .unit ,
  .bool default,
  .int default default,
  .float default default,
  .string default,
  .addr default,
  .nil ,
  .interface default default,
  .struct default default,
  .array default,
  .slice default,
  .map default,
  .chan default,
  .funcVal default default,
  .syncData default
]

def exprConstructors : List Expr := [
  .var default,
  .nil default,
  .intLit default default,
  .floatLit default default default,
  .stringLit default,
  .boolLit default,
  .convert default default,
  .bytesFromString default,
  .stringFromByteSlice default,
  .stringFromRune default,
  .add default default,
  .sub default default,
  .mul default default,
  .div default default,
  .mod default default,
  .shiftLeft default default,
  .shiftRight default default,
  .bitAnd default default,
  .bitOr default default,
  .bitXor default default,
  .bitClear default default,
  .bitNeg default,
  .neg default,
  .eqCmp default default default,
  .neqCmp default default default,
  .atMostCmp default default,
  .atLeastCmp default default,
  .lessCmp default default,
  .greaterCmp default default,
  .and default default,
  .or default default,
  .not default,
  .ref default,
  .funcVal default default,
  .global default,
  .deref default default,
  .addrOfDeref default,
  .structLit default default,
  .fieldGet default default default,
  .fieldAddr default default default,
  .arrayLit default default default,
  .defaultValue default,
  .toInterface default default default,
  .typeAssert default default default,
  .indexGet default default,
  .indexAddr default default,
  .mapGet default default default default,
  .slice default default default default,
  .length default default,
  .capacity default default,
  .minOf default,
  .maxOf default,
  .runeAt default default,
  .runeSizeAt default default,
  .runesFromString default,
  .stringFromRuneSlice default,
  .floatBits default default,
  .recoverCall ,
  .unsupported default
]

def nestedTy : Ty := .funcType [.map (.array 7 (.pointer .string)) (.chan .recv .bool),
  .funcType [] [.sync .rwmutex] true] [.interface ⟨"q\n\"雪"⟩, .unsupported "bad\t"] false

def interior : Loc := .index (.field (.base ⟨17⟩) ⟨"T9"⟩ "q\"\n雪") (-4)
def nestedValue : GoValue := .funcVal ⟨"f\n雪"⟩ [
  .interface nestedTy (.struct ⟨"T99"⟩ #[("a\n", .array #[.nil, .string ⟨#[0,255,192,128]⟩]),
    ("b", .addr interior)]),
  .slice ⟨some interior, 100, 9, 2⟩, .map ⟨some interior⟩, .chan ⟨some interior⟩,
  .int (-123) (.unbounded "bad\t"), .float (2^100) .float32,
  .syncData (.waitGroup (-5) 7)]
def nestedExpr : Expr := .slice (.arrayLit 1 nestedTy #[(3, .funcVal ⟨"f"⟩ #[.var 9]),
    (-4, .stringLit ⟨#[255,0]⟩)]) (.minOf #[]) (.maxOf #[.recoverCall, .unsupported "\n雪"])
    (some (.convert nestedTy (.structLit nestedTy #[.nil (some nestedTy)])))

def emitFormats [Repr α] (tag : String) (xs : List α) : IO Unit := do
  for (v,i) in xs.zipIdx do
    for prec in [0, 1, 1023, 1024, 1025] do
      for width in [0, 1, 8, 40, 120] do
        for indent in [0, 3] do
          for column in [0, 7] do
            IO.println s!"{tag}/{i}/{prec}/{width}/{indent}/{column}: {repr ((reprPrec v prec).pretty width indent column)}"

/-- Compare the resulting store, remaining tape, label and exact error.
The Config is intentionally outside this finite control projection. -/
def stepResult : Except Stop (Config × Store × Choices × StepLabel) → String
  | .error e => s!"error {repr e}"
  | .ok (_, s, ch, l) => s!"ok {repr s} {repr ch} {repr l.trace} {repr l.picks} {repr l.out}"

def main : IO Unit := do
  emitFormats "Ty" (tyConstructors ++ [nestedTy, .funcType [] [] false])
  emitFormats "GoValue" (govalueConstructors ++ [nestedValue, .array #[], .struct ⟨"T7"⟩ #[]])
  emitFormats "Expr" (exprConstructors ++ [nestedExpr, .slice (.var 0) (.var 1) (.var 2) none])
  for ty in tyConstructors ++ [nestedTy] do
    IO.println s!"checkedDynamicTy: {repr (checkedDynamicTy ty)}"
  let ctx := ProgramCtx.ofTables
  let s : Store := {}
  for v in govalueConstructors ++ [nestedValue] do
    IO.println s!"valueEq/bool: {repr (valueEq ctx .bool v nestedValue)}"
    IO.println s!"valueEq/sync: {repr (valueEq ctx (.sync .rwmutex) v nestedValue)}"
    IO.println s!"preprint: {repr (preprintDispatch ctx s ⟨v, false, .pending ⟨"String", ""⟩, false⟩)}"
  for e in exprConstructors ++ [nestedExpr] do
    IO.println s!"unseqAtom: {repr (unseqAtom ctx [] s e)}"
  for tape in [[], [0], [1,9,0]] do
    IO.println s!"step/eval: {stepResult (stepFn ctx s (.evalE (.add (.boolLit true) (.stringLit ⟨#[255]⟩)) [] .stop) tape)}"
    IO.println s!"step/preprint: {stepResult (stepFn ctx s (.next (.preprintK [] ⟨nestedValue, false, .pending ⟨"String", ""⟩, false⟩ [] .stop)) tape)}"
end RendererControl

def main := RendererControl.main
