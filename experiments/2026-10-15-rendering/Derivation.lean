import GoLean.GoCore.Syntax

/-! Checked equations against the old toolchain-generated constructor bodies.
The bodies below are extracted from the deriving trace at 82353580814b66399cdc472a4c4edf9044d0c097.
Recursive calls are parameters: no equality to an old opaque constant is asserted. -/
open Std GoLean GoLean.GoCore
namespace GoLean.RendererDerivation

def tyStep (rec : Ty → Nat → Format) (x : @GoLean.GoCore.Ty) (prec : Nat) : Format :=
  let _ : Repr (@GoLean.GoCore.Ty) := ⟨rec⟩;
  match x with
  | @GoLean.GoCore.Ty.bool =>
    Repr.addAppParen
      (Format.group (Format.nest (if prec ≥ max_prec then 1 else 2) (Format.text "GoLean.GoCore.Ty.bool")))
      prec
  | @GoLean.GoCore.Ty.int a =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.int" ++ Format.line ++ reprArg a)))
      prec
  | @GoLean.GoCore.Ty.float a1 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.float" ++ Format.line ++ reprArg a1)))
      prec
  | @GoLean.GoCore.Ty.string =>
    Repr.addAppParen
      (Format.group (Format.nest (if prec ≥ max_prec then 1 else 2) (Format.text "GoLean.GoCore.Ty.string")))
      prec
  | @GoLean.GoCore.Ty.array a2 a3 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.array" ++ Format.line ++ reprArg a2 ++ Format.line ++
            rec a3 max_prec)))
      prec
  | @GoLean.GoCore.Ty.slice a4 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.slice" ++ Format.line ++ rec a4 max_prec)))
      prec
  | @GoLean.GoCore.Ty.map a5 a6 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.map" ++ Format.line ++ rec a5 max_prec ++ Format.line ++
            rec a6 max_prec)))
      prec
  | @GoLean.GoCore.Ty.chan a7 a8 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.chan" ++ Format.line ++ reprArg a7 ++ Format.line ++
            rec a8 max_prec)))
      prec
  | @GoLean.GoCore.Ty.pointer a9 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.pointer" ++ Format.line ++ rec a9 max_prec)))
      prec
  | @GoLean.GoCore.Ty.funcType a10 a11 a12 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.funcType" ++ Format.line ++ reprArg a10 ++ Format.line ++
                reprArg a11 ++
              Format.line ++
            reprArg a12)))
      prec
  | @GoLean.GoCore.Ty.interface a13 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.interface" ++ Format.line ++ reprArg a13)))
      prec
  | @GoLean.GoCore.Ty.defined a14 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.defined" ++ Format.line ++ reprArg a14)))
      prec
  | @GoLean.GoCore.Ty.unsupported a15 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.unsupported" ++ Format.line ++ reprArg a15)))
      prec
  | @GoLean.GoCore.Ty.sync a16 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Ty.sync" ++ Format.line ++ reprArg a16)))
      prec

def govalueStep (rec : GoValue → Nat → Format) (x : @GoLean.GoValue) (prec : Nat) : Format :=
  let _ : Repr (@GoLean.GoValue) := ⟨rec⟩;
  match x with
  | @GoLean.GoValue.unit =>
    Repr.addAppParen
      (Format.group (Format.nest (if prec ≥ max_prec then 1 else 2) (Format.text "GoLean.GoValue.unit")))
      prec
  | @GoLean.GoValue.bool a =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.bool" ++ Format.line ++ reprArg a)))
      prec
  | @GoLean.GoValue.int a1 a2 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.int" ++ Format.line ++ reprArg a1 ++ Format.line ++ reprArg a2)))
      prec
  | @GoLean.GoValue.float a3 a4 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.float" ++ Format.line ++ reprArg a3 ++ Format.line ++ reprArg a4)))
      prec
  | @GoLean.GoValue.string a5 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.string" ++ Format.line ++ reprArg a5)))
      prec
  | @GoLean.GoValue.addr a6 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.addr" ++ Format.line ++ reprArg a6)))
      prec
  | @GoLean.GoValue.nil =>
    Repr.addAppParen
      (Format.group (Format.nest (if prec ≥ max_prec then 1 else 2) (Format.text "GoLean.GoValue.nil")))
      prec
  | @GoLean.GoValue.interface a7 a8 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.interface" ++ Format.line ++ reprArg a7 ++ Format.line ++
            rec a8 max_prec)))
      prec
  | @GoLean.GoValue.struct a9 a10 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.struct" ++ Format.line ++ reprArg a9 ++ Format.line ++
            reprArg a10)))
      prec
  | @GoLean.GoValue.array a11 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.array" ++ Format.line ++ reprArg a11)))
      prec
  | @GoLean.GoValue.slice a12 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.slice" ++ Format.line ++ reprArg a12)))
      prec
  | @GoLean.GoValue.map a13 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.map" ++ Format.line ++ reprArg a13)))
      prec
  | @GoLean.GoValue.chan a14 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.chan" ++ Format.line ++ reprArg a14)))
      prec
  | @GoLean.GoValue.funcVal a15 a16 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.funcVal" ++ Format.line ++ reprArg a15 ++ Format.line ++
            reprArg a16)))
      prec
  | @GoLean.GoValue.syncData a17 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoValue.syncData" ++ Format.line ++ reprArg a17)))
      prec

def exprStep (rec : Expr → Nat → Format) (x : @GoLean.GoCore.Expr) (prec : Nat) : Format :=
  let _ : Repr (@GoLean.GoCore.Expr) := ⟨rec⟩;
  match x with
  | @GoLean.GoCore.Expr.var a =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.var" ++ Format.line ++ reprArg a)))
      prec
  | @GoLean.GoCore.Expr.nil a1 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.nil" ++ Format.line ++ reprArg a1)))
      prec
  | @GoLean.GoCore.Expr.intLit a2 a3 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.intLit" ++ Format.line ++ reprArg a2 ++ Format.line ++
            reprArg a3)))
      prec
  | @GoLean.GoCore.Expr.floatLit a4 a5 a6 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.floatLit" ++ Format.line ++ reprArg a4 ++ Format.line ++
                reprArg a5 ++
              Format.line ++
            reprArg a6)))
      prec
  | @GoLean.GoCore.Expr.stringLit a7 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.stringLit" ++ Format.line ++ reprArg a7)))
      prec
  | @GoLean.GoCore.Expr.boolLit a8 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.boolLit" ++ Format.line ++ reprArg a8)))
      prec
  | @GoLean.GoCore.Expr.convert a9 a10 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.convert" ++ Format.line ++ reprArg a9 ++ Format.line ++
            rec a10 max_prec)))
      prec
  | @GoLean.GoCore.Expr.bytesFromString a11 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.bytesFromString" ++ Format.line ++
            rec a11 max_prec)))
      prec
  | @GoLean.GoCore.Expr.stringFromByteSlice a12 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.stringFromByteSlice" ++ Format.line ++
            rec a12 max_prec)))
      prec
  | @GoLean.GoCore.Expr.stringFromRune a13 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.stringFromRune" ++ Format.line ++ rec a13 max_prec)))
      prec
  | @GoLean.GoCore.Expr.add a14 a15 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.add" ++ Format.line ++ rec a14 max_prec ++
              Format.line ++
            rec a15 max_prec)))
      prec
  | @GoLean.GoCore.Expr.sub a16 a17 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.sub" ++ Format.line ++ rec a16 max_prec ++
              Format.line ++
            rec a17 max_prec)))
      prec
  | @GoLean.GoCore.Expr.mul a18 a19 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.mul" ++ Format.line ++ rec a18 max_prec ++
              Format.line ++
            rec a19 max_prec)))
      prec
  | @GoLean.GoCore.Expr.div a20 a21 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.div" ++ Format.line ++ rec a20 max_prec ++
              Format.line ++
            rec a21 max_prec)))
      prec
  | @GoLean.GoCore.Expr.mod a22 a23 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.mod" ++ Format.line ++ rec a22 max_prec ++
              Format.line ++
            rec a23 max_prec)))
      prec
  | @GoLean.GoCore.Expr.shiftLeft a24 a25 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.shiftLeft" ++ Format.line ++ rec a24 max_prec ++
              Format.line ++
            rec a25 max_prec)))
      prec
  | @GoLean.GoCore.Expr.shiftRight a26 a27 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.shiftRight" ++ Format.line ++ rec a26 max_prec ++
              Format.line ++
            rec a27 max_prec)))
      prec
  | @GoLean.GoCore.Expr.bitAnd a28 a29 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.bitAnd" ++ Format.line ++ rec a28 max_prec ++
              Format.line ++
            rec a29 max_prec)))
      prec
  | @GoLean.GoCore.Expr.bitOr a30 a31 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.bitOr" ++ Format.line ++ rec a30 max_prec ++
              Format.line ++
            rec a31 max_prec)))
      prec
  | @GoLean.GoCore.Expr.bitXor a32 a33 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.bitXor" ++ Format.line ++ rec a32 max_prec ++
              Format.line ++
            rec a33 max_prec)))
      prec
  | @GoLean.GoCore.Expr.bitClear a34 a35 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.bitClear" ++ Format.line ++ rec a34 max_prec ++
              Format.line ++
            rec a35 max_prec)))
      prec
  | @GoLean.GoCore.Expr.bitNeg a36 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.bitNeg" ++ Format.line ++ rec a36 max_prec)))
      prec
  | @GoLean.GoCore.Expr.neg a37 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.neg" ++ Format.line ++ rec a37 max_prec)))
      prec
  | @GoLean.GoCore.Expr.eqCmp a38 a39 a40 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.eqCmp" ++ Format.line ++ reprArg a38 ++ Format.line ++
                rec a39 max_prec ++
              Format.line ++
            rec a40 max_prec)))
      prec
  | @GoLean.GoCore.Expr.neqCmp a41 a42 a43 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.neqCmp" ++ Format.line ++ reprArg a41 ++ Format.line ++
                rec a42 max_prec ++
              Format.line ++
            rec a43 max_prec)))
      prec
  | @GoLean.GoCore.Expr.atMostCmp a44 a45 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.atMostCmp" ++ Format.line ++ rec a44 max_prec ++
              Format.line ++
            rec a45 max_prec)))
      prec
  | @GoLean.GoCore.Expr.atLeastCmp a46 a47 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.atLeastCmp" ++ Format.line ++ rec a46 max_prec ++
              Format.line ++
            rec a47 max_prec)))
      prec
  | @GoLean.GoCore.Expr.lessCmp a48 a49 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.lessCmp" ++ Format.line ++ rec a48 max_prec ++
              Format.line ++
            rec a49 max_prec)))
      prec
  | @GoLean.GoCore.Expr.greaterCmp a50 a51 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.greaterCmp" ++ Format.line ++ rec a50 max_prec ++
              Format.line ++
            rec a51 max_prec)))
      prec
  | @GoLean.GoCore.Expr.and a52 a53 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.and" ++ Format.line ++ rec a52 max_prec ++
              Format.line ++
            rec a53 max_prec)))
      prec
  | @GoLean.GoCore.Expr.or a54 a55 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.or" ++ Format.line ++ rec a54 max_prec ++
              Format.line ++
            rec a55 max_prec)))
      prec
  | @GoLean.GoCore.Expr.not a56 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.not" ++ Format.line ++ rec a56 max_prec)))
      prec
  | @GoLean.GoCore.Expr.ref a57 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.ref" ++ Format.line ++ reprArg a57)))
      prec
  | @GoLean.GoCore.Expr.funcVal a58 a59 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.funcVal" ++ Format.line ++ reprArg a58 ++ Format.line ++
            reprArg a59)))
      prec
  | @GoLean.GoCore.Expr.global a60 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.global" ++ Format.line ++ reprArg a60)))
      prec
  | @GoLean.GoCore.Expr.deref a61 a62 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.deref" ++ Format.line ++ rec a61 max_prec ++
              Format.line ++
            reprArg a62)))
      prec
  | @GoLean.GoCore.Expr.addrOfDeref a63 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.addrOfDeref" ++ Format.line ++ rec a63 max_prec)))
      prec
  | @GoLean.GoCore.Expr.structLit a64 a65 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.structLit" ++ Format.line ++ reprArg a64 ++ Format.line ++
            reprArg a65)))
      prec
  | @GoLean.GoCore.Expr.fieldGet a66 a67 a68 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.fieldGet" ++ Format.line ++ rec a66 max_prec ++
                  Format.line ++
                reprArg a67 ++
              Format.line ++
            reprArg a68)))
      prec
  | @GoLean.GoCore.Expr.fieldAddr a69 a70 a71 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.fieldAddr" ++ Format.line ++ rec a69 max_prec ++
                  Format.line ++
                reprArg a70 ++
              Format.line ++
            reprArg a71)))
      prec
  | @GoLean.GoCore.Expr.arrayLit a72 a73 a74 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.arrayLit" ++ Format.line ++ reprArg a72 ++ Format.line ++
                reprArg a73 ++
              Format.line ++
            reprArg a74)))
      prec
  | @GoLean.GoCore.Expr.defaultValue a75 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.defaultValue" ++ Format.line ++ reprArg a75)))
      prec
  | @GoLean.GoCore.Expr.toInterface a76 a77 a78 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.toInterface" ++ Format.line ++ reprArg a76 ++ Format.line ++
                reprArg a77 ++
              Format.line ++
            rec a78 max_prec)))
      prec
  | @GoLean.GoCore.Expr.typeAssert a79 a80 a81 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.typeAssert" ++ Format.line ++ rec a79 max_prec ++
                  Format.line ++
                reprArg a80 ++
              Format.line ++
            reprArg a81)))
      prec
  | @GoLean.GoCore.Expr.indexGet a82 a83 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.indexGet" ++ Format.line ++ rec a82 max_prec ++
              Format.line ++
            rec a83 max_prec)))
      prec
  | @GoLean.GoCore.Expr.indexAddr a84 a85 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.indexAddr" ++ Format.line ++ rec a84 max_prec ++
              Format.line ++
            rec a85 max_prec)))
      prec
  | @GoLean.GoCore.Expr.mapGet a86 a87 a88 a89 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.mapGet" ++ Format.line ++ rec a86 max_prec ++
                      Format.line ++
                    rec a87 max_prec ++
                  Format.line ++
                reprArg a88 ++
              Format.line ++
            reprArg a89)))
      prec
  | @GoLean.GoCore.Expr.slice a90 a91 a92 a93 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.slice" ++ Format.line ++ rec a90 max_prec ++
                      Format.line ++
                    rec a91 max_prec ++
                  Format.line ++
                rec a92 max_prec ++
              Format.line ++
            reprArg a93)))
      prec
  | @GoLean.GoCore.Expr.length a94 a95 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.length" ++ Format.line ++ rec a94 max_prec ++
              Format.line ++
            reprArg a95)))
      prec
  | @GoLean.GoCore.Expr.capacity a96 a97 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.capacity" ++ Format.line ++ rec a96 max_prec ++
              Format.line ++
            reprArg a97)))
      prec
  | @GoLean.GoCore.Expr.minOf a98 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.minOf" ++ Format.line ++ reprArg a98)))
      prec
  | @GoLean.GoCore.Expr.maxOf a99 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.maxOf" ++ Format.line ++ reprArg a99)))
      prec
  | @GoLean.GoCore.Expr.runeAt a100 a101 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.runeAt" ++ Format.line ++ rec a100 max_prec ++
              Format.line ++
            rec a101 max_prec)))
      prec
  | @GoLean.GoCore.Expr.runeSizeAt a102 a103 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.runeSizeAt" ++ Format.line ++ rec a102 max_prec ++
              Format.line ++
            rec a103 max_prec)))
      prec
  | @GoLean.GoCore.Expr.runesFromString a104 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.runesFromString" ++ Format.line ++
            rec a104 max_prec)))
      prec
  | @GoLean.GoCore.Expr.stringFromRuneSlice a105 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.stringFromRuneSlice" ++ Format.line ++
            rec a105 max_prec)))
      prec
  | @GoLean.GoCore.Expr.floatBits a106 a107 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.floatBits" ++ Format.line ++ reprArg a106 ++ Format.line ++
            rec a107 max_prec)))
      prec
  | @GoLean.GoCore.Expr.recoverCall =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2) (Format.text "GoLean.GoCore.Expr.recoverCall")))
      prec
  | @GoLean.GoCore.Expr.unsupported a108 =>
    Repr.addAppParen
      (Format.group
        (Format.nest (if prec ≥ max_prec then 1 else 2)
          (Format.text "GoLean.GoCore.Expr.unsupported" ++ Format.line ++ reprArg a108)))
      prec



theorem ty_items (xs : List Ty) :
    Ty.renderItems xs = xs.map repr := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [Ty.renderItems, List.map_cons, ih]; rfl

theorem ty_equation (v : Ty) (prec : Nat) :
    Ty.render v prec = tyStep Ty.render v prec := by
  cases v <;> simp only [Ty.render, tyStep, Rendering.app,
    List.foldl_cons, List.foldl_nil, ty_items, Rendering.list_repr (prec := max_prec)]
  all_goals rfl

theorem govalue_items (xs : List GoValue) :
    GoValue.renderItems xs = xs.map repr := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [GoValue.renderItems, List.map_cons, ih]; rfl

theorem govalue_fields (xs : List (String × GoValue)) :
    GoValue.renderFields xs = xs.map repr := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases a with ⟨k, v⟩
    simp only [GoValue.renderFields, List.map_cons, ih]
    rfl

theorem govalue_equation (v : GoValue) (prec : Nat) :
    GoValue.render v prec = govalueStep GoValue.render v prec := by
  cases v <;> simp only [GoValue.render, govalueStep, Rendering.app,
    List.foldl_cons, List.foldl_nil, govalue_items, govalue_fields, Rendering.list_repr (prec := max_prec), Rendering.array_repr]
  all_goals rfl

theorem expr_items (xs : List Expr) :
    Expr.renderItems xs = xs.map repr := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [Expr.renderItems, List.map_cons, ih]; rfl

theorem expr_fields (xs : List (Int × Expr)) :
    Expr.renderFields xs = xs.map repr := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases a with ⟨k, v⟩
    simp only [Expr.renderFields, List.map_cons, ih]
    rfl

theorem expr_option (v : Option Expr) (prec : Nat) :
    Rendering.option (Expr.renderOption v) prec = reprPrec v prec := by
  cases v <;> rfl

theorem expr_equation (v : Expr) (prec : Nat) :
    Expr.render v prec = exprStep Expr.render v prec := by
  cases v <;> simp only [Expr.render, exprStep, Rendering.app,
    List.foldl_cons, List.foldl_nil, expr_items, expr_fields, Rendering.array_repr, expr_option]
  all_goals rfl

end GoLean.RendererDerivation
