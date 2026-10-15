import GoLean.GoCore.Platform

/-! Formatting combinators matching the pinned deriving-Repr algorithm.
These build Format trees; width-dependent layout and string escaping remain
the pinned toolchain's ordinary Format/Repr operations. -/
namespace GoLean.Rendering
open Std

def app (name : String) (args : List Format) (prec : Nat) : Format :=
  Repr.addAppParen
    (Format.group (Format.nest (if prec >= max_prec then 1 else 2)
      (args.foldl (fun out arg => out ++ Format.line ++ arg) (Format.text name)))) prec

def list : List Format → Format
  | [] => "[]"
  | fs => Format.bracket "[" (Format.joinSep fs ("," ++ Format.line)) "]"

def array : List Format → Format
  | [] => "#[]"
  | fs => Format.bracketFill "#[" (Format.joinSep fs ("," ++ Format.line)) "]"

def pair (a b : Format) : Format :=
  Format.bracket "(" (Format.joinSep [a,b] ("," ++ Format.line)) ")"

def option (f : Option Format) (prec : Nat) : Format :=
  match f with
  | none => "none"
  | some a => Repr.addAppParen ("some " ++ a) prec

theorem joinSep_map (f : α → Format) (xs : List α) (sep : Format) :
    Format.joinSep (xs.map f) sep = @Format.joinSep α ⟨f⟩ xs sep := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b xs => simp only [Format.joinSep, List.map_cons, List.foldl_cons, List.foldl_map]; rfl

theorem list_repr [Repr α] (xs : List α) (prec : Nat) :
    list (xs.map repr) = List.repr xs prec := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    exact congrArg (fun f => Format.bracket "[" f "]")
      (joinSep_map repr (a :: xs) ("," ++ Format.line))

theorem array_repr [Repr α] (xs : Array α) :
    array (xs.toList.map repr) = Array.repr xs := by
  cases xs with
  | mk xs =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      exact congrArg (fun f => Format.bracketFill "#[" f "]")
        (joinSep_map repr (a :: xs) ("," ++ Format.line))

theorem pair_repr [Repr α] [Repr β] (a : α) (b : β) :
    pair (repr a) (repr b) = @Prod.repr α β _ (inferInstanceAs (ReprTuple β)) (a,b) 0 := rfl

end GoLean.Rendering
