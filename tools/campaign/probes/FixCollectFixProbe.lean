import GoLeanProofs.Frame.ChoiceCanon
open GoLean GoLean.GoCore GoLean.ChoiceErase

-- Addresses: A=0 (array of 2: slice->B(0,1), slice->C(0,2)),
-- B=1 (array of 1: slice->A(0,2)), C=2 (array of 2: int 0, addr D),
-- D=3 (zero array; length 3 vs 5 in the sibling).
def mkσ (dlen : Nat) : ExecState :=
  { heap :=
      [ (.base ⟨0⟩, { value := .array #[
            .slice ⟨some (.base ⟨1⟩), 0, 1, 1⟩,
            .slice ⟨some (.base ⟨2⟩), 0, 2, 2⟩] }),
        (.base ⟨1⟩, { value := .array #[
            .slice ⟨some (.base ⟨0⟩), 0, 2, 2⟩] }),
        (.base ⟨2⟩, { value := .array #[
            .int 0 .int, .addr (.base ⟨3⟩)] }),
        (.base ⟨3⟩, { value := .array (Array.replicate dlen (.int 0 .int)) }) ],
    nextAddr := 4 }

def wroots : List GoValue :=
  [ .slice ⟨some (.base ⟨2⟩), 0, 1, 1⟩,
    .slice ⟨some (.base ⟨0⟩), 0, 1, 1⟩ ]

def cellArrLen : CCell → Option Nat
  | ⟨_, .arr es⟩ => some es.length
  | _ => none

#eval toString (repr (canonState (mkσ 3) wroots))
#eval toString (repr (canonState (mkσ 5) wroots))
#eval ((canonState (mkσ 3) wroots).cells.map cellArrLen)
#eval ((canonState (mkσ 5) wroots).cells.map cellArrLen)
#eval ((canonState (mkσ 3) wroots).flags, (canonState (mkσ 5) wroots).flags)
-- the bug check: are the two forms' cell projections EQUAL though D differs?
#eval decide ((canonState (mkσ 3) wroots).cells.map cellArrLen
            = (canonState (mkσ 5) wroots).cells.map cellArrLen)
