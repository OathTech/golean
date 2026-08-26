import GoLeanProofs.Frame.ChoiceCanon

/-! # seedCForm — GENERATED (SP1; generator
`artifacts/probe/SeedCFormGen.lean` — DO NOT EDIT BY HAND).

The PINNED masked canonical form of the seed representative
(`canonStateM twinLatMask seedσ seedRoots`): 207 live cells,
flags []. Trust: `SeedPin.seed_cform_pin` kernel-recomputes the
canonicalization against this literal on every build; the
witness (`SeedWitness.seedVar_cform_pin`) lands the VARIANT
run's canonicalization on the SAME literal — equivalence by
shared pin (the tree-propagation route: never compare two
computed forms head-on). -/

namespace GoLean.RaftSeam

open GoLean.ChoiceErase

set_option maxRecDepth 8000000

def seedCFormRoots : List CVal :=
  [GoLean.ChoiceErase.CVal.ref 0,
 GoLean.ChoiceErase.CVal.ref 1,
 GoLean.ChoiceErase.CVal.ref 2,
 GoLean.ChoiceErase.CVal.ref 3,
 GoLean.ChoiceErase.CVal.ref 4,
 GoLean.ChoiceErase.CVal.ref 5,
 GoLean.ChoiceErase.CVal.ref 6,
 GoLean.ChoiceErase.CVal.ref 7,
 GoLean.ChoiceErase.CVal.ref 8,
 GoLean.ChoiceErase.CVal.ref 9,
 GoLean.ChoiceErase.CVal.ref 10,
 GoLean.ChoiceErase.CVal.ref 11,
 GoLean.ChoiceErase.CVal.ref 12,
 GoLean.ChoiceErase.CVal.ref 13,
 GoLean.ChoiceErase.CVal.ref 14,
 GoLean.ChoiceErase.CVal.ref 15,
 GoLean.ChoiceErase.CVal.ref 16,
 GoLean.ChoiceErase.CVal.ref 17,
 GoLean.ChoiceErase.CVal.ref 18,
 GoLean.ChoiceErase.CVal.ref 19,
 GoLean.ChoiceErase.CVal.ref 20,
 GoLean.ChoiceErase.CVal.ref 21,
 GoLean.ChoiceErase.CVal.ref 22,
 GoLean.ChoiceErase.CVal.ref 23,
 GoLean.ChoiceErase.CVal.ref 24,
 GoLean.ChoiceErase.CVal.ref 25,
 GoLean.ChoiceErase.CVal.ref 26,
 GoLean.ChoiceErase.CVal.ref 27,
 GoLean.ChoiceErase.CVal.ref 28,
 GoLean.ChoiceErase.CVal.ref 29,
 GoLean.ChoiceErase.CVal.ref 30,
 GoLean.ChoiceErase.CVal.ref 31,
 GoLean.ChoiceErase.CVal.ref 32,
 GoLean.ChoiceErase.CVal.ref 33,
 GoLean.ChoiceErase.CVal.ref 34,
 GoLean.ChoiceErase.CVal.ref 35,
 GoLean.ChoiceErase.CVal.ref 36,
 GoLean.ChoiceErase.CVal.ref 37,
 GoLean.ChoiceErase.CVal.ref 38,
 GoLean.ChoiceErase.CVal.ref 39,
 GoLean.ChoiceErase.CVal.ref 40,
 GoLean.ChoiceErase.CVal.ref 41,
 GoLean.ChoiceErase.CVal.ref 42,
 GoLean.ChoiceErase.CVal.ref 43,
 GoLean.ChoiceErase.CVal.ref 44,
 GoLean.ChoiceErase.CVal.ref 45,
 GoLean.ChoiceErase.CVal.ref 46,
 GoLean.ChoiceErase.CVal.ref 47,
 GoLean.ChoiceErase.CVal.ref 48,
 GoLean.ChoiceErase.CVal.ref 49,
 GoLean.ChoiceErase.CVal.ref 50,
 GoLean.ChoiceErase.CVal.ref 51,
 GoLean.ChoiceErase.CVal.ref 52,
 GoLean.ChoiceErase.CVal.ref 53,
 GoLean.ChoiceErase.CVal.ref 54,
 GoLean.ChoiceErase.CVal.ref 55,
 GoLean.ChoiceErase.CVal.ref 56,
 GoLean.ChoiceErase.CVal.ref 57,
 GoLean.ChoiceErase.CVal.ref 58,
 GoLean.ChoiceErase.CVal.ref 59,
 GoLean.ChoiceErase.CVal.ref 60,
 GoLean.ChoiceErase.CVal.ref 61,
 GoLean.ChoiceErase.CVal.ref 62,
 GoLean.ChoiceErase.CVal.ref 63,
 GoLean.ChoiceErase.CVal.ref 64,
 GoLean.ChoiceErase.CVal.ref 65,
 GoLean.ChoiceErase.CVal.ref 66,
 GoLean.ChoiceErase.CVal.ref 67,
 GoLean.ChoiceErase.CVal.ref 68,
 GoLean.ChoiceErase.CVal.ref 69,
 GoLean.ChoiceErase.CVal.ref 70,
 GoLean.ChoiceErase.CVal.ref 71,
 GoLean.ChoiceErase.CVal.ref 72,
 GoLean.ChoiceErase.CVal.ref 73,
 GoLean.ChoiceErase.CVal.ref 74,
 GoLean.ChoiceErase.CVal.ref 75,
 GoLean.ChoiceErase.CVal.ref 76,
 GoLean.ChoiceErase.CVal.ref 77,
 GoLean.ChoiceErase.CVal.ref 78,
 GoLean.ChoiceErase.CVal.ref 79,
 GoLean.ChoiceErase.CVal.ref 80,
 GoLean.ChoiceErase.CVal.ref 81,
 GoLean.ChoiceErase.CVal.ref 82,
 GoLean.ChoiceErase.CVal.ref 83,
 GoLean.ChoiceErase.CVal.ref 84,
 GoLean.ChoiceErase.CVal.ref 85,
 GoLean.ChoiceErase.CVal.ref 86,
 GoLean.ChoiceErase.CVal.ref 87,
 GoLean.ChoiceErase.CVal.ref 88,
 GoLean.ChoiceErase.CVal.ref 89,
 GoLean.ChoiceErase.CVal.ref 90,
 GoLean.ChoiceErase.CVal.ref 91,
 GoLean.ChoiceErase.CVal.ref 92,
 GoLean.ChoiceErase.CVal.ref 93,
 GoLean.ChoiceErase.CVal.ref 94,
 GoLean.ChoiceErase.CVal.ref 95,
 GoLean.ChoiceErase.CVal.ref 96,
 GoLean.ChoiceErase.CVal.ref 97,
 GoLean.ChoiceErase.CVal.ref 98,
 GoLean.ChoiceErase.CVal.ref 99,
 GoLean.ChoiceErase.CVal.ref 100,
 GoLean.ChoiceErase.CVal.ref 101,
 GoLean.ChoiceErase.CVal.ref 102,
 GoLean.ChoiceErase.CVal.ref 103]

def seedCFormCells : List CCell :=
  [⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint8))),
 GoLean.ChoiceErase.CVal.arr
  [GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint8),
   GoLean.ChoiceErase.CVal.int 11 (GoLean.GoCore.IntKind.uint8),
   GoLean.ChoiceErase.CVal.int 19 (GoLean.GoCore.IntKind.uint8),
   GoLean.ChoiceErase.CVal.int 26 (GoLean.GoCore.IntKind.uint8)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 34)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)) (GoLean.GoCore.Ty.string)),
 GoLean.ChoiceErase.CVal.mp (some 36)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.string) (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))),
 GoLean.ChoiceErase.CVal.mp (some 38)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)) (GoLean.GoCore.Ty.string)),
 GoLean.ChoiceErase.CVal.mp (some 40)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.string) (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))),
 GoLean.ChoiceErase.CVal.mp (some 42)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)) (GoLean.GoCore.Ty.string)),
 GoLean.ChoiceErase.CVal.mp (some 44)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.string) (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))),
 GoLean.ChoiceErase.CVal.mp (some 46)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)) (GoLean.GoCore.Ty.string)),
 GoLean.ChoiceErase.CVal.mp (some 48)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.string) (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))),
 GoLean.ChoiceErase.CVal.mp (some 50)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.array 3 (GoLean.GoCore.Ty.string)),
 GoLean.ChoiceErase.CVal.arr
  [GoLean.ChoiceErase.CVal.str #[83, 116, 97, 116, 101, 80, 114, 111, 98, 101],
   GoLean.ChoiceErase.CVal.str #[83, 116, 97, 116, 101, 82, 101, 112, 108, 105, 99, 97, 116, 101],
   GoLean.ChoiceErase.CVal.str #[83, 116, 97, 116, 101, 83, 110, 97, 112, 115, 104, 111, 116]]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.DefaultLogger" })),
 GoLean.ChoiceErase.CVal.ref 53⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.DefaultLogger" })),
 GoLean.ChoiceErase.CVal.ref 55⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.sync (GoLean.GoCore.SyncKind.mutex)),
 GoLean.ChoiceErase.CVal.sync (GoLean.SyncPrim.mutex false)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "raft.Logger" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
  (GoLean.ChoiceErase.CVal.ref 97)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
 GoLean.ChoiceErase.CVal.ref 57⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 61)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 65)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" })),
 GoLean.ChoiceErase.CVal.ref 67⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.array 4 (GoLean.GoCore.Ty.string)),
 GoLean.ChoiceErase.CVal.arr
  [GoLean.ChoiceErase.CVal.str #[83, 116, 97, 116, 101, 70, 111, 108, 108, 111, 119, 101, 114],
   GoLean.ChoiceErase.CVal.str #[83, 116, 97, 116, 101, 67, 97, 110, 100, 105, 100, 97, 116, 101],
   GoLean.ChoiceErase.CVal.str #[83, 116, 97, 116, 101, 76, 101, 97, 100, 101, 114],
   GoLean.ChoiceErase.CVal.str
     #[83, 116, 97, 116, 101, 80, 114, 101, 67, 97, 110, 100, 105, 100, 97, 116, 101]]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 71)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 75)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 79)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 83)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 87)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 91)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 95)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool)),
 GoLean.ChoiceErase.CVal.arr
  [GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool true]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.array 23 (GoLean.GoCore.Ty.bool)),
 GoLean.ChoiceErase.CVal.arr
  [GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool true,
   GoLean.ChoiceErase.CVal.bool false,
   GoLean.ChoiceErase.CVal.bool true]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })),
 GoLean.ChoiceErase.CVal.ref 97⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.bool),
 GoLean.ChoiceErase.CVal.bool true⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.string),
 GoLean.ChoiceErase.CVal.str
  #[112, 108, 97, 105, 110, 112, 98, 58, 32, 109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 119, 105, 114,
    101, 32, 105, 110, 112, 117, 116]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 34)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.goleanShimErrorString" })),
 GoLean.ChoiceErase.CVal.ref 34⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.goleanShimErrorString" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.goleanShimErrorString" }
  [("s",
    GoLean.ChoiceErase.CVal.str
      #[112, 108, 97, 105, 110, 112, 98, 58, 32, 109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 119, 105,
        114, 101, 32, 105, 110, 112, 117, 116])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)) (GoLean.GoCore.Ty.string)),
 GoLean.ChoiceErase.CVal.mp (some 36)⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[69, 110, 116, 114, 121, 78, 111, 114, 109, 97, 108]),
   (GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[69, 110, 116, 114, 121, 67, 111, 110, 102, 67, 104, 97, 110, 103, 101]),
   (GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[69, 110, 116, 114, 121, 67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 86, 50])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.string) (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))),
 GoLean.ChoiceErase.CVal.mp (some 38)⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.str #[69, 110, 116, 114, 121, 67, 111, 110, 102, 67, 104, 97, 110, 103, 101],
    GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str
      #[69, 110, 116, 114, 121, 67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 86, 50],
    GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[69, 110, 116, 114, 121, 78, 111, 114, 109, 97, 108],
    GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int32))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)) (GoLean.GoCore.Ty.string)),
 GoLean.ChoiceErase.CVal.mp (some 40)⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 72, 117, 112]),
   (GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 66, 101, 97, 116]),
   (GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 80, 114, 111, 112]),
   (GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 65, 112, 112]),
   (GoLean.ChoiceErase.CVal.int 4 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 65, 112, 112, 82, 101, 115, 112]),
   (GoLean.ChoiceErase.CVal.int 5 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 86, 111, 116, 101]),
   (GoLean.ChoiceErase.CVal.int 6 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 86, 111, 116, 101, 82, 101, 115, 112]),
   (GoLean.ChoiceErase.CVal.int 7 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 83, 110, 97, 112]),
   (GoLean.ChoiceErase.CVal.int 8 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 72, 101, 97, 114, 116, 98, 101, 97, 116]),
   (GoLean.ChoiceErase.CVal.int 9 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 72, 101, 97, 114, 116, 98, 101, 97, 116, 82, 101, 115, 112]),
   (GoLean.ChoiceErase.CVal.int 10 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 85, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101]),
   (GoLean.ChoiceErase.CVal.int 11 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 83, 110, 97, 112, 83, 116, 97, 116, 117, 115]),
   (GoLean.ChoiceErase.CVal.int 12 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 67, 104, 101, 99, 107, 81, 117, 111, 114, 117, 109]),
   (GoLean.ChoiceErase.CVal.int 13 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[77, 115, 103, 84, 114, 97, 110, 115, 102, 101, 114, 76, 101, 97, 100, 101, 114]),
   (GoLean.ChoiceErase.CVal.int 14 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 84, 105, 109, 101, 111, 117, 116, 78, 111, 119]),
   (GoLean.ChoiceErase.CVal.int 15 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 82, 101, 97, 100, 73, 110, 100, 101, 120]),
   (GoLean.ChoiceErase.CVal.int 16 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 82, 101, 97, 100, 73, 110, 100, 101, 120, 82, 101, 115, 112]),
   (GoLean.ChoiceErase.CVal.int 17 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 80, 114, 101, 86, 111, 116, 101]),
   (GoLean.ChoiceErase.CVal.int 18 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 80, 114, 101, 86, 111, 116, 101, 82, 101, 115, 112]),
   (GoLean.ChoiceErase.CVal.int 19 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[77, 115, 103, 83, 116, 111, 114, 97, 103, 101, 65, 112, 112, 101, 110, 100]),
   (GoLean.ChoiceErase.CVal.int 20 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[77, 115, 103, 83, 116, 111, 114, 97, 103, 101, 65, 112, 112, 101, 110, 100, 82, 101, 115, 112]),
   (GoLean.ChoiceErase.CVal.int 21 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 83, 116, 111, 114, 97, 103, 101, 65, 112, 112, 108, 121]),
   (GoLean.ChoiceErase.CVal.int 22 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[77, 115, 103, 83, 116, 111, 114, 97, 103, 101, 65, 112, 112, 108, 121, 82, 101, 115, 112]),
   (GoLean.ChoiceErase.CVal.int 23 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str #[77, 115, 103, 70, 111, 114, 103, 101, 116, 76, 101, 97, 100, 101, 114])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.string) (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))),
 GoLean.ChoiceErase.CVal.mp (some 42)⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.str #[77, 115, 103, 65, 112, 112],
    GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 65, 112, 112, 82, 101, 115, 112],
    GoLean.ChoiceErase.CVal.int 4 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 66, 101, 97, 116],
    GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 67, 104, 101, 99, 107, 81, 117, 111, 114, 117, 109],
    GoLean.ChoiceErase.CVal.int 12 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 70, 111, 114, 103, 101, 116, 76, 101, 97, 100, 101, 114],
    GoLean.ChoiceErase.CVal.int 23 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 72, 101, 97, 114, 116, 98, 101, 97, 116],
    GoLean.ChoiceErase.CVal.int 8 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 72, 101, 97, 114, 116, 98, 101, 97, 116, 82, 101, 115, 112],
    GoLean.ChoiceErase.CVal.int 9 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 72, 117, 112],
    GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 80, 114, 101, 86, 111, 116, 101],
    GoLean.ChoiceErase.CVal.int 17 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 80, 114, 101, 86, 111, 116, 101, 82, 101, 115, 112],
    GoLean.ChoiceErase.CVal.int 18 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 80, 114, 111, 112],
    GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 82, 101, 97, 100, 73, 110, 100, 101, 120],
    GoLean.ChoiceErase.CVal.int 15 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 82, 101, 97, 100, 73, 110, 100, 101, 120, 82, 101, 115, 112],
    GoLean.ChoiceErase.CVal.int 16 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 83, 110, 97, 112],
    GoLean.ChoiceErase.CVal.int 7 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 83, 110, 97, 112, 83, 116, 97, 116, 117, 115],
    GoLean.ChoiceErase.CVal.int 11 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 83, 116, 111, 114, 97, 103, 101, 65, 112, 112, 101, 110, 100],
    GoLean.ChoiceErase.CVal.int 19 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str
      #[77, 115, 103, 83, 116, 111, 114, 97, 103, 101, 65, 112, 112, 101, 110, 100, 82, 101, 115, 112],
    GoLean.ChoiceErase.CVal.int 20 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 83, 116, 111, 114, 97, 103, 101, 65, 112, 112, 108, 121],
    GoLean.ChoiceErase.CVal.int 21 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str
      #[77, 115, 103, 83, 116, 111, 114, 97, 103, 101, 65, 112, 112, 108, 121, 82, 101, 115, 112],
    GoLean.ChoiceErase.CVal.int 22 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 84, 105, 109, 101, 111, 117, 116, 78, 111, 119],
    GoLean.ChoiceErase.CVal.int 14 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str
      #[77, 115, 103, 84, 114, 97, 110, 115, 102, 101, 114, 76, 101, 97, 100, 101, 114],
    GoLean.ChoiceErase.CVal.int 13 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 85, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101],
    GoLean.ChoiceErase.CVal.int 10 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 86, 111, 116, 101],
    GoLean.ChoiceErase.CVal.int 5 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str #[77, 115, 103, 86, 111, 116, 101, 82, 101, 115, 112],
    GoLean.ChoiceErase.CVal.int 6 (GoLean.GoCore.IntKind.int32))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)) (GoLean.GoCore.Ty.string)),
 GoLean.ChoiceErase.CVal.mp (some 44)⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 84, 114, 97, 110, 115, 105, 116, 105, 111, 110, 65,
        117, 116, 111]),
   (GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 84, 114, 97, 110, 115, 105, 116, 105, 111, 110, 74,
        111, 105, 110, 116, 73, 109, 112, 108, 105, 99, 105, 116]),
   (GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 84, 114, 97, 110, 115, 105, 116, 105, 111, 110, 74,
        111, 105, 110, 116, 69, 120, 112, 108, 105, 99, 105, 116])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.string) (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))),
 GoLean.ChoiceErase.CVal.mp (some 46)⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 84, 114, 97, 110, 115, 105, 116, 105, 111, 110, 65,
        117, 116, 111],
    GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 84, 114, 97, 110, 115, 105, 116, 105, 111, 110, 74,
        111, 105, 110, 116, 69, 120, 112, 108, 105, 99, 105, 116],
    GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 84, 114, 97, 110, 115, 105, 116, 105, 111, 110, 74,
        111, 105, 110, 116, 73, 109, 112, 108, 105, 99, 105, 116],
    GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int32))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32)) (GoLean.GoCore.Ty.string)),
 GoLean.ChoiceErase.CVal.mp (some 48)⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 65, 100, 100, 78, 111, 100, 101]),
   (GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 82, 101, 109, 111, 118, 101, 78, 111, 100, 101]),
   (GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 85, 112, 100, 97, 116, 101, 78, 111, 100, 101]),
   (GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.int32),
    GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 65, 100, 100, 76, 101, 97, 114, 110, 101, 114, 78, 111,
        100, 101])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.map (GoLean.GoCore.Ty.string) (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int32))),
 GoLean.ChoiceErase.CVal.mp (some 50)⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 65, 100, 100, 76, 101, 97, 114, 110, 101, 114, 78, 111,
        100, 101],
    GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 65, 100, 100, 78, 111, 100, 101],
    GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 82, 101, 109, 111, 118, 101, 78, 111, 100, 101],
    GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int32)),
   (GoLean.ChoiceErase.CVal.str
      #[67, 111, 110, 102, 67, 104, 97, 110, 103, 101, 85, 112, 100, 97, 116, 101, 78, 111, 100, 101],
    GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int32))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.matchAckIndexer" }),
 GoLean.ChoiceErase.CVal.mp none⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.DefaultLogger" })),
 GoLean.ChoiceErase.CVal.ref 53⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.DefaultLogger" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.DefaultLogger" }
  [("Logger", GoLean.ChoiceErase.CVal.nilv), ("debug", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.DefaultLogger" })),
 GoLean.ChoiceErase.CVal.ref 55⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.DefaultLogger" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.DefaultLogger" }
  [("Logger", GoLean.ChoiceErase.CVal.nilv), ("debug", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" })),
 GoLean.ChoiceErase.CVal.ref 57⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.HardState" }
  [("Term", GoLean.ChoiceErase.CVal.nilv),
   ("Vote", GoLean.ChoiceErase.CVal.nilv),
   ("Commit", GoLean.ChoiceErase.CVal.nilv)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.string),
 GoLean.ChoiceErase.CVal.str #[114, 97, 102, 116, 58, 32, 115, 116, 111, 112, 112, 101, 100]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 61)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" })),
 GoLean.ChoiceErase.CVal.ref 61⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.goleanShimErrorString" }
  [("s", GoLean.ChoiceErase.CVal.str #[114, 97, 102, 116, 58, 32, 115, 116, 111, 112, 112, 101, 100])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.string),
 GoLean.ChoiceErase.CVal.str
  #[114, 97, 102, 116, 32, 112, 114, 111, 112, 111, 115, 97, 108, 32, 100, 114, 111, 112, 112, 101, 100]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 65)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" })),
 GoLean.ChoiceErase.CVal.ref 65⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.goleanShimErrorString" }
  [("s",
    GoLean.ChoiceErase.CVal.str
      #[114, 97, 102, 116, 32, 112, 114, 111, 112, 111, 115, 97, 108, 32, 100, 114, 111, 112, 112, 101, 100])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" })),
 GoLean.ChoiceErase.CVal.ref 67⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.lockedRand" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.lockedRand" }
  [("mu", GoLean.ChoiceErase.CVal.sync (GoLean.SyncPrim.mutex false))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.string),
 GoLean.ChoiceErase.CVal.str #[98, 114, 101, 97, 107]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 71)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" })),
 GoLean.ChoiceErase.CVal.ref 71⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.goleanShimErrorString" }
  [("s", GoLean.ChoiceErase.CVal.str #[98, 114, 101, 97, 107])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.string),
 GoLean.ChoiceErase.CVal.str
  #[114, 97, 102, 116, 58, 32, 99, 97, 110, 110, 111, 116, 32, 115, 116, 101, 112, 32, 114, 97, 102, 116, 32,
    108, 111, 99, 97, 108, 32, 109, 101, 115, 115, 97, 103, 101]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 75)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" })),
 GoLean.ChoiceErase.CVal.ref 75⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.goleanShimErrorString" }
  [("s",
    GoLean.ChoiceErase.CVal.str
      #[114, 97, 102, 116, 58, 32, 99, 97, 110, 110, 111, 116, 32, 115, 116, 101, 112, 32, 114, 97, 102, 116,
        32, 108, 111, 99, 97, 108, 32, 109, 101, 115, 115, 97, 103, 101])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.string),
 GoLean.ChoiceErase.CVal.str
  #[114, 97, 102, 116, 58, 32, 99, 97, 110, 110, 111, 116, 32, 115, 116, 101, 112, 32, 97, 115, 32, 112, 101,
    101, 114, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 79)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" })),
 GoLean.ChoiceErase.CVal.ref 79⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.goleanShimErrorString" }
  [("s",
    GoLean.ChoiceErase.CVal.str
      #[114, 97, 102, 116, 58, 32, 99, 97, 110, 110, 111, 116, 32, 115, 116, 101, 112, 32, 97, 115, 32, 112,
        101, 101, 114, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.string),
 GoLean.ChoiceErase.CVal.str
  #[114, 101, 113, 117, 101, 115, 116, 101, 100, 32, 105, 110, 100, 101, 120, 32, 105, 115, 32, 117, 110, 97,
    118, 97, 105, 108, 97, 98, 108, 101, 32, 100, 117, 101, 32, 116, 111, 32, 99, 111, 109, 112, 97, 99, 116,
    105, 111, 110]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 83)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" })),
 GoLean.ChoiceErase.CVal.ref 83⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.goleanShimErrorString" }
  [("s",
    GoLean.ChoiceErase.CVal.str
      #[114, 101, 113, 117, 101, 115, 116, 101, 100, 32, 105, 110, 100, 101, 120, 32, 105, 115, 32, 117, 110,
        97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 100, 117, 101, 32, 116, 111, 32, 99, 111, 109, 112, 97,
        99, 116, 105, 111, 110])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.string),
 GoLean.ChoiceErase.CVal.str
  #[114, 101, 113, 117, 101, 115, 116, 101, 100, 32, 105, 110, 100, 101, 120, 32, 105, 115, 32, 111, 108, 100,
    101, 114, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 101, 120, 105, 115, 116, 105, 110, 103, 32, 115,
    110, 97, 112, 115, 104, 111, 116]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 87)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" })),
 GoLean.ChoiceErase.CVal.ref 87⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.goleanShimErrorString" }
  [("s",
    GoLean.ChoiceErase.CVal.str
      #[114, 101, 113, 117, 101, 115, 116, 101, 100, 32, 105, 110, 100, 101, 120, 32, 105, 115, 32, 111, 108,
        100, 101, 114, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 101, 120, 105, 115, 116, 105, 110, 103,
        32, 115, 110, 97, 112, 115, 104, 111, 116])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.string),
 GoLean.ChoiceErase.CVal.str
  #[114, 101, 113, 117, 101, 115, 116, 101, 100, 32, 101, 110, 116, 114, 121, 32, 97, 116, 32, 105, 110, 100,
    101, 120, 32, 105, 115, 32, 117, 110, 97, 118, 97, 105, 108, 97, 98, 108, 101]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 91)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" })),
 GoLean.ChoiceErase.CVal.ref 91⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.goleanShimErrorString" }
  [("s",
    GoLean.ChoiceErase.CVal.str
      #[114, 101, 113, 117, 101, 115, 116, 101, 100, 32, 101, 110, 116, 114, 121, 32, 97, 116, 32, 105, 110,
        100, 101, 120, 32, 105, 115, 32, 117, 110, 97, 118, 97, 105, 108, 97, 98, 108, 101])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.string),
 GoLean.ChoiceErase.CVal.str
  #[115, 110, 97, 112, 115, 104, 111, 116, 32, 105, 115, 32, 116, 101, 109, 112, 111, 114, 97, 114, 105, 108,
    121, 32, 117, 110, 97, 118, 97, 105, 108, 97, 98, 108, 101]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.interface { key := "error" }),
 GoLean.ChoiceErase.CVal.iface
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }))
  (GoLean.ChoiceErase.CVal.ref 95)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" })),
 GoLean.ChoiceErase.CVal.ref 95⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.goleanShimErrorString" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.goleanShimErrorString" }
  [("s",
    GoLean.ChoiceErase.CVal.str
      #[115, 110, 97, 112, 115, 104, 111, 116, 32, 105, 115, 32, 116, 101, 109, 112, 111, 114, 97, 114, 105,
        108, 121, 32, 117, 110, 97, 118, 97, 105, 108, 97, 98, 108, 101])]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" })),
 GoLean.ChoiceErase.CVal.ref 97⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }),
 GoLean.ChoiceErase.CVal.strct { key := "main.harnessLogger" } []⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
 GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
 GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
 GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
 GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.int)),
 GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "main.twin" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "main.twin" }
  [("nodes", GoLean.ChoiceErase.CVal.sl (some 104) 0 3),
   ("net", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("live", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("leaderOf", GoLean.ChoiceErase.CVal.mp (some 105)),
   ("byIndex", GoLean.ChoiceErase.CVal.mp (some 106)),
   ("claims", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("committed", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("violations", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("pending", GoLean.ChoiceErase.CVal.sl (some 107) 0 2),
   ("driven", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("seq", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int)),
   ("trace",
    GoLean.ChoiceErase.CVal.str #[91, 99, 104, 111, 105, 99, 101, 45, 100, 114, 105, 118, 101, 110, 93, 10]),
   ("halt", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.backing
  (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.twinNode" })),
 GoLean.ChoiceErase.CVal.arr
  [GoLean.ChoiceErase.CVal.ref 108, GoLean.ChoiceErase.CVal.ref 109, GoLean.ChoiceErase.CVal.ref 110]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata []⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata []⟩,
   ⟨GoLean.ChoiceErase.CTy.backing (GoLean.GoCore.Ty.string),
 GoLean.ChoiceErase.CVal.arr [GoLean.ChoiceErase.CVal.str #[99, 49], GoLean.ChoiceErase.CVal.str #[99, 50]]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "main.twinNode" }
  [("id", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("rn", GoLean.ChoiceErase.CVal.ref 111),
   ("st", GoLean.ChoiceErase.CVal.ref 112),
   ("term", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("commit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("state", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("applied", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("lastTrm", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("got", GoLean.ChoiceErase.CVal.mp (some 113))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "main.twinNode" }
  [("id", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
   ("rn", GoLean.ChoiceErase.CVal.ref 114),
   ("st", GoLean.ChoiceErase.CVal.ref 115),
   ("term", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("commit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("state", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("applied", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("lastTrm", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("got", GoLean.ChoiceErase.CVal.mp (some 116))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "main.twinNode" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "main.twinNode" }
  [("id", GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.uint64)),
   ("rn", GoLean.ChoiceErase.CVal.ref 117),
   ("st", GoLean.ChoiceErase.CVal.ref 118),
   ("term", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("commit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("state", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("applied", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("lastTrm", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("got", GoLean.ChoiceErase.CVal.mp (some 119))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.RawNode" }
  [("raft", GoLean.ChoiceErase.CVal.ref 120),
   ("asyncStorageWrites", GoLean.ChoiceErase.CVal.bool false),
   ("prevSoftSt", GoLean.ChoiceErase.CVal.ref 121),
   ("prevHardSt", GoLean.ChoiceErase.CVal.ref 122),
   ("stepsOnAdvance", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.MemoryStorage" }
  [("Mutex", GoLean.ChoiceErase.CVal.sync (GoLean.SyncPrim.mutex false)),
   ("hardState", GoLean.ChoiceErase.CVal.nilv),
   ("snapshot", GoLean.ChoiceErase.CVal.ref 123),
   ("ents", GoLean.ChoiceErase.CVal.sl (some 124) 0 1),
   ("callStats",
    GoLean.ChoiceErase.CVal.strct
      { key := "raft.inMemStorageCallStats" }
      [("initialState", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int)),
       ("firstIndex", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int)),
       ("lastIndex", GoLean.ChoiceErase.CVal.int 7 (GoLean.GoCore.IntKind.int)),
       ("entries", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
       ("term", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int)),
       ("snapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int))])]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata []⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.RawNode" }
  [("raft", GoLean.ChoiceErase.CVal.ref 125),
   ("asyncStorageWrites", GoLean.ChoiceErase.CVal.bool false),
   ("prevSoftSt", GoLean.ChoiceErase.CVal.ref 126),
   ("prevHardSt", GoLean.ChoiceErase.CVal.ref 127),
   ("stepsOnAdvance", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.MemoryStorage" }
  [("Mutex", GoLean.ChoiceErase.CVal.sync (GoLean.SyncPrim.mutex false)),
   ("hardState", GoLean.ChoiceErase.CVal.nilv),
   ("snapshot", GoLean.ChoiceErase.CVal.ref 128),
   ("ents", GoLean.ChoiceErase.CVal.sl (some 129) 0 1),
   ("callStats",
    GoLean.ChoiceErase.CVal.strct
      { key := "raft.inMemStorageCallStats" }
      [("initialState", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int)),
       ("firstIndex", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int)),
       ("lastIndex", GoLean.ChoiceErase.CVal.int 7 (GoLean.GoCore.IntKind.int)),
       ("entries", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
       ("term", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int)),
       ("snapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int))])]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata []⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.RawNode" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.RawNode" }
  [("raft", GoLean.ChoiceErase.CVal.ref 130),
   ("asyncStorageWrites", GoLean.ChoiceErase.CVal.bool false),
   ("prevSoftSt", GoLean.ChoiceErase.CVal.ref 131),
   ("prevHardSt", GoLean.ChoiceErase.CVal.ref 132),
   ("stepsOnAdvance", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.MemoryStorage" }
  [("Mutex", GoLean.ChoiceErase.CVal.sync (GoLean.SyncPrim.mutex false)),
   ("hardState", GoLean.ChoiceErase.CVal.nilv),
   ("snapshot", GoLean.ChoiceErase.CVal.ref 133),
   ("ents", GoLean.ChoiceErase.CVal.sl (some 134) 0 1),
   ("callStats",
    GoLean.ChoiceErase.CVal.strct
      { key := "raft.inMemStorageCallStats" }
      [("initialState", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int)),
       ("firstIndex", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.int)),
       ("lastIndex", GoLean.ChoiceErase.CVal.int 7 (GoLean.GoCore.IntKind.int)),
       ("entries", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
       ("term", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int)),
       ("snapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int))])]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata []⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.raft" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.raft" }
  [("id", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("Term", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("Vote", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("readStates", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("raftLog", GoLean.ChoiceErase.CVal.ref 135),
   ("maxMsgSize", GoLean.ChoiceErase.CVal.int 1048576 (GoLean.GoCore.IntKind.uint64)),
   ("maxUncommittedSize", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("trk",
    GoLean.ChoiceErase.CVal.strct
      { key := "tracker.ProgressTracker" }
      [("Config",
        GoLean.ChoiceErase.CVal.strct
          { key := "tracker.Config" }
          [("Voters",
            GoLean.ChoiceErase.CVal.arr
              [GoLean.ChoiceErase.CVal.mp (some 136), GoLean.ChoiceErase.CVal.mp none]),
           ("AutoLeave", GoLean.ChoiceErase.CVal.bool false),
           ("Learners", GoLean.ChoiceErase.CVal.mp none),
           ("LearnersNext", GoLean.ChoiceErase.CVal.mp none)]),
       ("Progress", GoLean.ChoiceErase.CVal.mp (some 137)),
       ("Votes", GoLean.ChoiceErase.CVal.mp (some 138)),
       ("MaxInflight", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
       ("MaxInflightBytes",
        GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64))]),
   ("state", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("isLearner", GoLean.ChoiceErase.CVal.bool false),
   ("msgs", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("msgsAfterAppend", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("lead", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("leadTransferee", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("pendingConfIndex", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("disableConfChangeValidation", GoLean.ChoiceErase.CVal.bool false),
   ("uncommittedSize", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("readOnly", GoLean.ChoiceErase.CVal.ref 139),
   ("electionElapsed", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("heartbeatElapsed", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("checkQuorum", GoLean.ChoiceErase.CVal.bool false),
   ("preVote", GoLean.ChoiceErase.CVal.bool false),
   ("heartbeatTimeout", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int)),
   ("electionTimeout", GoLean.ChoiceErase.CVal.int 10 (GoLean.GoCore.IntKind.int)),
   ("randomizedElectionTimeout", GoLean.ChoiceErase.CVal.masked),
   ("disableProposalForwarding", GoLean.ChoiceErase.CVal.bool false),
   ("stepDownOnRemoval", GoLean.ChoiceErase.CVal.bool false),
   ("tick", GoLean.ChoiceErase.CVal.fn { key := "raft.raft.tickElection" } [GoLean.ChoiceErase.CVal.ref 120]),
   ("step", GoLean.ChoiceErase.CVal.fn { key := "raft.stepFollower" } []),
   ("logger",
    GoLean.ChoiceErase.CVal.iface
      (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
      (GoLean.ChoiceErase.CVal.ref 97)),
   ("pendingReadIndexMessages", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("traceLogger", GoLean.ChoiceErase.CVal.nilv)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.SoftState" }
  [("Lead", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RaftState", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.HardState" }
  [("Term", GoLean.ChoiceErase.CVal.ref 140),
   ("Vote", GoLean.ChoiceErase.CVal.ref 141),
   ("Commit", GoLean.ChoiceErase.CVal.ref 142)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.Snapshot" }
  [("Data", GoLean.ChoiceErase.CVal.sl none 0 0), ("Metadata", GoLean.ChoiceErase.CVal.ref 143)]⟩,
   ⟨GoLean.ChoiceErase.CTy.backing (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })),
 GoLean.ChoiceErase.CVal.arr [GoLean.ChoiceErase.CVal.ref 144]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.raft" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.raft" }
  [("id", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
   ("Term", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("Vote", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("readStates", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("raftLog", GoLean.ChoiceErase.CVal.ref 145),
   ("maxMsgSize", GoLean.ChoiceErase.CVal.int 1048576 (GoLean.GoCore.IntKind.uint64)),
   ("maxUncommittedSize", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("trk",
    GoLean.ChoiceErase.CVal.strct
      { key := "tracker.ProgressTracker" }
      [("Config",
        GoLean.ChoiceErase.CVal.strct
          { key := "tracker.Config" }
          [("Voters",
            GoLean.ChoiceErase.CVal.arr
              [GoLean.ChoiceErase.CVal.mp (some 146), GoLean.ChoiceErase.CVal.mp none]),
           ("AutoLeave", GoLean.ChoiceErase.CVal.bool false),
           ("Learners", GoLean.ChoiceErase.CVal.mp none),
           ("LearnersNext", GoLean.ChoiceErase.CVal.mp none)]),
       ("Progress", GoLean.ChoiceErase.CVal.mp (some 147)),
       ("Votes", GoLean.ChoiceErase.CVal.mp (some 148)),
       ("MaxInflight", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
       ("MaxInflightBytes",
        GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64))]),
   ("state", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("isLearner", GoLean.ChoiceErase.CVal.bool false),
   ("msgs", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("msgsAfterAppend", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("lead", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("leadTransferee", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("pendingConfIndex", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("disableConfChangeValidation", GoLean.ChoiceErase.CVal.bool false),
   ("uncommittedSize", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("readOnly", GoLean.ChoiceErase.CVal.ref 149),
   ("electionElapsed", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("heartbeatElapsed", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("checkQuorum", GoLean.ChoiceErase.CVal.bool false),
   ("preVote", GoLean.ChoiceErase.CVal.bool false),
   ("heartbeatTimeout", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int)),
   ("electionTimeout", GoLean.ChoiceErase.CVal.int 10 (GoLean.GoCore.IntKind.int)),
   ("randomizedElectionTimeout", GoLean.ChoiceErase.CVal.masked),
   ("disableProposalForwarding", GoLean.ChoiceErase.CVal.bool false),
   ("stepDownOnRemoval", GoLean.ChoiceErase.CVal.bool false),
   ("tick", GoLean.ChoiceErase.CVal.fn { key := "raft.raft.tickElection" } [GoLean.ChoiceErase.CVal.ref 125]),
   ("step", GoLean.ChoiceErase.CVal.fn { key := "raft.stepFollower" } []),
   ("logger",
    GoLean.ChoiceErase.CVal.iface
      (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
      (GoLean.ChoiceErase.CVal.ref 97)),
   ("pendingReadIndexMessages", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("traceLogger", GoLean.ChoiceErase.CVal.nilv)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.SoftState" }
  [("Lead", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RaftState", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.HardState" }
  [("Term", GoLean.ChoiceErase.CVal.ref 150),
   ("Vote", GoLean.ChoiceErase.CVal.ref 151),
   ("Commit", GoLean.ChoiceErase.CVal.ref 152)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.Snapshot" }
  [("Data", GoLean.ChoiceErase.CVal.sl none 0 0), ("Metadata", GoLean.ChoiceErase.CVal.ref 153)]⟩,
   ⟨GoLean.ChoiceErase.CTy.backing (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })),
 GoLean.ChoiceErase.CVal.arr [GoLean.ChoiceErase.CVal.ref 154]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.raft" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.raft" }
  [("id", GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.uint64)),
   ("Term", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("Vote", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("readStates", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("raftLog", GoLean.ChoiceErase.CVal.ref 155),
   ("maxMsgSize", GoLean.ChoiceErase.CVal.int 1048576 (GoLean.GoCore.IntKind.uint64)),
   ("maxUncommittedSize", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("trk",
    GoLean.ChoiceErase.CVal.strct
      { key := "tracker.ProgressTracker" }
      [("Config",
        GoLean.ChoiceErase.CVal.strct
          { key := "tracker.Config" }
          [("Voters",
            GoLean.ChoiceErase.CVal.arr
              [GoLean.ChoiceErase.CVal.mp (some 156), GoLean.ChoiceErase.CVal.mp none]),
           ("AutoLeave", GoLean.ChoiceErase.CVal.bool false),
           ("Learners", GoLean.ChoiceErase.CVal.mp none),
           ("LearnersNext", GoLean.ChoiceErase.CVal.mp none)]),
       ("Progress", GoLean.ChoiceErase.CVal.mp (some 157)),
       ("Votes", GoLean.ChoiceErase.CVal.mp (some 158)),
       ("MaxInflight", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
       ("MaxInflightBytes",
        GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64))]),
   ("state", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("isLearner", GoLean.ChoiceErase.CVal.bool false),
   ("msgs", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("msgsAfterAppend", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("lead", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("leadTransferee", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("pendingConfIndex", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("disableConfChangeValidation", GoLean.ChoiceErase.CVal.bool false),
   ("uncommittedSize", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("readOnly", GoLean.ChoiceErase.CVal.ref 159),
   ("electionElapsed", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("heartbeatElapsed", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("checkQuorum", GoLean.ChoiceErase.CVal.bool false),
   ("preVote", GoLean.ChoiceErase.CVal.bool false),
   ("heartbeatTimeout", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.int)),
   ("electionTimeout", GoLean.ChoiceErase.CVal.int 10 (GoLean.GoCore.IntKind.int)),
   ("randomizedElectionTimeout", GoLean.ChoiceErase.CVal.masked),
   ("disableProposalForwarding", GoLean.ChoiceErase.CVal.bool false),
   ("stepDownOnRemoval", GoLean.ChoiceErase.CVal.bool false),
   ("tick", GoLean.ChoiceErase.CVal.fn { key := "raft.raft.tickElection" } [GoLean.ChoiceErase.CVal.ref 130]),
   ("step", GoLean.ChoiceErase.CVal.fn { key := "raft.stepFollower" } []),
   ("logger",
    GoLean.ChoiceErase.CVal.iface
      (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
      (GoLean.ChoiceErase.CVal.ref 97)),
   ("pendingReadIndexMessages", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("traceLogger", GoLean.ChoiceErase.CVal.nilv)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.SoftState" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.SoftState" }
  [("Lead", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RaftState", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.HardState" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.HardState" }
  [("Term", GoLean.ChoiceErase.CVal.ref 160),
   ("Vote", GoLean.ChoiceErase.CVal.ref 161),
   ("Commit", GoLean.ChoiceErase.CVal.ref 162)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.Snapshot" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.Snapshot" }
  [("Data", GoLean.ChoiceErase.CVal.sl none 0 0), ("Metadata", GoLean.ChoiceErase.CVal.ref 163)]⟩,
   ⟨GoLean.ChoiceErase.CTy.backing (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" })),
 GoLean.ChoiceErase.CVal.arr [GoLean.ChoiceErase.CVal.ref 164]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.raftLog" }
  [("storage",
    GoLean.ChoiceErase.CVal.iface
      (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))
      (GoLean.ChoiceErase.CVal.ref 112)),
   ("unstable",
    GoLean.ChoiceErase.CVal.strct
      { key := "raft.unstable" }
      [("snapshot", GoLean.ChoiceErase.CVal.nilv),
       ("entries", GoLean.ChoiceErase.CVal.sl none 0 0),
       ("offset", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
       ("snapshotInProgress", GoLean.ChoiceErase.CVal.bool false),
       ("offsetInProgress", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
       ("logger",
        GoLean.ChoiceErase.CVal.iface
          (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
          (GoLean.ChoiceErase.CVal.ref 97))]),
   ("committed", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("applying", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("applied", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("logger",
    GoLean.ChoiceErase.CVal.iface
      (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
      (GoLean.ChoiceErase.CVal.ref 97)),
   ("maxApplyingEntsSize", GoLean.ChoiceErase.CVal.int 1048576 (GoLean.GoCore.IntKind.uint64)),
   ("applyingEntsSize", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("applyingEntsPaused", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64),
    GoLean.ChoiceErase.CVal.strct { key := "struct{}" } []),
   (GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64),
    GoLean.ChoiceErase.CVal.strct { key := "struct{}" } []),
   (GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.uint64),
    GoLean.ChoiceErase.CVal.strct { key := "struct{}" } [])]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64), GoLean.ChoiceErase.CVal.ref 165),
   (GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64), GoLean.ChoiceErase.CVal.ref 166),
   (GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.uint64), GoLean.ChoiceErase.CVal.ref 167)]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata []⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.readOnly" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.readOnly" }
  [("option", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("acks", GoLean.ChoiceErase.CVal.mp (some 168)),
   ("unconfirmedReads", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("confirmedReads", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.SnapshotMetadata" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.SnapshotMetadata" }
  [("ConfState", GoLean.ChoiceErase.CVal.ref 169),
   ("Index", GoLean.ChoiceErase.CVal.ref 170),
   ("Term", GoLean.ChoiceErase.CVal.ref 171)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.Entry" }
  [("Term", GoLean.ChoiceErase.CVal.ref 172),
   ("Index", GoLean.ChoiceErase.CVal.ref 173),
   ("Type", GoLean.ChoiceErase.CVal.nilv),
   ("Data", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.raftLog" }
  [("storage",
    GoLean.ChoiceErase.CVal.iface
      (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))
      (GoLean.ChoiceErase.CVal.ref 115)),
   ("unstable",
    GoLean.ChoiceErase.CVal.strct
      { key := "raft.unstable" }
      [("snapshot", GoLean.ChoiceErase.CVal.nilv),
       ("entries", GoLean.ChoiceErase.CVal.sl none 0 0),
       ("offset", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
       ("snapshotInProgress", GoLean.ChoiceErase.CVal.bool false),
       ("offsetInProgress", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
       ("logger",
        GoLean.ChoiceErase.CVal.iface
          (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
          (GoLean.ChoiceErase.CVal.ref 97))]),
   ("committed", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("applying", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("applied", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("logger",
    GoLean.ChoiceErase.CVal.iface
      (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
      (GoLean.ChoiceErase.CVal.ref 97)),
   ("maxApplyingEntsSize", GoLean.ChoiceErase.CVal.int 1048576 (GoLean.GoCore.IntKind.uint64)),
   ("applyingEntsSize", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("applyingEntsPaused", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64),
    GoLean.ChoiceErase.CVal.strct { key := "struct{}" } []),
   (GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64),
    GoLean.ChoiceErase.CVal.strct { key := "struct{}" } []),
   (GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.uint64),
    GoLean.ChoiceErase.CVal.strct { key := "struct{}" } [])]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64), GoLean.ChoiceErase.CVal.ref 174),
   (GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64), GoLean.ChoiceErase.CVal.ref 175),
   (GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.uint64), GoLean.ChoiceErase.CVal.ref 176)]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata []⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.readOnly" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.readOnly" }
  [("option", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("acks", GoLean.ChoiceErase.CVal.mp (some 177)),
   ("unconfirmedReads", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("confirmedReads", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.SnapshotMetadata" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.SnapshotMetadata" }
  [("ConfState", GoLean.ChoiceErase.CVal.ref 178),
   ("Index", GoLean.ChoiceErase.CVal.ref 179),
   ("Term", GoLean.ChoiceErase.CVal.ref 180)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.Entry" }
  [("Term", GoLean.ChoiceErase.CVal.ref 181),
   ("Index", GoLean.ChoiceErase.CVal.ref 182),
   ("Type", GoLean.ChoiceErase.CVal.nilv),
   ("Data", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.raftLog" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.raftLog" }
  [("storage",
    GoLean.ChoiceErase.CVal.iface
      (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "raft.MemoryStorage" }))
      (GoLean.ChoiceErase.CVal.ref 118)),
   ("unstable",
    GoLean.ChoiceErase.CVal.strct
      { key := "raft.unstable" }
      [("snapshot", GoLean.ChoiceErase.CVal.nilv),
       ("entries", GoLean.ChoiceErase.CVal.sl none 0 0),
       ("offset", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
       ("snapshotInProgress", GoLean.ChoiceErase.CVal.bool false),
       ("offsetInProgress", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
       ("logger",
        GoLean.ChoiceErase.CVal.iface
          (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
          (GoLean.ChoiceErase.CVal.ref 97))]),
   ("committed", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("applying", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("applied", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("logger",
    GoLean.ChoiceErase.CVal.iface
      (GoLean.GoCore.Ty.pointer (GoLean.GoCore.Ty.defined { key := "main.harnessLogger" }))
      (GoLean.ChoiceErase.CVal.ref 97)),
   ("maxApplyingEntsSize", GoLean.ChoiceErase.CVal.int 1048576 (GoLean.GoCore.IntKind.uint64)),
   ("applyingEntsSize", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("applyingEntsPaused", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64),
    GoLean.ChoiceErase.CVal.strct { key := "struct{}" } []),
   (GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64),
    GoLean.ChoiceErase.CVal.strct { key := "struct{}" } []),
   (GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.uint64),
    GoLean.ChoiceErase.CVal.strct { key := "struct{}" } [])]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata
  [(GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64), GoLean.ChoiceErase.CVal.ref 183),
   (GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64), GoLean.ChoiceErase.CVal.ref 184),
   (GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.uint64), GoLean.ChoiceErase.CVal.ref 185)]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata []⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raft.readOnly" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raft.readOnly" }
  [("option", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("acks", GoLean.ChoiceErase.CVal.mp (some 186)),
   ("unconfirmedReads", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("confirmedReads", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64))]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.SnapshotMetadata" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.SnapshotMetadata" }
  [("ConfState", GoLean.ChoiceErase.CVal.ref 187),
   ("Index", GoLean.ChoiceErase.CVal.ref 188),
   ("Term", GoLean.ChoiceErase.CVal.ref 189)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.Entry" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.Entry" }
  [("Term", GoLean.ChoiceErase.CVal.ref 190),
   ("Index", GoLean.ChoiceErase.CVal.ref 191),
   ("Type", GoLean.ChoiceErase.CVal.nilv),
   ("Data", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Progress" }
  [("Match", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("Next", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
   ("sentCommit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("State", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("PendingSnapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RecentActive", GoLean.ChoiceErase.CVal.bool false),
   ("MsgAppFlowPaused", GoLean.ChoiceErase.CVal.bool false),
   ("Inflights", GoLean.ChoiceErase.CVal.ref 192),
   ("IsLearner", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Progress" }
  [("Match", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("Next", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
   ("sentCommit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("State", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("PendingSnapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RecentActive", GoLean.ChoiceErase.CVal.bool false),
   ("MsgAppFlowPaused", GoLean.ChoiceErase.CVal.bool false),
   ("Inflights", GoLean.ChoiceErase.CVal.ref 193),
   ("IsLearner", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Progress" }
  [("Match", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("Next", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
   ("sentCommit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("State", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("PendingSnapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RecentActive", GoLean.ChoiceErase.CVal.bool false),
   ("MsgAppFlowPaused", GoLean.ChoiceErase.CVal.bool false),
   ("Inflights", GoLean.ChoiceErase.CVal.ref 194),
   ("IsLearner", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata []⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.ConfState" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.ConfState" }
  [("Voters", GoLean.ChoiceErase.CVal.sl (some 195) 0 3),
   ("Learners", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("VotersOutgoing", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("LearnersNext", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("AutoLeave", GoLean.ChoiceErase.CVal.ref 196)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Progress" }
  [("Match", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("Next", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
   ("sentCommit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("State", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("PendingSnapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RecentActive", GoLean.ChoiceErase.CVal.bool false),
   ("MsgAppFlowPaused", GoLean.ChoiceErase.CVal.bool false),
   ("Inflights", GoLean.ChoiceErase.CVal.ref 197),
   ("IsLearner", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Progress" }
  [("Match", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("Next", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
   ("sentCommit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("State", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("PendingSnapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RecentActive", GoLean.ChoiceErase.CVal.bool false),
   ("MsgAppFlowPaused", GoLean.ChoiceErase.CVal.bool false),
   ("Inflights", GoLean.ChoiceErase.CVal.ref 198),
   ("IsLearner", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Progress" }
  [("Match", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("Next", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
   ("sentCommit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("State", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("PendingSnapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RecentActive", GoLean.ChoiceErase.CVal.bool false),
   ("MsgAppFlowPaused", GoLean.ChoiceErase.CVal.bool false),
   ("Inflights", GoLean.ChoiceErase.CVal.ref 199),
   ("IsLearner", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata []⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.ConfState" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.ConfState" }
  [("Voters", GoLean.ChoiceErase.CVal.sl (some 200) 0 3),
   ("Learners", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("VotersOutgoing", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("LearnersNext", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("AutoLeave", GoLean.ChoiceErase.CVal.ref 201)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Progress" }
  [("Match", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("Next", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
   ("sentCommit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("State", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("PendingSnapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RecentActive", GoLean.ChoiceErase.CVal.bool false),
   ("MsgAppFlowPaused", GoLean.ChoiceErase.CVal.bool false),
   ("Inflights", GoLean.ChoiceErase.CVal.ref 202),
   ("IsLearner", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Progress" }
  [("Match", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("Next", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
   ("sentCommit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("State", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("PendingSnapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RecentActive", GoLean.ChoiceErase.CVal.bool false),
   ("MsgAppFlowPaused", GoLean.ChoiceErase.CVal.bool false),
   ("Inflights", GoLean.ChoiceErase.CVal.ref 203),
   ("IsLearner", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Progress" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Progress" }
  [("Match", GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)),
   ("Next", GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64)),
   ("sentCommit", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("State", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("PendingSnapshot", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("RecentActive", GoLean.ChoiceErase.CVal.bool false),
   ("MsgAppFlowPaused", GoLean.ChoiceErase.CVal.bool false),
   ("Inflights", GoLean.ChoiceErase.CVal.ref 204),
   ("IsLearner", GoLean.ChoiceErase.CVal.bool false)]⟩,
   ⟨GoLean.ChoiceErase.CTy.none,
 GoLean.ChoiceErase.CVal.mdata []⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "raftpb.ConfState" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "raftpb.ConfState" }
  [("Voters", GoLean.ChoiceErase.CVal.sl (some 205) 0 3),
   ("Learners", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("VotersOutgoing", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("LearnersNext", GoLean.ChoiceErase.CVal.sl none 0 0),
   ("AutoLeave", GoLean.ChoiceErase.CVal.ref 206)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64)⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Inflights" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Inflights" }
  [("start", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("count", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("bytes", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("size", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
   ("maxBytes", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("buffer", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Inflights" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Inflights" }
  [("start", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("count", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("bytes", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("size", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
   ("maxBytes", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("buffer", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Inflights" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Inflights" }
  [("start", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("count", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("bytes", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("size", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
   ("maxBytes", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("buffer", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.backing (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.arr
  [GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64),
   GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64),
   GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.uint64)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.bool),
 GoLean.ChoiceErase.CVal.bool false⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Inflights" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Inflights" }
  [("start", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("count", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("bytes", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("size", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
   ("maxBytes", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("buffer", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Inflights" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Inflights" }
  [("start", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("count", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("bytes", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("size", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
   ("maxBytes", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("buffer", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Inflights" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Inflights" }
  [("start", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("count", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("bytes", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("size", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
   ("maxBytes", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("buffer", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.backing (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.arr
  [GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64),
   GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64),
   GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.uint64)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.bool),
 GoLean.ChoiceErase.CVal.bool false⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Inflights" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Inflights" }
  [("start", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("count", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("bytes", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("size", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
   ("maxBytes", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("buffer", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Inflights" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Inflights" }
  [("start", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("count", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("bytes", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("size", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
   ("maxBytes", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("buffer", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.defined { key := "tracker.Inflights" }),
 GoLean.ChoiceErase.CVal.strct
  { key := "tracker.Inflights" }
  [("start", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("count", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.int)),
   ("bytes", GoLean.ChoiceErase.CVal.int 0 (GoLean.GoCore.IntKind.uint64)),
   ("size", GoLean.ChoiceErase.CVal.int 256 (GoLean.GoCore.IntKind.int)),
   ("maxBytes", GoLean.ChoiceErase.CVal.int 18446744073709551615 (GoLean.GoCore.IntKind.uint64)),
   ("buffer", GoLean.ChoiceErase.CVal.sl none 0 0)]⟩,
   ⟨GoLean.ChoiceErase.CTy.backing (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)),
 GoLean.ChoiceErase.CVal.arr
  [GoLean.ChoiceErase.CVal.int 1 (GoLean.GoCore.IntKind.uint64),
   GoLean.ChoiceErase.CVal.int 2 (GoLean.GoCore.IntKind.uint64),
   GoLean.ChoiceErase.CVal.int 3 (GoLean.GoCore.IntKind.uint64)]⟩,
   ⟨GoLean.ChoiceErase.CTy.exact (GoLean.GoCore.Ty.bool),
 GoLean.ChoiceErase.CVal.bool false⟩]

def seedCForm : CForm :=
  ⟨seedCFormRoots, seedCFormCells, []⟩

end GoLean.RaftSeam
