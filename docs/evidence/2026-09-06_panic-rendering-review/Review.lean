import GoLean.GoCore.Machine

namespace IndependentPanicRendererReview
open GoLean GoLean.GoCore GoLean.GoCore.Machine
set_option maxRecDepth 4096

def decodedBytes (bytes : Array UInt8) := (utf8String? bytes).map (·.toUTF8.data)

/-- Every one-byte ASCII value survives decoding, including NUL, control
characters, newline and DEL. This checks the model, not shell serialization. -/
theorem all_ascii_bytes_roundtrip :
    (List.range 128).all (fun n => decodedBytes #[n.toUInt8] == some #[n.toUInt8]) = true := by
  decide +kernel

/-- Legal scalar boundary encodings, including noncharacters, remain bytes. -/
theorem scalar_boundary_roundtrip :
    [#[0xc2, 0x80], #[0xdf, 0xbf], #[0xe0, 0xa0, 0x80],
      #[0xed, 0x9f, 0xbf], #[0xee, 0x80, 0x80], #[0xef, 0xbf, 0xbe],
      #[0xef, 0xbf, 0xbf], #[0xf0, 0x90, 0x80, 0x80], #[0xf4, 0x8f, 0xbf, 0xbf]].all
      (fun bytes => decodedBytes bytes == some bytes) = true := by
  decide +kernel

def payload (bytes : Array UInt8) : GoValue := .interface .string (.string ⟨bytes⟩)

theorem projection_preserves_carriage_return :
    (renderPanicHead {} ⟨payload #[97, 13, 10, 98], true⟩ []).map (·.toUTF8.data) =
      some #[97, 13] := by decide +kernel

theorem output_control_bytes_preserved_in_model :
    (renderPanicHead {} ⟨payload #[97, 0, 98, 1, 99], false⟩ []).map (·.toUTF8.data) =
      some #[97, 0, 98, 1, 99] := by decide +kernel

theorem invalid_tail_is_not_hidden :
    renderPanicHead {} ⟨payload #[97, 10, 0xe2, 0x82], false⟩ [] = none := by
  decide +kernel

#print axioms all_ascii_bytes_roundtrip
#print axioms scalar_boundary_roundtrip
#print axioms projection_preserves_carriage_return
#print axioms output_control_bytes_preserved_in_model
#print axioms invalid_tail_is_not_hidden
end IndependentPanicRendererReview
