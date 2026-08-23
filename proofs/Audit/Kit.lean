import Lean
import GoLeanProofs.StepKit
import GoLeanProofs.Sym.TableExt
import GoLeanProofs.SliceMem
import GoLeanProofs.StringMem
import GoLeanProofs.MapMem
import GoLeanProofs.MapLoops
import GoLeanProofs.FuelMeasure
import GoLeanProofs.Frame.Threshold
import GoLeanProofs.Examples.Fib
import GoLeanProofs.Examples.Gcd
import GoLeanProofs.Examples.MinMax
import GoLeanProofs.Examples.MinMax.HarnessR
import GoLeanProofs.Examples.Reverse
import GoLeanProofs.Examples.Reverse.HarnessV
import GoLeanProofs.Examples.InsertionSort
import GoLeanProofs.Examples.WordCount
import GoLeanProofs.Examples.WordCount.HarnessR
import GoLeanProofs.Examples.BinSearch
import GoLeanProofs.Sym.SpikeKadane

/-!
# In-build axiom gate — the KIT SURFACE

Gallery Campaign G0 item 4 (2026-08-15): the promotion wave's audit
wiring, adapted — every PUBLIC lemma of the direct-method kit
(`StepKit`, `SliceMem`, `MapMem`, `FuelMeasure`) and every
`derive_entry_eq`-emitted entry-equation theorem gets a verbatim
`#print axioms` `#guard_msgs` pin, so the kit is an audited surface
exactly like the examples (the brick-wp promotion-wave P5 pattern:
38 `Print Assumptions` entries landed WITH the promoted surface).

The exhaustive in-build sweep (root `Audit.lean`) already bounds every
declaration by the classical trio; these pins add EXACTNESS — a kit
lemma silently acquiring `Classical.choice` (say, through a new
dependency) is a visible diff here even though the sweep would stay
green. Pin lists follow each module's sealed PUBLIC API section;
`private` internals are deliberately unpinned (spelling may change).

To re-baseline after an intended change: `#print axioms <name>`,
update the matching docstring in the same commit, with the reason.
-/

namespace GoLean.Iris.Audit

/-! ## StepKit — the conditioned step-glue kit (26 public lemmas;
+2 in the GAP-M2 lift and +1 (`set_append_left`) in the GAP-C1 lift,
2026-08-15 — `DeadFrom` itself is a def, unpinned like the other
vocabulary defs) -/

/-- info: 'GoLean.Surface.lookup_append_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.lookup_append_left
/-- info: 'GoLean.Surface.lookup_append_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.lookup_append_right
/-- info: 'GoLean.Surface.set_append_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.set_append_right
/-- info: 'GoLean.Surface.set_fresh' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.set_fresh
/-- info: 'GoLean.Surface.set_append_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.set_append_left
/-- info: 'GoLean.Surface.base_beq_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.base_beq_false
/-- info: 'GoLean.Surface.lookup_cons_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.lookup_cons_ne
/-- info: 'GoLean.Surface.set_singleton_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.set_singleton_self
/-- info: 'GoLean.Surface.lookup_singleton_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.lookup_singleton_self
/-- info: 'GoLean.Surface.DeadFrom.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.DeadFrom.push
-- WP arc s2 item 1 (2026-08-18): the footprint pack — the lookup/set
-- battery + the DeadFrom algebra + the FreshFrom (whole-heap footprint
-- reading) views. Fresh probe: `.tmp/pinprobe8.lean`.
/-- info: 'GoLean.Surface.lookup_set_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.lookup_set_self
/-- info: 'GoLean.Surface.lookup_set_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.lookup_set_other
/-- info: 'GoLean.Surface.lookup_cons_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.lookup_cons_self
/-- info: 'GoLean.Surface.set_cons_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.set_cons_ne
/-- info: 'GoLean.Surface.set_cons_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.set_cons_self
/-- info: 'GoLean.Surface.set_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.set_set
/-- info: 'GoLean.Surface.set_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.set_comm
/-- info: 'GoLean.Surface.set_self_of_lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.set_self_of_lookup
/-- info: 'GoLean.Surface.DeadFrom.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.DeadFrom.mono
/-- info: 'GoLean.Surface.DeadFrom.push3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.DeadFrom.push3
/-- info: 'GoLean.Surface.DeadFrom.set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.DeadFrom.set
/-- info: 'GoLean.Surface.DeadFrom.lt_of_lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.DeadFrom.lt_of_lookup
/-- info: 'GoLean.Surface.FreshFrom.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.FreshFrom.mono
/-- info: 'GoLean.Surface.FreshFrom.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.FreshFrom.push
/-- info: 'GoLean.Surface.FreshFrom.push2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.FreshFrom.push2
/-- info: 'GoLean.Surface.FreshFrom.push3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.FreshFrom.push3
/-- info: 'GoLean.Surface.FreshFrom.set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.FreshFrom.set
/-- info: 'GoLean.Surface.FreshFrom.lt_of_lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.FreshFrom.lt_of_lookup
-- WP arc s2 item 5 (2026-08-18): growing-heap front support — the
-- executable front bound + live-cell lookup/set + the state-level
-- store. Fresh probe: `.tmp/pinprobe12.lean`.
/-- info: 'GoLean.Surface.lookup_of_keysBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.lookup_of_keysBelow
/-- info: 'GoLean.Surface.lookup_frontD_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.lookup_frontD_none
/-- info: 'GoLean.Surface.lookup_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.lookup_live
/-- info: 'GoLean.Surface.set_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.set_live
/-- info: 'GoLean.Surface.storeTarget_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.storeTarget_live
/-- info: 'GoLean.Surface.DeadFrom.push2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.DeadFrom.push2
/-- info: 'GoLean.Surface.stepFnIter_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFnIter_one
/-- info: 'GoLean.Surface.stepFn_call_enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_call_enter
/-- info: 'GoLean.Surface.stepFn_makeSlice_u64_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_makeSlice_u64_step
/-- info: 'GoLean.Surface.stepFn_strict_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_strict_apply
/-- info: 'GoLean.Surface.stepFn_store_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_store_step
/-- info: 'GoLean.Surface.stepFn_stmtOp_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_stmtOp_apply
/-- info: 'GoLean.Surface.stepFn_var' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_var
/-- info: 'GoLean.Surface.stepFn_init_seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_init_seq
/-- info: 'GoLean.Surface.stepFn_seqn_splice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_seqn_splice
/-- info: 'GoLean.Surface.stepFn_seq_pop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_seq_pop
/-- info: 'GoLean.Surface.stepFn_storeK_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_storeK_nil
-- WP arc s1 lift 6 (2026-08-18): the frame-exit step + the promoted
-- queue glue (stepFn_block in StepKit; the stepFnIter_* composites in
-- FuelMeasure). Fresh probe: `.tmp/pinprobe7.lean`.
/-- info: 'GoLean.Surface.stepFn_return_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_return_frame
/-- info: 'GoLean.Surface.stepFn_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_block
/-- info: 'GoLean.Surface.stepFnIter_splice_pop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFnIter_splice_pop
/-- info: 'GoLean.Surface.stepFnIter_drain3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFnIter_drain3
/-- info: 'GoLean.Surface.stepFnIter_block_pop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFnIter_block_pop
-- WP arc s2 item 2 (2026-08-18): the call-span combinator + the
-- loadMany pair that feeds stepFn_return_frame. Fresh probe:
-- `.tmp/pinprobe9.lean`.
/-- info: 'GoLean.Surface.loadMany_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.loadMany_one
/-- info: 'GoLean.Surface.loadMany_two' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.loadMany_two
/-- info: 'GoLean.Surface.stepFnIter_call_span' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFnIter_call_span
/-- info: 'GoLean.Surface.storeTarget_addr' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.storeTarget_addr
/-- info: 'GoLean.Surface.stepFn_mapAssign_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_mapAssign_apply
/-- info: 'GoLean.Surface.stepFn_mapRangeStart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_mapRangeStart
/-- info: 'GoLean.Surface.natFromNonneg_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.natFromNonneg_cast

/-! ## SliceMem — slice-in-memory vocabulary + executable op facts
(81 public lemmas; +11 in the GAP-P2 family/prefix lift, 2026-08-15;
+14 in the WP arc s1 lift 1 — the normal-form/op-fact family
completion + the C4 `intKind_normalize_idem` lift-out-of-HeapBridge;
+30 in the WP arc s1 lift 2 — the generic family layer
`familyZ`/`padZ`/`familyF`/`familyOf`/`takePad`; +9 in the WP arc s1
lift 3 — the swap surgery + count algebra — the
`familyMod`/`prefixPad`/family/`iterStep` defs are unpinned like the
other vocabulary defs) -/

/-- info: 'GoLean.SliceMem.unorm_of_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.unorm_of_range
/-- info: 'GoLean.SliceMem.inorm_of_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.inorm_of_range
/-- info: 'GoLean.SliceMem.inorm_nat_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.inorm_nat_of_lt
/-- info: 'GoLean.SliceMem.unorm_nat_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.unorm_nat_of_lt
/-- info: 'GoLean.SliceMem.unorm_add_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.unorm_add_nat
/-- info: 'GoLean.SliceMem.applyStrictOp_indexGet_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_indexGet_slice
/-- info: 'GoLean.SliceMem.applyStrictOp_len_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_len_slice
/-- info: 'GoLean.SliceMem.applyStrictOp_sliceExpr_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_sliceExpr_array
-- WP arc s1 lift 6 (2026-08-18): GAP-RESLICE, the general
-- s[lo:hi]-at-slice-base form. Fresh probe: `.tmp/pinprobe7.lean`.
/-- info: 'GoLean.SliceMem.applyStrictOp_sliceExpr_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_sliceExpr_slice
-- WP arc s2 item 3 (2026-08-18): GAP-APPEND — the one-element
-- growing-slice append family, element-type-generic via conditioned
-- hypotheses. Fresh probe: `.tmp/pinprobe10.lean`.
/-- info: 'GoLean.SliceMem.buildAppendBackingValue_of_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.buildAppendBackingValue_of_norm
/-- info: 'GoLean.SliceMem.applyStmtOp_append1_inplace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStmtOp_append1_inplace
/-- info: 'GoLean.SliceMem.appendRealizedCap_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.appendRealizedCap_lower
/-- info: 'GoLean.SliceMem.appendRealizedCap_upper' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.appendRealizedCap_upper
/-- info: 'GoLean.SliceMem.applyStmtOp_append1_spill' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStmtOp_append1_spill
/-- info: 'GoLean.SliceMem.applyStmtOp_append1_spill_ex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStmtOp_append1_spill_ex
-- WP arc s2 item 4 (2026-08-18): StringMem — the string VALUE
-- vocabulary (no heap half, by the recorded negative finding). Fresh
-- probe: `.tmp/pinprobe11.lean`.
/-- info: 'GoLean.StringMem.gs_nil' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.StringMem.gs_nil
/-- info: 'GoLean.StringMem.gs_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.StringMem.gs_append
/-- info: 'GoLean.StringMem.applyStrictOp_stringFromRune_ascii' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.StringMem.applyStrictOp_stringFromRune_ascii
/-- info: 'GoLean.StringMem.applyStrictOp_indexGet_string' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.StringMem.applyStrictOp_indexGet_string
/-- info: 'GoLean.StringMem.applyStrictOp_len_string' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.StringMem.applyStrictOp_len_string
/-- info: 'GoLean.StringMem.applyStrictOp_slice_string' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.StringMem.applyStrictOp_slice_string
/-- info: 'GoLean.SliceMem.mem_set_of_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.mem_set_of_mem
/-- info: 'GoLean.SliceMem.storeTarget_slice_u64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.storeTarget_slice_u64
/-- info: 'GoLean.SliceMem.normalizeValueForTy_arr_u64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.normalizeValueForTy_arr_u64
/-- info: 'GoLean.SliceMem.storeTarget_arrayLocal_u64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.storeTarget_arrayLocal_u64
/-- info: 'GoLean.SliceMem.getElem?_mapU' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.getElem?_mapU
/-- info: 'GoLean.SliceMem.getD_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.getD_mem
/-- info: 'GoLean.SliceMem.locSup_mapU' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.locSup_mapU
/-- info: 'GoLean.SliceMem.applyStrictOp_lessCmp_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_lessCmp_int
/-- info: 'GoLean.SliceMem.applyStrictOp_mod_u64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_mod_u64

-- WP arc s1 lift 1 (2026-08-16): the normal-form family + the
-- completed integer executable-op family + the C4 lift. Transcribed
-- verbatim from a fresh probe (`.tmp/pinprobe1.lean` at the lift
-- commit).
/-- info: 'GoLean.SliceMem.unorm_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.unorm_nat
/-- info: 'GoLean.SliceMem.unorm_mul_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.unorm_mul_nat
/-- info: 'GoLean.SliceMem.intKind_normalize_idem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.intKind_normalize_idem
/-- info: 'GoLean.SliceMem.normalize_of_range_unsigned' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.normalize_of_range_unsigned
/-- info: 'GoLean.SliceMem.normalize_of_range_signed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.normalize_of_range_signed
/-- info: 'GoLean.SliceMem.applyStrictOp_mul_u64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_mul_u64
/-- info: 'GoLean.SliceMem.applyStrictOp_div_u64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_div_u64
/-- info: 'GoLean.SliceMem.applyStrictOp_add_u64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_add_u64
/-- info: 'GoLean.SliceMem.applyStrictOp_sub_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_sub_int
/-- info: 'GoLean.SliceMem.applyStrictOp_eqCmp_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_eqCmp_int
/-- info: 'GoLean.SliceMem.applyStrictOp_neqCmp_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_neqCmp_int
/-- info: 'GoLean.SliceMem.applyStrictOp_atMostCmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_atMostCmp
/-- info: 'GoLean.SliceMem.applyStrictOp_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_not
/-- info: 'GoLean.SliceMem.applyStrictOp_convert_u64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.applyStrictOp_convert_u64

-- WP arc s1 lift 2 (2026-08-16): the generic family layer.
-- Transcribed verbatim from a fresh probe (`.tmp/pinprobe2.lean`
-- at the lift commit).
/-- info: 'GoLean.SliceMem.familyZ_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyZ_length
/-- info: 'GoLean.SliceMem.familyZ_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyZ_mem
/-- info: 'GoLean.SliceMem.familyZ_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyZ_succ
/-- info: 'GoLean.SliceMem.familyZ_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyZ_set
/-- info: 'GoLean.SliceMem.familyZ_getD' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyZ_getD
/-- info: 'GoLean.SliceMem.padZ_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.padZ_zero
/-- info: 'GoLean.SliceMem.padZ_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.padZ_length
/-- info: 'GoLean.SliceMem.padZ_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.padZ_set
/-- info: 'GoLean.SliceMem.padZ_set_any' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.padZ_set_any
/-- info: 'GoLean.SliceMem.padZ_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.padZ_range
/-- info: 'GoLean.SliceMem.familyMod_eq_familyF' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.SliceMem.familyMod_eq_familyF
/-- info: 'GoLean.SliceMem.familyF_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyF_length
/-- info: 'GoLean.SliceMem.familyF_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyF_range
/-- info: 'GoLean.SliceMem.familyFZ_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyFZ_range
/-- info: 'GoLean.SliceMem.familyF_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyF_succ
/-- info: 'GoLean.SliceMem.familyF_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyF_set
/-- info: 'GoLean.SliceMem.familyF_getD' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyF_getD
/-- info: 'GoLean.SliceMem.prefixPad_familyF_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.prefixPad_familyF_set
/-- info: 'GoLean.SliceMem.iterStep_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.iterStep_lt
/-- info: 'GoLean.SliceMem.familyOf_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyOf_length
/-- info: 'GoLean.SliceMem.familyOf_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyOf_range
/-- info: 'GoLean.SliceMem.familyOfZ_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyOfZ_range
/-- info: 'GoLean.SliceMem.familyOf_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyOf_succ
/-- info: 'GoLean.SliceMem.familyOf_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyOf_set
/-- info: 'GoLean.SliceMem.familyOf_getD' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyOf_getD
/-- info: 'GoLean.SliceMem.takePad_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.takePad_zero
/-- info: 'GoLean.SliceMem.takePad_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.takePad_length
/-- info: 'GoLean.SliceMem.takePad_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.takePad_range
/-- info: 'GoLean.SliceMem.takePad_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.takePad_set
/-- info: 'GoLean.SliceMem.takePad_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.takePad_full

-- WP arc s1 lift 3 (2026-08-16): the swap surgery + count algebra.
-- Transcribed verbatim from a fresh probe (`.tmp/pinprobe3.lean`
-- at the lift commit).
/-- info: 'GoLean.SliceMem.getD_set_self' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.getD_set_self
/-- info: 'GoLean.SliceMem.getD_set_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.getD_set_ne
/-- info: 'GoLean.SliceMem.count_set_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.count_set_add
/-- info: 'GoLean.SliceMem.swapList_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.swapList_length
/-- info: 'GoLean.SliceMem.getD_swapList_fst' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.getD_swapList_fst
/-- info: 'GoLean.SliceMem.getD_swapList_snd' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.getD_swapList_snd
/-- info: 'GoLean.SliceMem.getD_swapList_other' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.getD_swapList_other
/-- info: 'GoLean.SliceMem.count_swapList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.count_swapList
/-- info: 'GoLean.SliceMem.range_swapList' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.range_swapList

/-- info: 'GoLean.SliceMem.familyMod_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyMod_length
/-- info: 'GoLean.SliceMem.familyMod_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyMod_range
/-- info: 'GoLean.SliceMem.familyModZ_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyModZ_range
/-- info: 'GoLean.SliceMem.familyMod_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyMod_succ
/-- info: 'GoLean.SliceMem.familyMod_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyMod_set
/-- info: 'GoLean.SliceMem.familyMod_getD' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.familyMod_getD
/-- info: 'GoLean.SliceMem.prefixPad_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.SliceMem.prefixPad_zero
/-- info: 'GoLean.SliceMem.prefixPad_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.prefixPad_length
/-- info: 'GoLean.SliceMem.prefixPad_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.prefixPad_range
/-- info: 'GoLean.SliceMem.prefixPad_familyMod_set' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceMem.prefixPad_familyMod_set
/-- info: 'GoLean.SliceMem.prefixPad_full' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.SliceMem.prefixPad_full

/-! ## Frame/Threshold — the threshold shift/rebase layer (WP arc s1
lift 4, 2026-08-16: 17 public lemmas + the StepKit `lookup_append`
match form; `ρT`/`bumpAt`/`retiredFrame`/`CellFixed` are vocabulary
defs, unpinned). Transcribed verbatim from a fresh probe
(`.tmp/pinprobe4.lean` at the lift commit). -/
/-- info: 'GoLean.Surface.lookup_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.lookup_append
/-- info: 'GoLean.Frame.ρT_lt' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Frame.ρT_lt
/-- info: 'GoLean.Frame.ρT_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.ρT_ge
/-- info: 'GoLean.Frame.shiftSpec_ρT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.shiftSpec_ρT
/-- info: 'GoLean.Frame.ρT_zero_app' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.ρT_zero_app
/-- info: 'GoLean.Frame.base_ne_of_ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Frame.base_ne_of_ne
/-- info: 'GoLean.Frame.renameLoc_ρT_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.renameLoc_ρT_zero
/-- info: 'GoLean.Frame.renameValue_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.renameValue_id
/-- info: 'GoLean.Frame.renameCell_ρT_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.renameCell_ρT_zero
/-- info: 'GoLean.Frame.CellFixed.of_locFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.CellFixed.of_locFree
/-- info: 'GoLean.Frame.renameLoc_ρT_bump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.renameLoc_ρT_bump
/-- info: 'GoLean.Frame.retiredFrame_lookup_base_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.retiredFrame_lookup_base_none
/-- info: 'GoLean.Frame.retiredFrame_lookup_field' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Frame.retiredFrame_lookup_field
/-- info: 'GoLean.Frame.retiredFrame_lookup_index' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Frame.retiredFrame_lookup_index
/-- info: 'GoLean.Frame.retiredFrame_lookup_some_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.retiredFrame_lookup_some_inv
/-- info: 'GoLean.Frame.frameSim_seed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.frameSim_seed
/-- info: 'GoLean.Frame.rebaseSimT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.rebaseSimT
/-- info: 'GoLean.Frame.transfer_segT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.transfer_segT

/-! ## MapMem — map-in-memory vocabulary + executable op facts
(27 public lemmas; +11 in the GAP-P1 counting-fold lift and +3 in the
GAP-M1 choice-pick lift, 2026-08-15 — the `bump`/`countsFold`/
`nilMapCell` defs are unpinned like the other vocabulary defs) -/

/-- info: 'GoLean.MapMem.scan_generic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.scan_generic
/-- info: 'GoLean.MapMem.mapEntryIndex?_toEntries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.mapEntryIndex?_toEntries
/-- info: 'GoLean.MapMem.idxOf?_none_cnt' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.idxOf?_none_cnt
/-- info: 'GoLean.MapMem.idxOf?_none_setk' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.idxOf?_none_setk
/-- info: 'GoLean.MapMem.idxOf?_some_snd' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.idxOf?_some_snd
/-- info: 'GoLean.MapMem.idxOf?_some_setk' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.idxOf?_some_setk
/-- info: 'GoLean.MapMem.toEntries_getElem?' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.toEntries_getElem?
/-- info: 'GoLean.MapMem.toEntries_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.toEntries_size
/-- info: 'GoLean.MapMem.map_eraseIdx' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.map_eraseIdx
/-- info: 'GoLean.MapMem.toEntries_eraseIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.toEntries_eraseIdx
/-- info: 'GoLean.MapMem.setk_cnt_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.setk_cnt_succ
/-- info: 'GoLean.MapMem.countsFold_nil' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.MapMem.countsFold_nil
/-- info: 'GoLean.MapMem.countsFold_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.countsFold_append
/-- info: 'GoLean.MapMem.cnt_countsFold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.cnt_countsFold
/-- info: 'GoLean.MapMem.countsFold_key_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.countsFold_key_mem
/-- info: 'GoLean.MapMem.countsFold_nodup_keys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.countsFold_nodup_keys
/-- info: 'GoLean.MapMem.cnt_of_mem_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.cnt_of_mem_nodup
/-- info: 'GoLean.MapMem.cnt_pos_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.cnt_pos_mem
/-- info: 'GoLean.MapMem.countsFold_val_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.countsFold_val_le
/-- info: 'GoLean.MapMem.take_succ_getD' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.take_succ_getD
/-- info: 'GoLean.MapMem.cnt_take_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.cnt_take_le
-- (BUG-005 (L), 2026-08-19: the pick lemmas lost `Classical.choice` —
-- the live-cell candidates path is fully constructive.)
/-- info: 'GoLean.MapMem.stepFn_pick_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.stepFn_pick_bind
/-- info: 'GoLean.MapMem.stepFn_pick_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.stepFn_pick_value
/-- info: 'GoLean.MapMem.stepFn_pick_novars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.stepFn_pick_novars
/-- info: 'GoLean.MapMem.applyStrictOp_mapGet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.applyStrictOp_mapGet
/-- info: 'GoLean.MapMem.mapAssignValue_toEntries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.mapAssignValue_toEntries
-- (BUG-005 (L), 2026-08-19: `snapshot_toEntries` retired with the
-- snapshot step; the live-pick kit surface replaces it.)
/-- info: 'GoLean.MapMem.rangeStart_toEntries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.rangeStart_toEntries
/-- info: 'GoLean.MapMem.candidates_toEntries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.candidates_toEntries
/-- info: 'GoLean.MapMem.mandatory_toEntries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.mandatory_toEntries
/-- info: 'GoLean.MapMem.mandatory_true_of_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.mandatory_true_of_all
/-- info: 'GoLean.MapMem.filter_push_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.filter_push_key
/-- info: 'GoLean.MapMem.stepFn_iter_done' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.stepFn_iter_done

/-! ## MapLoops — the map-loop schemas (7 public lemmas; the GAP-C1
counting-loop lift + the GAP-R1 pick-loop lift, 2026-08-15) -/

/-- info: 'GoLean.MapLoops.mapCountIter_generic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapLoops.mapCountIter_generic
/-- info: 'GoLean.MapLoops.mapCountIter_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapLoops.mapCountIter_at
/-- info: 'GoLean.MapLoops.mapCountLoop_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapLoops.mapCountLoop_generic
/-- info: 'GoLean.MapLoops.consume_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapLoops.consume_lt
/-- info: 'GoLean.MapLoops.eraseIdx_length_of_lt' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapLoops.eraseIdx_length_of_lt
/-- info: 'GoLean.MapLoops.mem_of_mem_eraseIdx' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapLoops.mem_of_mem_eraseIdx
/-- info: 'GoLean.MapLoops.mapPickLoop_generic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapLoops.mapPickLoop_generic

/-! ## FuelMeasure — the termination/composition kit incl. the P5 iteration schema (18 public lemmas) -/

/-- info: 'GoLean.Surface.CompletesIn.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.CompletesIn.mono
/-- info: 'GoLean.Surface.terminates_of_completesIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.terminates_of_completesIn
/-- info: 'GoLean.Surface.execStmtLoop_of_stepFnIter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.execStmtLoop_of_stepFnIter
/-- info: 'GoLean.Surface.completesIn_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.completesIn_comp
/-- info: 'GoLean.Surface.completesIn_measure_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.completesIn_measure_loop
/-- info: 'GoLean.Surface.completesIn_next_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.completesIn_next_stop
/-- info: 'GoLean.Surface.execStmtLoop_next_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.execStmtLoop_next_stop
/-- info: 'GoLean.Surface.normal_readout_of_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.normal_readout_of_total
/-- info: 'GoLean.Surface.runConfig_unfold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runConfig_unfold
/-- info: 'GoLean.Surface.runConfig_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runConfig_step
/-- info: 'GoLean.Surface.runConfig_of_stepFnIter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runConfig_of_stepFnIter
/-- info: 'GoLean.Surface.runConfig_next_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runConfig_next_stop
/-- info: 'GoLean.Surface.runConfig_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runConfig_mono
/-- info: 'GoLean.Surface.runFunctionWithContextM_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runFunctionWithContextM_mono
/-- info: 'GoLean.Surface.harness_readout_of_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.harness_readout_of_total
/-- info: 'GoLean.Surface.stepFnIter_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFnIter_chain
/-- info: 'GoLean.Surface.stepFnIter_iterate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFnIter_iterate
/-- info: 'GoLean.Surface.stepFnIter_iterate_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFnIter_iterate_exit
-- WP arc s5 item 3 (2026-08-18): the loop-guard bridge every counted-loop
-- instantiation needs (the 79-site `decide_eq_true (by exact_mod_cast …)`
-- idiom, lifted after the go_iterate TACTIC was trimmed). Transcribed
-- verbatim from a fresh probe (`.tmp/pinprobe13.lean`) — the set is
-- [propext] ALONE, smaller than its neighbours here; do not copy a
-- neighbour's trio (the S4.11 stale-pin lesson).
/-- info: 'GoLean.Surface.decide_natCast_lt_true' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.decide_natCast_lt_true
-- WP arc s1 lift 5 (2026-08-16): the two-exit loop schema.
-- Transcribed verbatim from a fresh probe (`.tmp/pinprobe5.lean`).
/-- info: 'GoLean.Surface.stepFnIter_iterate_bail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFnIter_iterate_bail
-- WP arc s1.5b (2026-08-18): the relational/measure-indexed two-exit
-- schema (twosum's variable row costs, bubble's frame-interleaved
-- existential states). Fresh probe: `.tmp/pinprobe6.lean`.
/-- info: 'GoLean.Surface.stepFnIter_iterate_bail_rel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFnIter_iterate_bail_rel

/-! ## The derive_entry_eq emitted-theorem fixtures (all 10 landed entry equations) -/

/-- info: 'GoLean.Examples.Fib.fibH_entry_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Fib.fibH_entry_eq
/-- info: 'GoLean.Examples.Gcd.gcdh_entry_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Gcd.gcdh_entry_eq
/-- info: 'GoLean.Examples.MinMax.mmh_entry_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MinMax.mmh_entry_eq
/-- info: 'GoLean.Examples.Reverse.revH_entry_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Reverse.revH_entry_eq
/-- info: 'GoLean.Examples.InsertionSort.iharness_entry_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.InsertionSort.iharness_entry_eq
/-- info: 'GoLean.Examples.WordCount.wcH_entry_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordCount.wcH_entry_eq
/-- info: 'GoLean.Examples.BinSearch.harness_entry_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.BinSearch.harness_entry_eq
/-- info: 'GoLean.Examples.MinMax.rH_entry_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.MinMax.rH_entry_eq
/-- info: 'GoLean.Examples.Reverse.revHV_entry_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.Reverse.revHV_entry_eq
/-- info: 'GoLean.Examples.WordCount.rH_entry_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.WordCount.rH_entry_eq

/-! ### WP arc slice 4 (mirror symbolic evaluator, phase 2): the
public Sym surface, per the design §8 Kit-pin convention — THE MASTER
WALK (`stepFn'_conc`), its two gated instances (**THE DRIFT THEOREM**
`stepFn'_concrete_agrees`, charter :80-83 in the ruled OQ3 spelling;
the symbolic per-step `stepFnS_sound`), **THE REFINEMENT THEOREM**
(`symEvalWindow_refines`, charter :89), and the Kadane non-vacuity
witness (`kd_su_A0_via_sym`, ruled OQ4 — statement byte-identical to
the shipped `kd_su_A0_raw`, now discharged through the refinement
theorem; phase 1's bespoke spike route is retired, log unit S4.8).
Phase 3 adds the PROJECTION corollary `symEvalWindow_refines'` (the
emission-seam spelling: the transported RHS is the run's own output,
so a window discharge writes only the INPUT fixture; first consumers =
the matmul blocked-segment transports, `Examples/MatMul.lean`, log
unit S4.11). -/

/-- info: 'GoLean.Sym.stepFn'_conc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.stepFn'_conc
/-- info: 'GoLean.Sym.stepFn'_concrete_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.stepFn'_concrete_agrees
/-- info: 'GoLean.Sym.stepFnS_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.stepFnS_sound
/-- info: 'GoLean.Sym.symEvalWindow_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.symEvalWindow_refines
/-- info: 'GoLean.Sym.symEvalWindow_refines'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.symEvalWindow_refines' 
/-- info: 'GoLean.Sym.Spike.kd_su_A0_via_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.Spike.kd_su_A0_via_sym

/-! ### Campaign Arc 4, A4-U2 (the handler-fragment extension,
`Sym/TableExt.lean`): the table-conditioned surface — the extended
step's transport (`stepFnT_conc`, delegating to the shipped master
walk on every non-overridden arm), its symbolic instance, the
table-conditioned refinement pair (the shipped template + the ONE
`SubTable` premise), the store-chain drift heads, and the slice-2
sync apply. Witnesses: `HandlerEqSym` (store window at the pinned
tables) and `syncWit_refines` (lock/unlock window, in-module). -/

/-- info: 'GoLean.Sym.stepFnT_conc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.stepFnT_conc
/-- info: 'GoLean.Sym.stepFnST_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.stepFnST_sound
/-- info: 'GoLean.Sym.symEvalWindowT_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.symEvalWindowT_refines
/-- info: 'GoLean.Sym.symEvalWindowT_refines'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.symEvalWindowT_refines'
/-- info: 'GoLean.Sym.normalizeFuelT_conc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.normalizeFuelT_conc
/-- info: 'GoLean.Sym.storeTargetT_conc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.storeTargetT_conc
/-- info: 'GoLean.Sym.applySyncOp_conc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.applySyncOp_conc
/-- info: 'GoLean.Sym.syncWit_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.syncWit_refines
/-- info: 'GoLean.Sym.enterFrameT_conc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.enterFrameT_conc
/-- info: 'GoLean.Sym.stepFnTB_conc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.stepFnTB_conc
/-- info: 'GoLean.Sym.symEvalWindowTB_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.symEvalWindowTB_refines
/-- info: 'GoLean.Sym.symEvalWindowTB_refines'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.symEvalWindowTB_refines'
/-- info: 'GoLean.Sym.stepFn_pick_generic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.stepFn_pick_generic
/-- info: 'GoLean.Sym.stepFnIter_window_pick_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.stepFnIter_window_pick_window

/-! A4-U3 residual lifts (same lever, found by the becomeFollower
populated-fixture probe): defaultValue/equality at the input table
(`stepFnT` layer) and `toInterface` at the pack layer (canonicalTy
needs table equality). Exercised in-window by the U3 becomeFollower
spans in `HandlerEqSym`/`BfEquation`. -/

/-- info: 'GoLean.Sym.defaultValueFuelT_conc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.defaultValueFuelT_conc
/-- info: 'GoLean.Sym.valueEqBFuelT_conc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.valueEqBFuelT_conc
/-- info: 'GoLean.Sym.valueEqRT_conc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.valueEqRT_conc
/-- info: 'GoLean.Sym.canonicalTyFuel_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.canonicalTyFuel_types

end GoLean.Iris.Audit
