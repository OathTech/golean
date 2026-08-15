import Lean
import GoLeanProofs.StepKit
import GoLeanProofs.SliceMem
import GoLeanProofs.MapMem
import GoLeanProofs.MapLoops
import GoLeanProofs.FuelMeasure
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
/-- info: 'GoLean.Surface.storeTarget_addr' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.storeTarget_addr
/-- info: 'GoLean.Surface.stepFn_mapAssign_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_mapAssign_apply
/-- info: 'GoLean.Surface.stepFn_snapshot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_snapshot
/-- info: 'GoLean.Surface.natFromNonneg_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.natFromNonneg_cast

/-! ## SliceMem — slice-in-memory vocabulary + executable op facts
(28 public lemmas; +11 in the GAP-P2 family/prefix lift, 2026-08-15 —
the `familyMod`/`prefixPad` defs are unpinned like the other
vocabulary defs) -/

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
/-- info: 'GoLean.MapMem.stepFn_pick_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.stepFn_pick_bind
/-- info: 'GoLean.MapMem.stepFn_pick_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.stepFn_pick_value
/-- info: 'GoLean.MapMem.stepFn_pick_novars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.stepFn_pick_novars
/-- info: 'GoLean.MapMem.applyStrictOp_mapGet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.applyStrictOp_mapGet
/-- info: 'GoLean.MapMem.mapAssignValue_toEntries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapMem.mapAssignValue_toEntries
/-- info: 'GoLean.MapMem.snapshot_toEntries' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapMem.snapshot_toEntries

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

end GoLean.Iris.Audit
