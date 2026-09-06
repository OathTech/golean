import GoLean.GoCore.RecoveryControl

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem ReturnCont.mono {world next fs k} (h : ReturnCont world fs k)
    (ext : Extends world next) : ReturnCont next fs k := by
  induction h using ReturnCont.rec (motive_2 := fun k _ => ExitCont next fs k) with
  | seq he hs _ ih => exact .seq (he.mono ext) hs ih
  | frame he hp hr hd _ _ ih ihw =>
    exact .frame (he.mono ext) hp (hr.mono ext) (hd.mono ext) ih ihw
  | stop => exact .stop
  | stmt _ ih => exact .stmt ih
  | resume hc _ ih => exact .resume hc ih

theorem ExitCont.mono {world next fs k} (h : ExitCont world fs k)
    (ext : Extends world next) : ExitCont next fs k := by
  induction h using ExitCont.rec (motive_1 := fun k _ => ReturnCont next fs k) with
  | seq he hs _ ih => exact .seq (he.mono ext) hs ih
  | frame he hp hr hd _ _ ih ihw =>
    exact .frame (he.mono ext) hp (hr.mono ext) (hd.mono ext) ih ihw
  | stop => exact .stop
  | stmt _ ih => exact .stmt ih
  | resume hc _ ih => exact .resume hc ih

theorem ValueCont.mono {world next fs kind k} (h : ValueCont world fs kind k)
    (ext : Extends world next) : ValueCont next fs kind k := by
  induction h with
  | coerce hi _ ih => exact .coerce hi ih
  | strict he ho hd hp _ ih => exact .strict (he.mono ext) ho (hd.mono ext) hp ih
  | and he hr _ ih => exact .and (he.mono ext) hr ih
  | or he hr _ ih => exact .or (he.mono ext) hr ih
  | bool _ ih => exact .bool ih
  | branch he ht hf nt nf hk => exact .branch (he.mono ext) ht hf nt nf (hk.mono ext)
  | target he ht hr hp hs hk =>
    exact .target (he.mono ext) ht (hr.mono ext) hp (hs.mono ext) (hk.mono ext)
  | rhs he hr hd hp hk => exact .rhs (he.mono ext) (hr.mono ext) (hd.mono ext) hp (hk.mono ext)
  | callArgs he hf ha hd hp ht hk =>
    exact .callArgs (he.mono ext) hf ha (hd.mono ext) hp ht (hk.mono ext)
  | callCallee he hf ha hp ht hk => exact .callCallee (he.mono ext) hf ha hp ht (hk.mono ext)
  | callValueArgs he hf ha hc hd hp ht hk =>
    exact .callValueArgs (he.mono ext) hf ha (hc.mono ext) (hd.mono ext) hp ht (hk.mono ext)
  | deferCallee he hf ha hp hk => exact .deferCallee (he.mono ext) hf ha hp (hk.mono ext)
  | deferArgs he hf ha hc hd hp hk =>
    exact .deferArgs (he.mono ext) hf ha (hc.mono ext) (hd.mono ext) hp (hk.mono ext)
  | panic hk => exact .panic (hk.mono ext)

theorem UnwindCont.mono {world next fs k} (h : UnwindCont world fs k)
    (ext : Extends world next) : UnwindCont next fs k := by
  cases h with
  | exit h => exact .exit (h.mono ext)
  | value h => exact .value (h.mono ext)

theorem Control.mono {world next fs c} (h : Control world fs c)
    (ext : Extends world next) : Control next fs c := by
  cases h with
  | next h => exact .next (h.mono ext)
  | execNeutral he hs hn hk => exact .execNeutral (he.mono ext) hs hn (hk.mono ext)
  | execFrame he hs hk => exact .execFrame (he.mono ext) hs (hk.mono ext)
  | execSeq he hs ht hk => exact .execSeq (he.mono ext) hs ht (hk.mono ext)
  | eval he hx hk => exact .eval (he.mono ext) hx (hk.mono ext)
  | ret hv hk => exact .ret (hv.mono ext) (hk.mono ext)
  | store he hr hv hk => exact .store (he.mono ext) (hr.mono ext) (hv.mono ext) (hk.mono ext)
  | returning hk => exact .returning (hk.mono ext)
  | panicking hc hk => exact .panicking hc (hk.mono ext)

end GoLean.GoCore.RecoveryRuntime
