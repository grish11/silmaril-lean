module

public import Silmaril.Wasm.Abstract.Closing.Thms

/-!
# The closed call oracle against Core 3.0 (proofs)

`closedCall s a us (s', fl)` relates a direct call of the function at `a` on
the parameter-order arguments `us` to the store it ends in and its raw body
flow `fl`, top-first. Read through the exit flow it is a Core 3.0 run of
`invoke s a us` to a result with that store (`closedCall_core_iff`), and its
absence is Core divergence (`closedCall_none_iff_diverges`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Closing

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

/-- The closed call relation read through the exit flow. -/
theorem closedCall_exit_iff {s : Store H} {a : Nat} {us : List Val} {s' : Store H} {fl : Flow} :
    (∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (bfl : Flow),
      s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      closedCall s a us (s', bfl) ∧ exitFlow rs.length bfl = some fl) ↔
      ClosedOutcome s a us s' fl := by
  constructor
  · rintro ⟨fi, ps, rs, bfl, hfi, hty, hC, hx⟩
    rw [closedCall_fixpoint] at hC
    obtain ⟨fi', fn, ps', rs', f₂, hfi', hc, hty', d⟩ := hC
    obtain rfl : fi = fi' := Option.some.inj (hfi.symm.trans hfi')
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
    exact ⟨fi, fn, ps, rs, f₂, bfl, hfi, hc, hty, d, hx⟩
  · rintro ⟨fi, fn, ps, rs, f₂, bfl, hfi, hc, hty, d, hx⟩
    refine ⟨fi, ps, rs, bfl, hfi, hty, ?_, hx⟩
    rw [closedCall_fixpoint]
    exact ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, d⟩

theorem closedCall_core_iff {s : Store H} {a : Nat} {us : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a us) (P : Numerics.Profile) (r : Result) (s' : Store H) :
    (∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (bfl fl : Flow),
      s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      closedCall s a us (s', bfl) ∧ exitFlow rs.length bfl = some fl ∧
      flowBeh fl = some r.toBehaviour) ↔
      ∃ c : Config H, Steps P closedHost (invoke s a us) c ∧ c.code = r.toAdmin ∧ c.store = s' := by
  rw [core_result_iff_closed hs hF hS hok P r s']
  constructor
  · rintro ⟨fi, ps, rs, bfl, fl, hfi, hty, hC, hx, hb⟩
    exact ⟨fl, closedCall_exit_iff.mp ⟨fi, ps, rs, bfl, hfi, hty, hC, hx⟩, hb⟩
  · rintro ⟨fl, hco, hb⟩
    obtain ⟨fi, ps, rs, bfl, hfi, hty, hC, hx⟩ := closedCall_exit_iff.mpr hco
    exact ⟨fi, ps, rs, bfl, fl, hfi, hty, hC, hx, hb⟩

theorem closedCall_none_iff_diverges {s : Store H} {a : Nat} {us : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a us) (P : Numerics.Profile) :
    (∀ (fi : FuncInst H) (ps rs : List Validation.CValType) (s' : Store H) (bfl : Flow),
      s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
      closedCall s a us (s', bfl) → exitFlow rs.length bfl = none) ↔
      Diverges P closedHost (invoke s a us) := by
  rw [diverges_iff_no_closedOutcome hs hF hS hok P]
  constructor
  · intro h s' fl hco
    obtain ⟨fi, ps, rs, bfl, hfi, hty, hC, hx⟩ := closedCall_exit_iff.mpr hco
    rw [h fi ps rs s' bfl hfi hty hC] at hx
    cases hx
  · intro h fi ps rs s' bfl hfi hty hC
    rcases hx : exitFlow rs.length bfl with _ | fl
    · rfl
    · exact (h s' fl (closedCall_exit_iff.mp ⟨fi, ps, rs, bfl, hfi, hty, hC, hx⟩)).elim

end Silmaril.Proofs.Wasm.Abstract.Closing
