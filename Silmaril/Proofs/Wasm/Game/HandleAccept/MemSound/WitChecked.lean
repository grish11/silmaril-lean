module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Checked.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitChecked

open Silmaril.Formats Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own

theorem lookupChecked_toOption (rt : RT) (resource : Nat) (handle : BitVec 32) :
    (lookupChecked rt resource handle).toOption = rt.lookup resource handle := by
  cases hentry : rt handle with
  | none => simp [lookupChecked, RT.lookup, hentry, Except.toOption]
  | some entry =>
    cases hlive : entry.live <;> by_cases htype : entry.ty = resource <;>
      simp [lookupChecked, RT.lookup, hentry, hlive, htype, Except.toOption]

theorem resolveFieldChecked_toOption (rt : RT) (type : PTy) (value : (ownRaw type).Val) :
    (resolveFieldChecked rt type value).toOption = resolve1 rt type value := by
  cases type <;> try rfl
  case own resource => exact lookupChecked_toOption rt resource value.toBitVec

theorem resolveFieldsChecked_toOption (rt : RT) : (types : List PTy) →
    (values : PTy.Vals (types.map ownRaw)) →
    (resolveFieldsChecked rt types values).toOption = resolveVals rt types values
  | [], _ => rfl
  | type :: types, (value, values) => by
    have hfield := resolveFieldChecked_toOption rt type value
    have hfields := resolveFieldsChecked_toOption rt types values
    cases hf : resolveFieldChecked rt type value <;>
      cases hs : resolveFieldsChecked rt types values <;>
      simp only [hf, hs, Except.toOption] at hfield hfields <;>
      simp [resolveFieldsChecked, resolveVals, hf, hs, ← hfield, ← hfields, Except.toOption,
        bind, pure, Except.bind, Except.pure, Option.map]

theorem resolveOpChecked_toOption (S : WitSig) (rt : RT) (raw : ROp S) :
    (resolveOpChecked S rt raw).toOption = resolveOp S rt raw := by
  have hfields := resolveFieldsChecked_toOption rt (S.params raw.1) raw.2
  cases hc : checkPTys .ownFields (S.params raw.1) with
  | error issue =>
    simp [resolveOpChecked, resolveOp, hc, Except.toOption, Except.mapError, bind, Except.bind]
  | ok admitted =>
    cases admitted
    by_cases hn : (movedOp S raw).Nodup
    · cases hv : resolveFieldsChecked rt (S.params raw.1) raw.2 <;>
        simp only [hv, Except.toOption] at hfields <;>
        simp [resolveOpChecked, resolveOp, hn, hc, hv, ← hfields, Except.toOption,
          Except.mapError, bind, pure, Except.bind, Except.pure, Option.map]
    · simp [resolveOpChecked, resolveOp, hn, hc, Except.toOption, Except.mapError, bind, Except.bind]
      rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitChecked
