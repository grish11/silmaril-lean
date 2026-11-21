module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnNested

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested

mutual
theorem rawType_layout : (type : PTy) → PTy.layout (rawType type) = PTy.layout type
  | .fixedList element length => by simp only [rawType, PTy.layout, rawType_layout element]
  | .record fields => by simp only [rawType, PTy.layout, rawFields_layout fields]
  | .tuple types => by simp only [rawType, PTy.layout, rawTypes_layout types]
  | .variant cases => by simp only [rawType, PTy.layout, rawCases_layout cases]
  | .option element => by simp only [rawType, PTy.layout, rawType_layout element]
  | .result ok error => by simp only [rawType, PTy.layout, rawOpt_layout ok, rawOpt_layout error]
  | .bool | .s32 | .u32 | .s64 | .u64 | .string | .list _ | .s8 | .u8 | .s16 | .u16 | .f32
  | .f64 | .char | .enum _ | .flags _ | .own _ | .borrow _ => rfl

theorem rawTypes_layout : (types : List PTy) → PTy.layouts (rawTypes types) = PTy.layouts types
  | [] => rfl
  | type :: types => by simp only [rawTypes, PTy.layouts, rawType_layout type, rawTypes_layout types]

theorem rawFields_layout : (fields : List (String × PTy)) →
    PTy.fieldLayouts (rawFields fields) = PTy.fieldLayouts fields
  | [] => rfl
  | (_, type) :: fields => by
    simp only [rawFields, PTy.fieldLayouts, rawType_layout type, rawFields_layout fields]

theorem rawCases_layout : (cases : List (String × Option PTy)) →
    PTy.caseLayouts (rawCases cases) = PTy.caseLayouts cases
  | [] => rfl
  | (_, type) :: cases => by
    simp only [rawCases, PTy.caseLayouts, rawOpt_layout type, rawCases_layout cases]

theorem rawOpt_layout : (type : Option PTy) → PTy.optLayout (rawOpt type) = PTy.optLayout type
  | none => rfl
  | some type => by simp only [rawOpt, PTy.optLayout, rawType_layout type]
end

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnNested
