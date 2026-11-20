module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Fragments.Thms

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Fragments

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Game.HandleAccept.Wit

def scalarCalcSig : ScalarSig where
  Tag := CalcTag
  params
    | .num => [⟨.s64, by decide⟩]
    | .add => []
  arity := calcSig.arity

/-- The existing module, proofs and accepted language are unchanged under this restriction. -/
theorem scalarCalcSig_embed : scalarCalcSig.toWitSig = calcSig :=
  congrArg (fun params => WitSig.mk CalcTag params calcSig.arity) (funext fun tag => by cases tag <;> rfl)

def compoundGlyphSig : CompoundSig where
  Tag := GlyphTag
  params
    | .glyph => [.record [("ch", .char), ("size", .option .u8)]]
    | .pair => []
  arity := glyphSig.arity

/-- The existing compound example needs no separate AST or decoder. -/
theorem compoundGlyphSig_embed : compoundGlyphSig.toWitSig = glyphSig :=
  congrArg (fun params => WitSig.mk GlyphTag params glyphSig.arity) (funext fun tag => by cases tag <;> rfl)

theorem string_is_not_scalar : ScalarType.ofPrimitive .string = none := rfl

theorem resource_is_not_compound : CompoundType.ofPayload (.own 7) = none := rfl

theorem resource_field_is_structural :
    (CompoundType.record [("handle", .own 7)]).toWit =
      (.record [("handle", .own 7)] : WIT.ClosedType Nat) := rfl

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Fragments
