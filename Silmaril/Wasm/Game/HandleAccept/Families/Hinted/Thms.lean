module

public import Silmaril.Wasm.Game.HandleAccept.Families.Matrix
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Families.Hinted

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Families

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Accept.Handle (Policy writerLang)
open Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted Silmaril.Wasm.Game.HandleAccept.MemSound.Tab

/-- The family table retains every write and acceptance from the dedicated hinted decoder. -/
theorem hinted_roles : tabRoles hintedTab {} = hintedRoles {} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Families.hinted_roles

private theorem hinted_writer_lang_eq (profile : Profile) (policy : Policy (BitVec 32)) :
    tabWriterLang profile (ReplyEnvs hiReply) 0 hintedSepMod hintedTab {} policy =
      hintedWriterLang profile (ReplyEnvs hiReply) 0 hintedSepMod {} policy := by
  unfold tabWriterLang tabTraces hintedWriterLang hintedTraces
  exact congrArg (fun roles => writerLang (sexpW Hinted) policy
    (inputsOf (some .enter) '' tagTraces profile (ReplyEnvs hiReply) 0 hintedSepMod roles)) hinted_roles

/-- Every writer policy admits the traced session calling the four-operand import. -/
theorem hinted_naryW_tagged_live (profile : Profile) (policy : Policy (BitVec 32)) :
    .atom hiabHinted ∈ tabWriterLang profile (ReplyEnvs hiReply) 0 hintedSepMod hintedTab {} policy := by
  rw [hinted_writer_lang_eq]
  exact hintedSep_live profile policy

/-- Exercise the actual four-operand import with separate hint and octet segments. -/
theorem hinted_naryW_tagged_lang (profile : Profile) {policy : Policy (BitVec 32)}
    (acceptDefined : policy.onAccept ≠ .ub) (writeDefined : policy.onWrite ≠ .ub) :
    tabWriterLang profile (ReplyEnvs hiReply) 0 hintedSepMod hintedTab {} policy =
      {.atom hiabHinted} :=
  (hinted_writer_lang_eq profile policy).trans (hintedSep_lang profile acceptDefined writeDefined)

/-- The same Wasm trace publishes the hinted value as a typed AST leaf. -/
theorem hinted_astW_tagged_lang (profile : Profile) {policy : Policy (BitVec 32)}
    (acceptDefined : policy.onAccept ≠ .ub) (writeDefined : policy.onWrite ≠ .ub) :
    tabAstWriterLang profile (ReplyEnvs hiReply) 0 hintedSepMod hintedTab {} policy =
      {SExp.toAST (.atom hiabHinted)} := by
  rw [tabAstWriterLang_eq acceptDefined writeDefined,
    hinted_naryW_tagged_lang profile acceptDefined writeDefined, Set.image_singleton]

end Silmaril.Wasm.Game.HandleAccept.Families
