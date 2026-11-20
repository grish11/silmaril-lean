module

public import Silmaril.Wasm.Game.HandleAccept.Families.Mixed.Defs
import Silmaril.Semantics.Accept.Host.Thms

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Families.Mixed

open Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Families.Mixed
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted

private theorem noAgreement {Tree : Type} {handle : BitVec 32} {tree : Tree} :
    Agrees none handle tree := fun _ impossible => by cases impossible

public theorem pair_accepted {Atom : Type} (first second : Atom) :
    SExp.ofList [.atom first, .atom second] ∈
      writerLang (sexpW Atom) {} {mixedPairTrace first second} := by
  apply Silmaril.Accept.Host.mem_lang.mpr
  refine ⟨_, rfl, _, _, .cons (WStep.writeOk (t := SExp.atom first) rfl ⟨by simp, .inl rfl⟩ noAgreement)
    (.cons (WStep.writeOk (t := SExp.atom second) rfl ⟨by simp, .inl rfl⟩ noAgreement)
    (.cons (WStep.writeOk (t := SExp.ofList [.atom first, .atom second]) rfl
      ⟨by simp, .inl rfl⟩ noAgreement)
    (.cons (WStep.acceptOk (Function.update_self _ _ _)) (.nil _)))), ?_⟩
  simp

public theorem hinted_cons_accepted : hintedConsTree ∈ writerLang (consW Hinted) {} {hintedConsTrace} := by
  apply Silmaril.Accept.Host.mem_lang.mpr
  refine ⟨_, rfl, _, _, .cons (WStep.writeOk (t := SExp2.atom hiabHinted) rfl ⟨by simp, .inl rfl⟩ noAgreement)
    (.cons (WStep.writeOk (t := SExp2.atom bareBlob) rfl ⟨by simp, .inl rfl⟩ noAgreement)
    (.cons (WStep.writeOk (t := SExp2.nil) rfl ⟨by simp, .inl rfl⟩ noAgreement)
    (.cons (WStep.writeOk (t := SExp2.cons (.atom bareBlob) .nil) rfl ⟨by simp, .inl rfl⟩ noAgreement)
    (.cons (WStep.writeOk (t := hintedConsTree) rfl ⟨by simp, .inl rfl⟩ noAgreement)
    (.cons (WStep.acceptOk (Function.update_self _ _ _)) (.nil _)))))), ?_⟩
  simp

end Silmaril.Proofs.Wasm.Game.HandleAccept.Families.Mixed
