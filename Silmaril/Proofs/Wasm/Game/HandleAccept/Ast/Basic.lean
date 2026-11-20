module

public import Silmaril.Wasm.Game.HandleAccept.Ast.Defs

/-! # Proofs: AST decoders and arities -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Ast

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers
  Silmaril.Wasm.Game.HandleAccept.Ast Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api

variable {S : WitSig} {ts : List FnType}

theorem astWDecAns_isWrite (ix : AstWImports S) (e : (ifaceSig ts).Op)
    (v : (ifaceSig ts).Ar e) (ev : AstWEv S) (h : astWDecAns ix e v = some ev) :
    ∃ op args r, ev = .write op args r := by
  unfold astWDecAns at h
  rcases hr : retI32 v with _ | r <;> simp only [hr, Option.bind_eq_bind, Option.bind_none,
    Option.bind_some, reduceCtorEq] at h
  rcases ht : ix.tagOf e.1.val with _ | t <;> simp only [ht, Option.bind_none,
    Option.bind_some, reduceCtorEq] at h
  rcases ho : ofVals? (S.params t) e.2.1 with _ | ⟨a, rest⟩ <;> simp only [ho, Option.bind_none,
    Option.bind_some, reduceCtorEq] at h
  rcases hc : i32Args rest with _ | cs <;> simp only [hc, Option.bind_none,
    Option.bind_some, reduceCtorEq] at h
  exact ⟨_, _, _, (Option.some.inj h).symm⟩

theorem astWDecAsk_isAccept (ix : AstWImports S) (e : (ifaceSig ts).Op) (ev : AstWEv S)
    (h : astWDecAsk ix e = some ev) : ∃ h, ev = .accept h := by
  unfold astWDecAsk at h
  split_ifs at h
  rcases ha : i32Arg e.2.1 with _ | k <;> simp [ha] at h
  exact ⟨k, h.symm⟩

theorem astW_writeClosed (op : Σ t, S.toAstSig.Arg t) (args : List (BitVec 32)) :
    WriteClosed (astW S.toAstSig) {x | AST.WellArity x} op args := by
  intro cs y _ hb hcs
  simp only [astW] at hb
  split_ifs at hb with hA
  cases hb
  obtain ⟨t, a⟩ := op
  exact ⟨hA, fun i => hcs _ (List.getElem_mem _)⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Ast
