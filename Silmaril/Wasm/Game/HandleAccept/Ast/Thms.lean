module

public import Silmaril.Wasm.Game.HandleAccept.Ast.Defs
public import Silmaril.Wasm.Game.HandleAccept.Writer.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Ast.Basic

/-!
# Tagged-AST APIs of core Wasm modules: laws

* `moduleAstWLang_wellArity`: every tree a module accepts through an AST writer API is
  well-arity (`AST.WellArity`), for every module, profile and policy without UB, with no
  obligation: the generic writer `astW` checks arities, and closed writes bound the language
  (`writerLang_subset_of_closed`);
* `astWLang_sound_of_gameSat`: the writer bridge (`writerLang_subset_of_AG`) for AST writer
  modules;
* `astDecAns_ne_accept`, `astLang_sound_of_gameSat`, `astLang_sound_of_forall`: the reader
  bridge (`readerLang_subset_of_AG`) for AST reader modules.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Ast

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers
open Silmaril.Wasm.Logic.GameLink (GameSat)

variable {S : WitSig}

/-! ## Writer -/

/-- **AST writer modules accept only well-arity trees.** -/
theorem moduleAstWLang_wellArity {P : Profile} {m : Module} {ix : AstWImports S}
    {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    moduleAstWLang P m ix pol ⊆ {x | AST.WellArity x} :=
  writerLang_subset_of_closed ha hw fun _ _ op args _ _ =>
    Silmaril.Proofs.Wasm.Game.HandleAccept.Ast.astW_writeClosed op args

/-- **Soundness of an AST writer module** from its Hoare-logic obligation in every fixed
environment (store semantics, no UB). -/
theorem astWLang_sound_of_gameSat {P : Profile} {m : Module} {ix : AstWImports S}
    {pol : Policy (BitVec 32)} {L : Set (AST S.toAstSig)} {Inv : Store Nat → Prop}
    (hm : ∀ ρ, GameSat P (Verify.instOf m) Inv
      (writerISpec (astW S.toAstSig) pol.sentinel (astWDecAsk ix) (astWDecAns ix) ρ L)
      (topISpec _))
    (hs : Inv (Verify.instOf m).store) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    moduleAstWLang P m ix pol ⊆ L :=
  writerLang_subset_of_AG
    (fun ρ _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound (hm ρ) hs hp).2)
    (Silmaril.Proofs.Wasm.Game.HandleAccept.Ast.astWDecAsk_isAccept ix)
    (Silmaril.Proofs.Wasm.Game.HandleAccept.Ast.astWDecAns_isWrite ix) hw ha

/-! ## Reader -/

theorem astDecAns_ne_accept {ts : List FnType} (ix : AstRImports S) (e : (ifaceSig ts).Op)
    (v : (ifaceSig ts).Ar e) (h : BitVec 32) : astDecAns ix e v ≠ some (.accept h) := by
  unfold astDecAns
  cases astDecRead ix e v <;> simp

/-- **Soundness of an AST reader checker from its Hoare-logic obligation.** -/
theorem astLang_sound_of_gameSat {P : Profile} {m : Module} {ix : AstRImports S}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST S.toAstSig)} {L : Set (AST S.toAstSig)}
    {Inv : Store Nat → Prop}
    (hm : GameSat P (Verify.instOf m) Inv (astISpec ix ρ L) (topISpec _))
    (hs : Inv (Verify.instOf m).store) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    moduleAstLang P m ix .trap oa {ρ} ⊆ L :=
  readerLang_subset_of_AG
    (fun _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound hm hs hp).2)
    (fun _ _ h => h) (fun _ h hd hpre => hpre h hd)
    (astDecAns_ne_accept ix) hoa

/-- For every environment of a set. -/
theorem astLang_sound_of_forall {P : Profile} {m : Module} {ix : AstRImports S}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (AST S.toAstSig))}
    {L : Set (AST S.toAstSig)} {Inv : Store Nat → Prop}
    (hm : ∀ ρ ∈ Envs, GameSat P (Verify.instOf m) Inv (astISpec ix ρ L) (topISpec _))
    (hs : Inv (Verify.instOf m).store) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    moduleAstLang P m ix .trap oa Envs ⊆ L := fun _ hx => by
  obtain ⟨⟨ρ, hρ⟩, hx⟩ := Silmaril.Accept.mem_langOver.1 hx
  exact astLang_sound_of_gameSat (hm ρ hρ) hs hoa (Silmaril.Accept.mem_langOver.2 ⟨⟨ρ, rfl⟩, hx⟩)

end Silmaril.Wasm.Game.HandleAccept.Ast
