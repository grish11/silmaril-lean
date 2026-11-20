module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Ast.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.AstLive

/-!
# The tagged-node (AST) writer through linear memory: soundness and non-vacuity

**Bridges** (`astFixedLang_subset`, `astWriterLang_subset`): the generic role bridges
`rolesFixedLang_subset`, `rolesWriterLang_subset` at the AST roles `astRoles` (accepts at calls,
`tag(tagptr, taglen, children, n)` writes at answers) and the writer `astW strSig`.

**The example `astMod`** (`tag(16, 1, 0, 0)` over the name `a`, the handle stored at `[0, 4)`,
`tag(16, 1, 0, 1)` over the name `f` and that one child handle, `accept`), for every profile,
against every environment admitted by `hiReply`:

* `astMod_fixed_sound`: in every fixed environment and for every policy without a sentinel, it
  accepts only `f(a)`;
* `astMod_sound`: the same for the writer language (no sentinel, no undefined behaviour);
* `astMod_live`: it accepts `f(a)`, for every policy (traced session against the counting host);
* `astMod_lang`: **its writer language is exactly `{f(a)}`** (no sentinel, no undefined
  behaviour).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Ast

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.IO Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Cons Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api

variable {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat} {m : Module}

/-- **The AST writer bridge in a fixed environment**, for every policy. -/
theorem astFixedLang_subset {ix : AstImports} {pol : Policy (BitVec 32)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST strSig)} {L : Set (AST strSig)}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : MemSat P m memIdx (astRoles ix)
      (roleWriterContract (astRoles ix) (astW strSig) pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) :
    fixedLang (astW strSig) pol {ρ} (astTraces P Envs memIdx m ix) ⊆ L :=
  rolesFixedLang_subset
    (fun _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast.astAccept_isAccept h)
    (fun _ _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast.astWrite_isWrite h)
    hsat hE

/-- **The AST writer bridge** (store semantics, no undefined behaviour). -/
theorem astWriterLang_subset {ix : AstImports} {pol : Policy (BitVec 32)}
    {L : Set (AST strSig)} {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (astRoles ix)
      (roleWriterContract (astRoles ix) (astW strSig) pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : astWriterLang P Envs memIdx m ix pol ⊆ L :=
  rolesWriterLang_subset
    (fun _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast.astAccept_isAccept h)
    (fun _ _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast.astWrite_isWrite h)
    hsat hE hw ha

/-- **In a fixed environment, `astMod` accepts only `f(a)`.** -/
theorem astMod_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST strSig)) :
    fixedLang (astW strSig) pol {ρ} (astTraces P (ReplyEnvs hiReply) 0 astMod {}) ⊆ {faTree} :=
  astFixedLang_subset
    (by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast.ast_sat P ρ)
    (fun _ _ h => h)

/-- **`astMod` accepts only `f(a)`.** -/
theorem astMod_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    astWriterLang P (ReplyEnvs hiReply) 0 astMod {} pol ⊆ {faTree} :=
  astWriterLang_subset
    (fun ρ => by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast.ast_sat P ρ)
    (fun _ _ h => h) hw ha

/-- **`astMod` accepts `f(a)`**, for every policy. -/
theorem astMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    faTree ∈ astWriterLang P (ReplyEnvs hiReply) 0 astMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Ast.astMod_live P pol

/-- **The writer language of `astMod` is exactly `{f(a)}`.** -/
theorem astMod_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    astWriterLang P (ReplyEnvs hiReply) 0 astMod {} pol = {faTree} :=
  Set.Subset.antisymm (astMod_sound P hs hw ha)
    (Set.singleton_subset_iff.2 (astMod_live P pol))

end Silmaril.Wasm.Game.HandleAccept.MemSound.Ast
