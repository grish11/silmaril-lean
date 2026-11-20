module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast

/-!
# Proofs: `astMod` accepts the node `f(a)`

Against the counting host `countEnv hiOut` started at `q` (it answers `tag` with the next handle,
`accept` with nothing, in the caller's store), the traced session of `astMod` invokes `run` and
runs its body to `accept(q + 1)`: `tag(16, 1, 0, 0)` observes `61` and no children (handle `q`),
the module stores `q` at `[0, 4)` and `66` at `16`, and `tag(16, 1, 0, 1)` observes the name `f`
and the child handle `q` (handle `q + 1`). Its writer trace is
`[enter, write a [] q, write f [q] (q + 1), accept (q + 1)]`, which accepts `f(a)` in the store
semantics when neither handle is the policy's sentinel.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Ast

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Ast
  Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
open Silmaril.Wasm.Logic.Core (bytesAt)

theorem astSpec_some : (Silmaril.Wasm.Verify.specInstance? astMod).isSome = true := by
  decide +kernel

theorem astMem : memSizes astMod = [65536] := by decide +kernel

theorem hiOut_shape (k : Nat) (q : BitVec 32) : hiShape k (hiOut k q) := by
  rcases k with _ | _ | k <;> simp [hiShape, hiOut]

/-- **The writer trace of the session.** -/
theorem ast_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write ⟨"a", ()⟩ [] q, .write ⟨"f", ()⟩ [q] (q + 1), .accept (q + 1)] ∈
      astTraces P (ReplyEnvs hiReply) 0 astMod {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists astSpec_some
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := ast_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page astMem hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, hD⟩ := fnOk_spec h2
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hfs : ∀ s : Store Nat, s.funcs = c.store.funcs → s.funcs[0]? = some f₀ ∧
      s.funcs[1]? = some f₁ ∧ s.funcs[2]? = some f₂ := by
    intro s h; rw [h, hf]; exact ⟨rfl, rfl, rfl⟩
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  let L := countEnv hiOut
  let R := astRoles {}
  have t₀ : TSession P L astMod (some 0) R c q Is.addrs .inst false (c, q) [] := .start
  have hok : InvokeOk c.store 2 [] := ⟨f₂, ps, rs, (hfs _ rfl).2.2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 2 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  -- enter `run`
  have st₀ : Step P NH (invoke c.store 2 [])
      ⟨c.store, {}, [.frame 0 (Frame.forCall f₂.module [] [.i32])
        [.label 0 [] (expression astBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[2]?.map FuncInst.type).getD default)) (vs := [])
      (a := 2) (fi := f₂) (code := code) trivial (hfs _ rfl).2.2 he (by rw [hps]; rfl) hcode2
    rw [hrs, hloc, hbody] at h
    exact h
  have hFf : (Frame.forCall f₂.module [] [.i32]).module.funcs = [0, 1, 2] := by
    simp [Frame.forCall, hfuncs]
  have hFm : (Frame.forCall f₂.module [] [.i32]).module.mems = [0] := by
    simp [Frame.forCall, hmems2]
  have hFl : (Frame.forCall f₂.module [] [.i32]).locals = astD := by
    simp [Frame.forCall, hD]
  generalize Frame.forCall f₂.module [] [.i32] = F at st₀ hFf hFm hFl
  let F₁ := F.setLocal ⟨0⟩ (.i32 q)
  -- "a" at 16
  obtain ⟨b₁, hst₁⟩ := store_some (B := mi.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i8.width / 8) ((0x61 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  have hz₁ : b₁.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₁).trans hsize
  let mi₁ : MemInst := { mi with bytes := b₁ }
  let s₁ := c.store.setMem 0 mi₁
  obtain ⟨hm₁, hl₁, hf₁⟩ := setMem_mems (mi := mi₁) hml
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression astBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (astBody.drop 3))]]⟩ :=
    step_body (step_mid [] _ (step_storePack hFm hmi hst₁))
  -- tag(16, 1, 0, 0)
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (astBody.drop 3))]]⟩
      ⟨s₁, {}, (bodyCtx F (expression (astBody.drop 8))).fill
        (vals [.i32 16, .i32 1, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 16, .i32 1, .i32 0, .i32 0] (expression (astBody.drop 8))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) (hfs _ hf₁).1))
  have hd₁ : decompose? s₁ ((bodyCtx F (expression (astBody.drop 8))).fill
      (vals [.i32 16, .i32 1, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (astBody.drop 8)), 0, 0, [.i32 16, .i32 1, .i32 0, .i32 0]) :=
    decompose_fill _ trivial (hfs _ hf₁).1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    (((st₀.steps.trans st₁.steps).trans st₂.steps))) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  -- local.set 0; the handle at 0
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (astBody.drop 8))).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (astBody.drop 9))]]⟩ :=
    step_body (step_mid [] (expression (astBody.drop 9))
      (step_localSet (x := ⟨0⟩) (v := .i32 q) (by simp [hFl, astD, Idx.toNat])))
  have hv₀ : F₁.local? ⟨0⟩ = some (some (.i32 q)) := by
    simp [F₁, Frame.local?, Frame.setLocal, hFl, astD, Idx.toNat]
  have hF₁m : F₁.module.mems = [0] := hFm
  have hF₁f : F₁.module.funcs = [0, 1, 2] := hFf
  have st₄ : Step P NH
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (astBody.drop 9))]]⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [.i32 0] ++ [(Val.i32 q).toAdmin] ++
        expression (astBody.drop 11))]]⟩ :=
    step_body (step_mid [.i32 0] (expression (astBody.drop 11)) (step_localGet hv₀))
  obtain ⟨b₂, hst₂⟩ := store_some (B := mi₁.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i32.width / 8) (q.setWidth _) (by rw [hz₁]; decide)
  have hz₂ : b₂.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₂).trans hz₁
  let mi₂ : MemInst := { mi₁ with bytes := b₂ }
  let s₂ := s₁.setMem 0 mi₂
  obtain ⟨hm₂, hl₂, hf₂⟩ := setMem_mems (s := s₁) (mi := mi₂) hl₁
  have st₅ : Step P NH
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [.i32 0] ++ [(Val.i32 q).toAdmin] ++
        expression (astBody.drop 11))]]⟩
      ⟨s₂, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (astBody.drop 12))]]⟩ :=
    step_body (step_mid [] (expression (astBody.drop 12)) (step_store32 hF₁m hm₁ hst₂))
  -- "f" at 16
  obtain ⟨b₃, hst₃⟩ := store_some (B := mi₂.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i8.width / 8) ((0x66 : BitVec 32).setWidth _) (by rw [hz₂]; decide)
  have hz₃ : b₃.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₃).trans hz₂
  let mi₃ : MemInst := { mi₂ with bytes := b₃ }
  let s₃ := s₂.setMem 0 mi₃
  obtain ⟨-, hl₃, hf₃⟩ := setMem_mems (s := s₂) (mi := mi₃) hl₂
  have st₆ : Step P NH
      ⟨s₂, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (astBody.drop 12))]]⟩
      ⟨s₃, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (astBody.drop 15))]]⟩ :=
    step_body (step_mid [] (expression (astBody.drop 15)) (step_storePack hF₁m hm₂ hst₃))
  -- tag(16, 1, 0, 1)
  have hs₃f := hfs s₃ (hf₃.trans (hf₂.trans hf₁))
  have st₇ : Step P NH
      ⟨s₃, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (astBody.drop 15))]]⟩
      ⟨s₃, {}, (bodyCtx F₁ (expression (astBody.drop 20))).fill
        (vals [.i32 16, .i32 1, .i32 0, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 16, .i32 1, .i32 0, .i32 1] (expression (astBody.drop 20))
      (step_call (x := ⟨0⟩) (by rw [hF₁f]; rfl) hs₃f.1))
  have hd₂ : decompose? s₃ ((bodyCtx F₁ (expression (astBody.drop 20))).fill
      (vals [.i32 16, .i32 1, .i32 0, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F₁ (expression (astBody.drop 20)), 0, 0, [.i32 16, .i32 1, .i32 0, .i32 1]) :=
    decompose_fill _ trivial hs₃f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₄ := TSession.call (TSession.of_core_steps t₃
    ((((st₃.steps.trans st₄.steps).trans st₅.steps).trans st₆.steps).trans st₇.steps)) hd₂
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₃, .values [.i32 (q + 1)]⟩) (q' := q + 1 + 1)
    ⟨rfl, rfl⟩
  -- accept
  have st₈ : Step P NH ⟨s₃, {}, (bodyCtx F₁ (expression (astBody.drop 20))).fill
      (Result.values [.i32 (q + 1)]).toAdmin⟩
      ⟨s₃, {}, (bodyCtx F₁ []).fill
        (vals [.i32 (q + 1)] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 (q + 1)] [] (step_call (x := ⟨1⟩) (by rw [hF₁f]; rfl) hs₃f.2.1))
  have hd₃ : decompose? s₃ ((bodyCtx F₁ []).fill
      (vals [.i32 (q + 1)] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F₁ [], 1, 1, [.i32 (q + 1)]) :=
    decompose_fill _ trivial hs₃f.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₆ := TSession.call (TSession.of_core_steps t₅ st₈.steps) hd₃
  -- the decoded events
  have hco₁ : calloutAt? astMod (some 0) ⟨s₁, {}, (bodyCtx F (expression (astBody.drop 8))).fill
      (vals [.i32 16, .i32 1, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn impTag (some 0) s₁ [.i32 16, .i32 1, .i32 0, .i32 0]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? astMod (some 0) ⟨s₃, {}, (bodyCtx F₁ (expression (astBody.drop 20))).fill
      (vals [.i32 16, .i32 1, .i32 0, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn impTag (some 0) s₃ [.i32 16, .i32 1, .i32 0, .i32 1]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? astMod (some 0) ⟨s₃, {}, (bodyCtx F₁ []).fill
      (vals [.i32 (q + 1)] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn impAcc (some 0) s₃ [.i32 (q + 1)]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have htn₁ : Callout.tagNode (calloutIn impTag (some 0) s₁ [.i32 16, .i32 1, .i32 0, .i32 0]) =
      some ("a", []) :=
    tagNode_eq rfl ((segment_of_store hst₁ _ (memOf_setMem hml)).trans (by decide)) utf8_a
      (segment_nil (memOf_setMem hml) 0 (Nat.zero_le _)) rfl
  have h₀ : bytesAt b₃ ⟨0, 4⟩ = (Memory.encodeLE 4 q.toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hst₃ (.inr (by decide))]
    exact bytes_of_store32 hst₂
  have htn₂ : Callout.tagNode (calloutIn impTag (some 0) s₃ [.i32 16, .i32 1, .i32 0, .i32 1]) =
      some ("f", [q]) :=
    tagNode_eq rfl ((segment_of_store hst₃ _ (memOf_setMem hl₂)).trans (by decide)) utf8_f
      (segment_of_bytesAt (memOf_setMem hl₂) (by rw [hz₃]; decide) h₀) (le32s_one q)
  have hw₁ : astWrite {} (calloutIn impTag (some 0) s₁ [.i32 16, .i32 1, .i32 0, .i32 0])
      ⟨.values [.i32 q], memOf (some 0) s₁⟩ = some (.write ⟨"a", ()⟩ [] q) :=
    astWrite_eq rfl htn₁ rfl
  have hw₂ : astWrite {} (calloutIn impTag (some 0) s₃ [.i32 16, .i32 1, .i32 0, .i32 1])
      ⟨.values [.i32 (q + 1)], memOf (some 0) s₃⟩ = some (.write ⟨"f", ()⟩ [q] (q + 1)) :=
    astWrite_eq rfl htn₂ rfl
  have hna₁ : astAccept {} (calloutIn impTag (some 0) s₁ [.i32 16, .i32 1, .i32 0, .i32 0]) =
      none := astAccept_eq_none (by show ("ast", "tag") ≠ ("ast", "accept"); decide)
  have hna₂ : astAccept {} (calloutIn impTag (some 0) s₃ [.i32 16, .i32 1, .i32 0, .i32 1]) =
      none := astAccept_eq_none (by show ("ast", "tag") ≠ ("ast", "accept"); decide)
  have hac : astAccept {} (calloutIn impAcc (some 0) s₃ [.i32 (q + 1)]) =
      some (.accept (q + 1)) := by
    simp [astAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  rw [hco₁, hco₂, hco₃] at t₆
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply hiOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₆⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, astRoles]
  rw [hna₁, hw₁, hna₂, hw₂, hac]
  rfl

/-- **`astMod` accepts `f(a)`**, for every profile and policy. -/
theorem astMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    faTree ∈ astWriterLang P (ReplyEnvs hiReply) 0 astMod {} pol := by
  let q := base pol
  have hn₀ : pol.sentinel ≠ some q := by simpa using base_ne pol (k := 0) (by decide)
  have hn₁ : pol.sentinel ≠ some (q + 1) := base_ne pol (k := 1) (by decide)
  have d₁ : q + 1 ≠ q := by bv_omega
  have e₁ : Function.update (Env.empty : Env (BitVec 32) (AST strSig)) q
      (some leafA) (q + 1) = none := by
    rw [Function.update_of_ne d₁]; rfl
  have hb₁ : (astW strSig).built (Env.empty : Env (BitVec 32) (AST strSig)) ⟨"a", ()⟩ [] =
      some leafA := rfl
  have hb₂ : (astW strSig).built (Function.update (Env.empty : Env (BitVec 32) (AST strSig)) q
      (some leafA)) ⟨"f", ()⟩ [q] = some faTree := by
    unfold Writer.built Env.lookupAll
    rw [List.mapM_cons, List.mapM_nil, Function.update_self]
    rfl
  simp only [astWriterLang, writerLang, Host.lang]
  refine Set.mem_biUnion (ast_traces P q) ⟨_, _, .cons .enter
    (.cons (.writeOk (t := leafA) hb₁ ⟨hn₀, .inl rfl⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := faTree) hb₂ ⟨hn₁, .inl e₁⟩ fun _ h => by cases h)
    (.cons (.acceptOk (t := faTree) (by simp)) (.nil _)))), by simp⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Ast
