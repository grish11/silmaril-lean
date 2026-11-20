module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAstLive
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnMod

/-!
# Proofs: `ownMod` accepts `res(rep)`; `twiceMod` moves a handle twice

Against the counting host `countEnv hiOut` started at `q`:

* `own_traces`: the traced session of `ownMod` has the raw writer trace
  `[enter, write (res 1) [] q, accept q]`: `node(0, 16, 0, 0)` reads the handle `1` stored at
  `[16, 20)`. `ownMod_live`: when `1` is a live `own<0>` handle of `rt₀` with representation
  `rep`, the resource host consumes it and accepts `res(rep)`.
* `twice_traces`: the traced session of `twiceMod` has the raw writer trace
  `[enter, write (res 1) [] q, write (res 1) [] (q + 1), accept (q + 1)]` (both calls read the
  same handle). `twice_accepts`: **under the resource host this trace accepts nothing**, in every
  table, for every policy without undefined behaviour: the second move does not resolve (the
  first consumed the handle, or neither resolves), so `q + 1` denotes no tree. `twice_via`:
  the stateless reading, which ignores consumption, accepts `res(rep)` on the same trace.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitOwn

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own
  Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WordAtom
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnMod
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
open Silmaril.Wasm.Logic.Core (bytesAt)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitAst (hiOut_shape)

theorem ownSpec_some : (Silmaril.Wasm.Verify.specInstance? ownMod).isSome = true := by
  decide +kernel

theorem ownMem : memSizes ownMod = [65536] := by decide +kernel

/-- **The raw writer trace of the session of `ownMod`.** -/
theorem own_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write (rawRes 1) [] q, .accept q] ∈
      witTraces (rawSig ownSig) ownRawTagOf P (ReplyEnvs hiReply) 0 ownMod {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists ownSpec_some
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := own_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page ownMem hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, -⟩ := fnOk_spec h2
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hfs : ∀ s : Store Nat, s.funcs = c.store.funcs → s.funcs[0]? = some f₀ ∧
      s.funcs[1]? = some f₁ ∧ s.funcs[2]? = some f₂ := by
    intro s h; rw [h, hf]; exact ⟨rfl, rfl, rfl⟩
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  let L := countEnv hiOut
  let R := ownRoles
  have t₀ : TSession P L ownMod (some 0) R c q Is.addrs .inst false (c, q) [] := .start
  have hok : InvokeOk c.store 2 [] := ⟨f₂, ps, rs, (hfs _ rfl).2.2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 2 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  -- enter `run`
  have st₀ : Step P NH (invoke c.store 2 [])
      ⟨c.store, {}, [.frame 0 (Frame.forCall f₂.module [] [.i32, .i32])
        [.label 0 [] (expression ownBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[2]?.map FuncInst.type).getD default)) (vs := [])
      (a := 2) (fi := f₂) (code := code) trivial (hfs _ rfl).2.2 he (by rw [hps]; rfl) hcode2
    rw [hrs, hloc, hbody] at h
    exact h
  have hFf : (Frame.forCall f₂.module [] [.i32, .i32]).module.funcs = [0, 1, 2] := by
    simp [Frame.forCall, hfuncs]
  have hFm : (Frame.forCall f₂.module [] [.i32, .i32]).module.mems = [0] := by
    simp [Frame.forCall, hmems2]
  generalize Frame.forCall f₂.module [] [.i32, .i32] = F at st₀ hFf hFm
  -- the handle `1` at 16
  obtain ⟨b₁, hst₁⟩ := store_some (B := mi.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i32.width / 8) ((1 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  let mi₁ : MemInst := { mi with bytes := b₁ }
  let s₁ := c.store.setMem 0 mi₁
  obtain ⟨-, -, hf₁⟩ := setMem_mems (mi := mi₁) hml
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression ownBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (ownBody.drop 3))]]⟩ :=
    step_body (step_mid [] _ (step_store32 hFm hmi hst₁))
  -- node(0, 16, 0, 0)
  have hs₁f := hfs s₁ hf₁
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (ownBody.drop 3))]]⟩
      ⟨s₁, {}, (bodyCtx F (expression (ownBody.drop 8))).fill
        (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 16, .i32 0, .i32 0] (expression (ownBody.drop 8))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hs₁f.1))
  have hd₁ : decompose? s₁ ((bodyCtx F (expression (ownBody.drop 8))).fill
      (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (ownBody.drop 8)), 0, 0, [.i32 0, .i32 16, .i32 0, .i32 0]) :=
    decompose_fill _ trivial hs₁f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  -- accept
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (ownBody.drop 8))).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, (bodyCtx F []).fill
        (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 q] [] (step_call (x := ⟨1⟩) (by rw [hFf]; rfl) hs₁f.2.1))
  have hd₂ : decompose? s₁ ((bodyCtx F []).fill
      (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F [], 1, 1, [.i32 q]) :=
    decompose_fill _ trivial hs₁f.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₄ := TSession.call (TSession.of_core_steps t₃ st₃.steps) hd₂
  -- the decoded events
  have hco₁ : calloutAt? ownMod (some 0) ⟨s₁, {}, (bodyCtx F (expression (ownBody.drop 8))).fill
      (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn impNode (some 0) s₁ [.i32 0, .i32 16, .i32 0, .i32 0]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? ownMod (some 0) ⟨s₁, {}, (bodyCtx F []).fill
      (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn WitAst.impAcc (some 0) s₁ [.i32 q]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hn₁' : Callout.witNode (rawSig ownSig) ownRawTagOf
      (calloutIn impNode (some 0) s₁ [.i32 0, .i32 16, .i32 0, .i32 0]) = some (rawRes 1, []) :=
    witNode_eq rfl rfl (segment_of_store hst₁ _ (memOf_setMem hml)) (readVals_handle _)
      (segment_nil (memOf_setMem hml) 0 (Nat.zero_le _)) rfl rfl
  have hna : ∀ (s : Store Nat) (args : List Val),
      witAccept (rawSig ownSig) {} (calloutIn impNode (some 0) s args) = none := fun _ _ =>
    witAccept_eq_none (by show ("wit", "node") ≠ ("wit", "accept"); decide)
  have hac : witAccept (rawSig ownSig) {} (calloutIn WitAst.impAcc (some 0) s₁ [.i32 q]) =
      some (.accept q) := by
    simp [witAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  rw [hco₁, hco₂] at t₄
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply hiOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₄⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, witRoles]
  rw [hna, witWrite_eq rfl hn₁' rfl, hac]
  rfl

/-- **`ownMod` accepts `res(rep)`** under the resource host, when the handle `1` of the table is
a live `own<0>` handle with representation `rep`, for every profile and policy. -/
theorem ownMod_live (P : Profile) (pol : Policy (BitVec 32)) {rt₀ : RT} {rep : Nat}
    (h : rt₀.lookup 0 1 = some rep) :
    resTree rep ∈ ownLang (astW ownSig.toAstSig) pol rt₀
      (witTraces (rawSig ownSig) ownRawTagOf P (ReplyEnvs hiReply) 0 ownMod {}) := by
  let q := base pol
  have hn₀ : pol.sentinel ≠ some q := by simpa using base_ne pol (k := 0) (by decide)
  simp only [ownLang, Host.lang]
  refine Set.mem_biUnion (own_traces P q) ⟨_, _, .cons (.other rfl .enter)
    (.cons (.move (resolve_res h) (.writeOk (t := resTree rep) rfl ⟨hn₀, .inl rfl⟩
      fun _ h => by cases h))
    (.cons (.other rfl (.acceptOk (t := resTree rep) (by simp))) (.nil _))), by simp⟩

/-! ## Moving a handle twice: `twiceMod` -/

/-- The shape of the instantiated module. -/
def twiceOk : Bool :=
  match prep twiceMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 4 f₀ && stubOk 1 1 f₁ &&
          fnOk [.i32, .i32] twiceBody 0 0 [0, 1, 2] [0] calcD f₂
       | _ => false)
  | none => false

theorem twiceOk_true : twiceOk = true := by decide +kernel

theorem twice_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep twiceMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧
      stubOk 0 4 f₀ = true ∧ stubOk 1 1 f₁ = true ∧
      fnOk [.i32, .i32] twiceBody 0 0 [0, 1, 2] [0] calcD f₂ = true := by
  have h := twiceOk_true
  unfold twiceOk at h
  rw [hp] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  split at h6
  · rename_i f₀ f₁ f₂ hf
    simp only [Bool.and_eq_true] at h6
    exact ⟨f₀, f₁, f₂, hf, h6.1.1, h6.1.2, h6.2⟩
  · cases h6

theorem twiceSpec_some : (Silmaril.Wasm.Verify.specInstance? twiceMod).isSome = true := by
  decide +kernel

theorem twiceMem : memSizes twiceMod = [65536] := by decide +kernel

/-- **The raw writer trace of the session of `twiceMod`**: the handle `1` is moved twice. -/
theorem twice_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write (rawRes 1) [] q, .write (rawRes 1) [] (q + 1), .accept (q + 1)] ∈
      witTraces (rawSig ownSig) ownRawTagOf P (ReplyEnvs hiReply) 0 twiceMod {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists twiceSpec_some
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := twice_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page twiceMem hp
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
  let R := ownRoles
  have t₀ : TSession P L twiceMod (some 0) R c q Is.addrs .inst false (c, q) [] := .start
  have hok : InvokeOk c.store 2 [] := ⟨f₂, ps, rs, (hfs _ rfl).2.2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 2 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  -- enter `run`
  have st₀ : Step P NH (invoke c.store 2 [])
      ⟨c.store, {}, [.frame 0 (Frame.forCall f₂.module [] [.i32, .i32])
        [.label 0 [] (expression twiceBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[2]?.map FuncInst.type).getD default)) (vs := [])
      (a := 2) (fi := f₂) (code := code) trivial (hfs _ rfl).2.2 he (by rw [hps]; rfl) hcode2
    rw [hrs, hloc, hbody] at h
    exact h
  have hFf : (Frame.forCall f₂.module [] [.i32, .i32]).module.funcs = [0, 1, 2] := by
    simp [Frame.forCall, hfuncs]
  have hFm : (Frame.forCall f₂.module [] [.i32, .i32]).module.mems = [0] := by
    simp [Frame.forCall, hmems2]
  have hFl : (Frame.forCall f₂.module [] [.i32, .i32]).locals = calcD := by
    simp [Frame.forCall, hD]
  generalize Frame.forCall f₂.module [] [.i32, .i32] = F at st₀ hFf hFm hFl
  let F₁ := F.setLocal ⟨0⟩ (.i32 q)
  have hF₁f : F₁.module.funcs = [0, 1, 2] := hFf
  -- the handle `1` at 16
  obtain ⟨b₁, hst₁⟩ := store_some (B := mi.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i32.width / 8) ((1 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  let mi₁ : MemInst := { mi with bytes := b₁ }
  let s₁ := c.store.setMem 0 mi₁
  obtain ⟨-, -, hf₁⟩ := setMem_mems (mi := mi₁) hml
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression twiceBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (twiceBody.drop 3))]]⟩ :=
    step_body (step_mid [] _ (step_store32 hFm hmi hst₁))
  -- node(0, 16, 0, 0)
  have hs₁f := hfs s₁ hf₁
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (twiceBody.drop 3))]]⟩
      ⟨s₁, {}, (bodyCtx F (expression (twiceBody.drop 8))).fill
        (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 16, .i32 0, .i32 0] (expression (twiceBody.drop 8))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hs₁f.1))
  have hd₁ : decompose? s₁ ((bodyCtx F (expression (twiceBody.drop 8))).fill
      (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (twiceBody.drop 8)), 0, 0, [.i32 0, .i32 16, .i32 0, .i32 0]) :=
    decompose_fill _ trivial hs₁f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  -- local.set 0; node(0, 16, 0, 0) again
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (twiceBody.drop 8))).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (twiceBody.drop 9))]]⟩ :=
    step_body (step_mid [] (expression (twiceBody.drop 9))
      (step_localSet (x := ⟨0⟩) (v := .i32 q) (by simp [hFl, calcD, Idx.toNat])))
  have st₄ : Step P NH
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (twiceBody.drop 9))]]⟩
      ⟨s₁, {}, (bodyCtx F₁ (expression (twiceBody.drop 14))).fill
        (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 16, .i32 0, .i32 0] (expression (twiceBody.drop 14))
      (step_call (x := ⟨0⟩) (by rw [hF₁f]; rfl) hs₁f.1))
  have hd₂ : decompose? s₁ ((bodyCtx F₁ (expression (twiceBody.drop 14))).fill
      (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F₁ (expression (twiceBody.drop 14)), 0, 0, [.i32 0, .i32 16, .i32 0, .i32 0]) :=
    decompose_fill _ trivial hs₁f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₄ := TSession.call (TSession.of_core_steps t₃ (st₃.steps.trans st₄.steps)) hd₂
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₁, .values [.i32 (q + 1)]⟩) (q' := q + 1 + 1)
    ⟨rfl, rfl⟩
  -- accept
  have st₅ : Step P NH ⟨s₁, {}, (bodyCtx F₁ (expression (twiceBody.drop 14))).fill
      (Result.values [.i32 (q + 1)]).toAdmin⟩
      ⟨s₁, {}, (bodyCtx F₁ []).fill
        (vals [.i32 (q + 1)] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 (q + 1)] [] (step_call (x := ⟨1⟩) (by rw [hF₁f]; rfl) hs₁f.2.1))
  have hd₃ : decompose? s₁ ((bodyCtx F₁ []).fill
      (vals [.i32 (q + 1)] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F₁ [], 1, 1, [.i32 (q + 1)]) :=
    decompose_fill _ trivial hs₁f.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₆ := TSession.call (TSession.of_core_steps t₅ st₅.steps) hd₃
  -- the decoded events
  have hco₁ : calloutAt? twiceMod (some 0)
      ⟨s₁, {}, (bodyCtx F (expression (twiceBody.drop 8))).fill
        (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn impNode (some 0) s₁ [.i32 0, .i32 16, .i32 0, .i32 0]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? twiceMod (some 0)
      ⟨s₁, {}, (bodyCtx F₁ (expression (twiceBody.drop 14))).fill
        (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn impNode (some 0) s₁ [.i32 0, .i32 16, .i32 0, .i32 0]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? twiceMod (some 0) ⟨s₁, {}, (bodyCtx F₁ []).fill
      (vals [.i32 (q + 1)] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn WitAst.impAcc (some 0) s₁ [.i32 (q + 1)]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hn₁' : Callout.witNode (rawSig ownSig) ownRawTagOf
      (calloutIn impNode (some 0) s₁ [.i32 0, .i32 16, .i32 0, .i32 0]) = some (rawRes 1, []) :=
    witNode_eq rfl rfl (segment_of_store hst₁ _ (memOf_setMem hml)) (readVals_handle _)
      (segment_nil (memOf_setMem hml) 0 (Nat.zero_le _)) rfl rfl
  have hna : ∀ (s : Store Nat) (args : List Val),
      witAccept (rawSig ownSig) {} (calloutIn impNode (some 0) s args) = none := fun _ _ =>
    witAccept_eq_none (by show ("wit", "node") ≠ ("wit", "accept"); decide)
  have hac : witAccept (rawSig ownSig) {} (calloutIn WitAst.impAcc (some 0) s₁ [.i32 (q + 1)]) =
      some (.accept (q + 1)) := by
    simp [witAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  rw [hco₁, hco₂, hco₃] at t₆
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply hiOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₆⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, witRoles]
  rw [hna, witWrite_eq rfl hn₁' rfl, witWrite_eq rfl hn₁' rfl, hac]
  rfl

/-- **Moving a handle twice yields no second tree**: under the resource host the trace of
`twiceMod` accepts nothing, in every table, for every policy without undefined behaviour. The
second move does not resolve (if the first resolved it consumed the handle, otherwise neither
resolves), so it gives `q + 1` no meaning and `accept(q + 1)` is invalid. -/
theorem twice_accepts {X : Type} (W : Writer (Op ownSig) X) {pol : Policy (BitVec 32)}
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) (rt₀ : RT) (q : BitVec 32) :
    (ownHost W pol rt₀).accepts
      [.enter, .write (rawRes 1) [] q, .write (rawRes 1) [] (q + 1), .accept (q + 1)] = ∅ := by
  have hq : q + 1 ≠ q := by bv_omega
  have hx : (1 : BitVec 32) ∈ movedOp ownSig (rawRes 1) := by
    rw [movedOp_res]; exact List.mem_singleton_self _
  refine Set.eq_empty_of_subset_empty fun y ⟨s, A, hr, hy⟩ => ?_
  rw [Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.run_twice hx hw ha rfl rfl hq hr]
    at hy
  exact hy

/-- **The stateless reading ignores consumption**: on the same trace it accepts `res(rep)`. -/
theorem twice_via (pol : Policy (BitVec 32)) {rt₀ : RT} {rep : Nat}
    (h : rt₀.lookup 0 1 = some rep) (q : BitVec 32) (hq : pol.sentinel ≠ some q)
    (hq₁ : pol.sentinel ≠ some (q + 1)) :
    resTree rep ∈ (writer (viaRT (astW ownSig.toAstSig) rt₀) pol).accepts
      [.enter, .write (rawRes 1) [] q, .write (rawRes 1) [] (q + 1), .accept (q + 1)] := by
  have hd : q + 1 ≠ q := by bv_omega
  refine ⟨_, _, .cons .enter
    (.cons (.writeOk (t := resTree rep) (built_res h _) ⟨hq, .inl rfl⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := resTree rep) (built_res h _) ⟨hq₁, .inl ?_⟩ fun _ h => by cases h)
    (.cons (.acceptOk (t := resTree rep) (Function.update_self ..)) (.nil _)))), by simp⟩
  show Function.update Env.empty q _ (q + 1) = none
  rw [Function.update_of_ne hd]
  rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitOwn
