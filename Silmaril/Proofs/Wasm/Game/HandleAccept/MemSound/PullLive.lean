module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull

/-!
# Proofs: `echoMod` relates the chunk it reads

Against `echoEnv`, the traced session of `echoMod` invokes `run`, calls `read(0, 16)` (the host
writes `68 69` at `0` and returns `2`: decoded at the answer as `feed [68, 69]`), then calls
`finish(2, 7)` (decoded at the call as `finish 2 7`). In a fixed environment where `7` denotes
`x` and `7` is not the sentinel, the parsing run relates `68 69` to `x`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Accept.Parse Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Game.HandleAccept.MemSound.Pull
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
open Silmaril.Wasm.Logic.Core (bytesAt)

theorem echoSpec_some : (Silmaril.Wasm.Verify.specInstance? echoMod).isSome = true := by
  decide +kernel

theorem echoMem : memSizes echoMod = [65536] := by decide +kernel

theorem hiStore_keeps (s : Store Nat) : KeepsCode s (hiStore s) := by
  unfold hiStore
  cases s.mems[0]? with
  | none => exact ⟨rfl, rfl⟩
  | some mi =>
    simp only [Option.bind_some]
    cases Memory.store mi.bytes 0 (count := PackSize.i16.width / 8)
        ((0x6968 : BitVec 32).setWidth _) with
    | none => exact ⟨rfl, rfl⟩
    | some b => simp [KeepsCode, Store.setMem]

/-- `echoEnv` is admitted by `echoReply`. -/
theorem echoEnv_reply (s : Store Nat) : ReplyEnvs echoReply s echoEnv := by
  rintro q e a q' (⟨h0, ha, rfl⟩ | ⟨h1, rfl⟩)
  · refine ⟨hiStore_keeps _, fun vs hv => ?_⟩
    cases hv
    refine ⟨fun _ => ⟨2, rfl, fun p c hpc => ?_⟩, fun h => by rw [h0] at h; cases h⟩
    rw [ha] at hpc
    have hc : Callout.i32? (Val.i32 16) = Callout.i32? (Val.i32 c) :=
      congrArg Callout.i32? (List.cons.inj (List.cons.inj hpc).2).1
    obtain rfl : (16 : BitVec 32) = c := Option.some.inj hc
    decide
  · refine ⟨⟨rfl, rfl⟩, fun vs hv => ?_⟩
    cases hv
    exact ⟨(fun h => by rw [h1] at h; cases h), fun _ => rfl⟩

/-- **The parsing trace of the session.** -/
theorem echo_traces (P : Profile) :
    [.feed [0x68, 0x69], .finish 2 7] ∈ pullTraces P (ReplyEnvs echoReply) 0 echoMod {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists echoSpec_some
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := echo_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page echoMem hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, -, -⟩ := fnOk_spec h2
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hf0 : c.store.funcs[0]? = some f₀ := by rw [hf]; rfl
  have hf2 : c.store.funcs[2]? = some f₂ := by rw [hf]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  let F : Frame := Frame.forCall f₂.module [] []
  have hFf : F.module.funcs = [0, 1, 2] := by simp [F, Frame.forCall, hfuncs]
  have t₀ : TSession P echoEnv echoMod (some 0) (pullRoles {}) c () Is.addrs .inst false
      (c, ()) [] := .start
  have hok : InvokeOk c.store 2 [] := ⟨f₂, ps, rs, hf2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 2 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  have st₀ : Step P NH (invoke c.store 2 [])
      ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression echoBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[2]?.map FuncInst.type).getD default)) (vs := [])
      (a := 2) (fi := f₂) (code := code) trivial hf2 he (by rw [hps]; rfl) hcode2
    rw [hrs, hloc, hbody] at h
    exact h
  -- read(0, 16)
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression echoBody)]]⟩
      ⟨c.store, {}, (bodyCtx F (expression (echoBody.drop 3))).fill
        (vals [.i32 0, .i32 16] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 16] (expression (echoBody.drop 3))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hf0))
  have hd₁ : decompose? c.store ((bodyCtx F (expression (echoBody.drop 3))).fill
      (vals [.i32 0, .i32 16] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (echoBody.drop 3)), 0, 0, [.i32 0, .i32 16]) :=
    decompose_fill _ trivial hf0 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁ (st₀.steps.trans st₁.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨hiStore c.store, .values [.i32 2]⟩) (q' := ())
    (.inl ⟨rfl, rfl, rfl⟩)
  -- the host's write
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := 0) (n := PackSize.i16.width / 8)
    ((0x6968 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  have hs₁ : hiStore c.store = c.store.setMem 0 { mi with bytes := b } := by
    simp only [hiStore, hmi, hst, Option.bind_some, Option.map_some, Option.getD_some]
  obtain ⟨hfs₁, -⟩ := hiStore_keeps c.store
  have hf1' : (hiStore c.store).funcs[1]? = some f₁ := by rw [hfs₁, hf]; rfl
  -- finish(2, 7)
  have st₂ : Step P NH ⟨hiStore c.store, {}, (bodyCtx F (expression (echoBody.drop 3))).fill
      (Result.values [.i32 2]).toAdmin⟩
      ⟨hiStore c.store, {}, (bodyCtx F []).fill
        (vals [.i32 2, .i32 7] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 2, .i32 7] [] (step_call (x := ⟨1⟩) (by rw [hFf]; rfl) hf1'))
  have hd₂ : decompose? (hiStore c.store) ((bodyCtx F []).fill
      (vals [.i32 2, .i32 7] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F [], 1, 1, [.i32 2, .i32 7]) :=
    decompose_fill _ trivial hf1' he₁ (by rw [hn₁]; rfl) hc₁
  have t₄ := TSession.call (TSession.of_core_steps t₃ st₂.steps) hd₂
  -- the decoded events
  have hco₁ : calloutAt? echoMod (some 0) ⟨c.store, {},
      (bodyCtx F (expression (echoBody.drop 3))).fill
        (vals [.i32 0, .i32 16] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn ⟨"input", "read", .func ⟨0⟩⟩ (some 0) c.store [.i32 0, .i32 16]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? echoMod (some 0) ⟨hiStore c.store, {}, (bodyCtx F []).fill
      (vals [.i32 2, .i32 7] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨"input", "finish", .func ⟨1⟩⟩ (some 0) (hiStore c.store)
        [.i32 2, .i32 7]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hseg : segOf b 0 2 = some [0x68, 0x69] := by
    have hz : b.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst).trans hsize
    unfold segOf
    rw [readBytes_toList (by rw [hz]; decide)]
    exact congrArg some ((Silmaril.Wasm.Logic.Core.bytesAt_store_same hst).trans (by decide))
  have hrd : pullRead {} (calloutIn ⟨"input", "read", .func ⟨0⟩⟩ (some 0) c.store
      [.i32 0, .i32 16]) ⟨.values [.i32 2], memOf (some 0) (hiStore c.store)⟩ =
      some (.feed [0x68, 0x69]) := by
    have hm : memOf (some 0) (hiStore c.store) = some b := by rw [hs₁]; exact memOf_setMem hml
    simp [pullRead, calloutIn, Val.i32, replyI32, hm]
    exact hseg
  have hna : pullFinish {} (calloutIn ⟨"input", "read", .func ⟨0⟩⟩ (some 0) c.store
      [.i32 0, .i32 16]) = none := by
    simp [pullFinish, calloutIn]
  have hfin : pullFinish {} (calloutIn ⟨"input", "finish", .func ⟨1⟩⟩ (some 0) (hiStore c.store)
      [.i32 2, .i32 7]) = some (.finish 2 7) := by
    simp only [pullFinish, calloutIn, Val.i32, usedOfI32, ↓reduceIte]
    rfl
  rw [hco₁, hco₂] at t₄
  refine ⟨_, ⟨mt, Is, c, hI, echoEnv, (), echoEnv_reply _, .run, true, _,
    by rw [hmem0]; exact t₄⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, pullRoles]
  rw [hna, hrd, hfin]
  rfl

/-- **`echoMod` relates the chunk `68 69` it reads to the tree of `7`.** -/
theorem echo_live (P : Profile) {X : Type} (pol : PPolicy (BitVec 32)) (hsent : pol.sentinel ≠ 7)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) X} (hρ : ρ ∈ Rhos) {x : X} (h7 : ρ 7 = some x) :
    ([0x68, 0x69], x) ∈ pullRel P (ReplyEnvs echoReply) 0 echoMod {} pol Rhos := by
  have hres : resolve pol ρ ([0x68, 0x69] : List UInt8) 7 =
      some {(([0x68, 0x69] : List UInt8), x)} := by
    unfold resolve
    split_ifs with h
    · exact absurd h.symm hsent
    · rw [h7]; rfl
  simp only [pullRel, parseRel, langOver, Host.lang]
  refine Set.mem_iUnion.2 ⟨⟨ρ, hρ⟩, Set.mem_biUnion (echo_traces P) ⟨_, _, .cons (.feed _)
    (.cons (.ret (s' := ⟨[], [], .live⟩) (w := [0x68, 0x69]) (h := 7) rfl
      ⟨by decide, rfl, rfl, rfl⟩ hres) (.nil _)), by simp⟩⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull
