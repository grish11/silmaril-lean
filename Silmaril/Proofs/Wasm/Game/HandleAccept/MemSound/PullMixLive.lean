module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullLive

/-!
# Proofs: `blobEcho` relates the chunk it reads to the atom it builds

Against `blobEnv q`, the traced session of `blobEcho` invokes `run`; `read(0, 16)` is answered
by writing `68 69` at `0` and returning `2` (decoded at the answer as `feed [68, 69]`); the
callout of `blob(0, 2)` observes `68 69` and is answered with `q` (decoded as the write of the
byte atom `68 69` with handle `q`); `finish(2, q)` is decoded at the call. The mixed trace
`[enter, feed [68, 69], write (bytes 68 69) [] q, finish 2 q]` relates `68 69` to the byte atom
`68 69` in the store semantics: the store current at `finish` maps `q` to the atom just written.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats
  Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pull
  Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull
open Silmaril.Wasm.Logic.Core (bytesAt)

theorem beSpec_some : (Silmaril.Wasm.Verify.specInstance? blobEcho).isSome = true := by
  decide +kernel

theorem hiStore_grows (s : Store Nat) : MemGrows s (hiStore s) := by
  intro mi hmi
  unfold hiStore
  rw [hmi]
  simp only [Option.bind_some]
  rcases hst : Memory.store mi.bytes 0 (count := PackSize.i16.width / 8)
      ((0x6968 : BitVec 32).setWidth _) with _ | b
  · exact ⟨mi, by simpa using hmi, le_rfl⟩
  · refine ⟨{ mi with bytes := b }, ?_, (Silmaril.Wasm.Logic.Core.size_store hst).ge⟩
    have hl : 0 < s.mems.length := by
      rcases hs : s.mems with _ | ⟨x, xs⟩
      · rw [hs] at hmi; cases hmi
      · simp
    simp [Store.setMem, hl]

/-- `blobEnv q` is admitted by `blobReply`. -/
theorem blobEnv_reply (q : BitVec 32) (s : Store Nat) : ReplyEnvs blobReply s (blobEnv q) := by
  rintro _ e a _ (⟨h0, ha, rfl⟩ | ⟨h1, rfl⟩ | ⟨h2, rfl⟩)
  · refine ⟨hiStore_keeps _, hiStore_grows _, fun vs hv => ?_⟩
    cases hv
    refine ⟨fun _ => ⟨2, rfl, fun p c hpc => ?_⟩, fun h => ?_, fun h => ?_⟩
    rotate_left
    · rw [h0] at h; cases h
    · rw [h0] at h; cases h
    rw [ha] at hpc
    have hc : Callout.i32? (Val.i32 16) = Callout.i32? (Val.i32 c) :=
      congrArg Callout.i32? (List.cons.inj (List.cons.inj hpc).2).1
    obtain rfl : (16 : BitVec 32) = c := Option.some.inj hc
    decide
  · refine ⟨⟨rfl, rfl⟩, fun mi h => ⟨mi, h, le_rfl⟩, fun vs hv => ?_⟩
    cases hv
    refine ⟨fun h => ?_, fun _ => ⟨q, rfl⟩, fun h => ?_⟩
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h
  · refine ⟨⟨rfl, rfl⟩, fun mi h => ⟨mi, h, le_rfl⟩, fun vs hv => ?_⟩
    cases hv
    refine ⟨fun h => ?_, fun h => ?_, fun _ => rfl⟩
    · rw [h2] at h; cases h
    · rw [h2] at h; cases h

/-- The byte atom `68 69` as a memory atom. -/
abbrev hiBytes : MemAtom := ⟨.bytes, by decide, [0x68, 0x69]⟩

/-- The roles of the sessions. -/
abbrev mR : Roles Unit MixEv Unit Unit := mixRoles {} {}

/-- The tags of one invocation of `run` reading `cs` and writing its atom with handle `h`. -/
abbrev roundTags (cs : List UInt8) (h : BitVec 32) : List (Tag Unit MixEv Unit Unit) :=
  [.enter none, .inp (.p (.feed cs)), .inp (.w (.write (.atom ⟨.bytes, by decide, cs⟩) [] h)),
    .inp (.p (.finish 2 h))]

theorem callTags_mR (o : Callout) : mR.callTags o = (mixCall {} {} o).toList.map Tag.inp := by
  simp [Roles.callTags, mR, mixRoles]

theorem answerTags_mR (o : Callout) (w : HostReply) :
    mR.answerTags o w = (mixAnswer {} {} o w).toList.map Tag.inp := rfl

section Round

variable {P : Profile} {L : SEnv UImp} {mt : CModuleType} {Is : ScalarInstance}
  {c : Config Nat} {q₀ : L.S} {p : IOAccept.Phase} {w : Bool} {c' : Config Nat} {k₀ k₁ k₂ : L.S}
  {ts : List (Tag Unit MixEv Unit Unit)} {s₁ : Store Nat} {b : ByteArray} {cs : List UInt8}

/-- The session up to the answer of `read(0, 16)` and the calls before `blob`: the common prefix
of `be_round` and `be_trap_round`. -/
theorem be_prefix (hI : IsSpecInstance blobEcho mt Is c) (hp : prep blobEcho = some (c, none))
    (t : TSession P L blobEcho (some 0) mR c q₀ Is.addrs p w (c', k₀) ts)
    (hp' : p ≠ .run) (fin : Finished p.started c') (hfs : c'.store.funcs = c.store.funcs)
    (hs₁ : s₁.funcs = c.store.funcs) (hm : memOf (some 0) s₁ = some b)
    (hseg : segOf b 0 2 = some cs)
    (hA₀ : L.Ans k₀ ⟨0, c'.store, [.i32 0, .i32 16]⟩ ⟨s₁, .values [.i32 2]⟩ k₁) :
    ∃ (E : SingleThreaded.Ctx) (F₁ : Frame) (f₁ f₂ : FuncInst Nat),
      E = .frame [] 0 F₁ (.label [] 0 [] (.top [.i32 2] (expression [.call ⟨2⟩])) []) [] ∧
      F₁.module.funcs = [0, 1, 2, 3] ∧ s₁.funcs[1]? = some f₁ ∧ s₁.funcs[2]? = some f₂ ∧
      stubOk 1 2 f₁ = true ∧ stubOk 2 2 f₂ = true ∧
      decompose? s₁ (E.fill (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])) =
        some (E, 1, 1, [.i32 0, .i32 2]) ∧
      TSession P L blobEcho (some 0) mR c q₀ Is.addrs .run true
        (⟨s₁, {}, E.fill (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩, k₁)
        (ts ++ [.enter none, .inp (.p (.feed cs))]) := by
  obtain ⟨-, -, -, hexp, -, f₀, f₁, f₂, f₃, hf, h0, h1, h2, h3⟩ := be_facts hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨code, ps, rs, hcode3, hloc, hbody, he, hps, hrs, hfuncs, -, hD⟩ := fnOk_spec h3
  obtain ⟨cc, st', hp'', -, -, haddr⟩ := prep_of_spec hI
  obtain ⟨hcc, -⟩ := Prod.mk.inj (Option.some.inj (hp''.symm.trans hp))
  rw [hcc] at haddr
  have hfs' : ∀ s : Store Nat, s.funcs = c.store.funcs → s.funcs[0]? = some f₀ ∧
      s.funcs[1]? = some f₁ ∧ s.funcs[2]? = some f₂ ∧ s.funcs[3]? = some f₃ := by
    intro s h; rw [h, hf]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hok : InvokeOk c'.store 3 [] := ⟨f₃, ps, rs, (hfs' _ hfs).2.2.2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 3 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t hp' fin ha hok
  have st₀ : Step P NH (invoke c'.store 3 [])
      ⟨c'.store, {}, [.frame 0 (Frame.forCall f₃.module [] [.i32])
        [.label 0 [] (expression blobEchoBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c'.store) (f := {})
      (c := .callRefType ((c'.store.funcs[3]?.map FuncInst.type).getD default)) (vs := [])
      (a := 3) (fi := f₃) (code := code) trivial (hfs' _ hfs).2.2.2 he (by rw [hps]; rfl) hcode3
    rw [hrs, hloc, hbody] at h
    exact h
  have hFf : (Frame.forCall f₃.module [] [.i32]).module.funcs = [0, 1, 2, 3] := by
    simp [Frame.forCall, hfuncs]
  have hFl : (Frame.forCall f₃.module [] [.i32]).locals = beD := by
    simp [Frame.forCall, hD]
  generalize Frame.forCall f₃.module [] [.i32] = F at st₀ hFf hFl
  let F₁ := F.setLocal ⟨0⟩ (.i32 2)
  have hF₁f : F₁.module.funcs = [0, 1, 2, 3] := hFf
  have hs₁f := hfs' _ hs₁
  -- read(0, 16)
  have st₁ : Step P NH ⟨c'.store, {}, [.frame 0 F [.label 0 [] (expression blobEchoBody)]]⟩
      ⟨c'.store, {}, (bodyCtx F (expression (blobEchoBody.drop 3))).fill
        (vals [.i32 0, .i32 16] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 16] (expression (blobEchoBody.drop 3))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) (hfs' _ hfs).1))
  have hd₁ : decompose? c'.store ((bodyCtx F (expression (blobEchoBody.drop 3))).fill
      (vals [.i32 0, .i32 16] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (blobEchoBody.drop 3)), 0, 0, [.i32 0, .i32 16]) :=
    decompose_fill _ trivial (hfs' _ hfs).1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁ (st₀.steps.trans st₁.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 2]⟩) hA₀
  -- local.set 0; local.get 0; i32.const 0; local.get 0; blob(0, 2)
  have st₂ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (blobEchoBody.drop 3))).fill
      (Result.values [.i32 2]).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (blobEchoBody.drop 4))]]⟩ :=
    step_body (step_mid [] (expression (blobEchoBody.drop 4))
      (step_localSet (x := ⟨0⟩) (v := .i32 2) (by simp [hFl, beD, Idx.toNat])))
  have hv : F₁.local? ⟨0⟩ = some (some (.i32 2)) := by
    simp [F₁, Frame.local?, Frame.setLocal, hFl, beD, Idx.toNat]
  have st₃ : Step P NH
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (blobEchoBody.drop 4))]]⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 []
        (vals [] ++ [(Val.i32 2).toAdmin] ++ expression (blobEchoBody.drop 5))]]⟩ :=
    step_body (step_mid [] (expression (blobEchoBody.drop 5)) (step_localGet hv))
  have st₄ : Step P NH ⟨s₁, {}, [.frame 0 F₁ [.label 0 []
        (vals [] ++ [(Val.i32 2).toAdmin] ++ expression (blobEchoBody.drop 5))]]⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 []
        (vals [.i32 2, .i32 0] ++ [(Val.i32 2).toAdmin] ++ expression (blobEchoBody.drop 7))]]⟩ :=
    step_body (step_mid [.i32 2, .i32 0] (expression (blobEchoBody.drop 7)) (step_localGet hv))
  let E₂ : SingleThreaded.Ctx :=
    .frame [] 0 F₁ (.label [] 0 [] (.top [.i32 2] (expression [.call ⟨2⟩])) []) []
  have st₅ : Step P NH ⟨s₁, {}, [.frame 0 F₁ [.label 0 []
        (vals [.i32 2, .i32 0] ++ [(Val.i32 2).toAdmin] ++ expression (blobEchoBody.drop 7))]]⟩
      ⟨s₁, {}, E₂.fill (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 2, .i32 0, .i32 2] (expression (blobEchoBody.drop 8))
      (step_call (x := ⟨1⟩) (by rw [hF₁f]; rfl) hs₁f.2.1))
  have hd₂ : decompose? s₁ (E₂.fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (E₂, 1, 1, [.i32 0, .i32 2]) :=
    decompose_fill _ trivial hs₁f.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₄ := TSession.call (TSession.of_core_steps t₃
    (((st₂.steps.trans st₃.steps).trans st₄.steps).trans st₅.steps)) hd₂
  -- the decoded events
  have hco₁ : calloutAt? blobEcho (some 0) ⟨c'.store, {},
      (bodyCtx F (expression (blobEchoBody.drop 3))).fill
        (vals [.i32 0, .i32 16] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn ⟨"input", "read", .func ⟨0⟩⟩ (some 0) c'.store [.i32 0, .i32 16]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? blobEcho (some 0) ⟨s₁, {}, E₂.fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨"sexp", "blob", .func ⟨0⟩⟩ (some 0) s₁ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hrd : mixAnswer {} {} (calloutIn ⟨"input", "read", .func ⟨0⟩⟩ (some 0) c'.store
      [.i32 0, .i32 16]) ⟨.values [.i32 2], memOf (some 0) s₁⟩ = some (.p (.feed cs)) := by
    have hw : memWrite {} (calloutIn ⟨"input", "read", .func ⟨0⟩⟩ (some 0) c'.store
        [.i32 0, .i32 16]) ⟨.values [.i32 2], memOf (some 0) s₁⟩ = none :=
      memWrite_eq_none (by show ("input", "read") ≠ ("sexp", "symbol"); decide)
        (by show ("input", "read") ≠ ("sexp", "string"); decide)
        (by show ("input", "read") ≠ ("sexp", "blob"); decide)
        (by show ("input", "read") ≠ ("sexp", "sexp"); decide)
    have hr : pullRead {} (calloutIn ⟨"input", "read", .func ⟨0⟩⟩ (some 0) c'.store
        [.i32 0, .i32 16]) ⟨.values [.i32 2], memOf (some 0) s₁⟩ = some (.feed cs) := by
      simp [pullRead, calloutIn, Val.i32, replyI32, hm]
      exact hseg
    unfold mixAnswer
    rw [hw]
    dsimp only
    rw [hr]
    rfl
  have hn₁ : mixCall {} {} (calloutIn ⟨"input", "read", .func ⟨0⟩⟩ (some 0) c'.store
      [.i32 0, .i32 16]) = none := by
    simp [mixCall, memAccept, pullFinish, calloutIn]
  have hn₂ : mixCall {} {} (calloutIn ⟨"sexp", "blob", .func ⟨0⟩⟩ (some 0) s₁
      [.i32 0, .i32 2]) = none := by
    simp [mixCall, memAccept, pullFinish, calloutIn]
  rw [hco₁, hco₂] at t₄
  have e₁ : mR.callTags (calloutIn ⟨"input", "read", .func ⟨0⟩⟩ (some 0) c'.store
      [.i32 0, .i32 16]) = [] := by rw [callTags_mR, hn₁]; rfl
  have e₂ : mR.answerTags (calloutIn ⟨"input", "read", .func ⟨0⟩⟩ (some 0) c'.store
      [.i32 0, .i32 16]) ⟨.values [.i32 2], memOf (some 0) s₁⟩ = [.inp (.p (.feed cs))] := by
    rw [answerTags_mR, hrd]; rfl
  have e₃ : mR.callTags (calloutIn ⟨"sexp", "blob", .func ⟨0⟩⟩ (some 0) s₁
      [.i32 0, .i32 2]) = [] := by rw [callTags_mR, hn₂]; rfl
  refine ⟨E₂, F₁, f₁, f₂, rfl, hF₁f, hs₁f.2.1, hs₁f.2.2.1, h1, h2, hd₂, ?_⟩
  have e₀ : mR.entry 3 [] = none := rfl
  simp only [Option.elim, e₀, e₁, e₂, e₃] at t₄
  simpa using t₄

/-- **One invocation of `run`** after a finished run: `read(0, 16)` answered in `s₁` with `2`
over the chunk `cs`, `blob(0, 2)` answered with `h` in `s₁`, then the call `finish(2, h)`. -/
theorem be_round (hI : IsSpecInstance blobEcho mt Is c) (hp : prep blobEcho = some (c, none))
    (t : TSession P L blobEcho (some 0) mR c q₀ Is.addrs p w (c', k₀) ts)
    (hp' : p ≠ .run) (fin : Finished p.started c') (hfs : c'.store.funcs = c.store.funcs)
    (hs₁ : s₁.funcs = c.store.funcs) (hm : memOf (some 0) s₁ = some b)
    (hseg : segOf b 0 2 = some cs) {h : BitVec 32}
    (hA₀ : L.Ans k₀ ⟨0, c'.store, [.i32 0, .i32 16]⟩ ⟨s₁, .values [.i32 2]⟩ k₁)
    (hA₁ : L.Ans k₁ ⟨1, s₁, [.i32 0, .i32 2]⟩ ⟨s₁, .values [.i32 h]⟩ k₂) :
    ∃ c'', TSession P L blobEcho (some 0) mR c q₀ Is.addrs .run true (c'', k₂)
      (ts ++ roundTags cs h) := by
  obtain ⟨E, F₁, f₁, f₂, rfl, hF₁f, -, hf₂, -, h2, hd₂, t₄⟩ :=
    be_prefix hI hp t hp' fin hfs hs₁ hm hseg hA₀
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₁, .values [.i32 h]⟩) hA₁
  have st₆ : Step P NH ⟨s₁, {}, (SingleThreaded.Ctx.frame [] 0 F₁
      (.label [] 0 [] (.top [.i32 2] (expression [.call ⟨2⟩])) []) []).fill
        (Result.values [.i32 h]).toAdmin⟩
      ⟨s₁, {}, (bodyCtx F₁ []).fill
        (vals [.i32 2, .i32 h] ++ [.ref (.func 2), .callRefType f₂.type])⟩ :=
    step_body (step_mid [.i32 2, .i32 h] [] (step_call (x := ⟨2⟩) (by rw [hF₁f]; rfl) hf₂))
  have hd₃ : decompose? s₁ ((bodyCtx F₁ []).fill
      (vals [.i32 2, .i32 h] ++ [.ref (.func 2), .callRefType f₂.type])) =
      some (bodyCtx F₁ [], 2, 2, [.i32 2, .i32 h]) :=
    decompose_fill _ trivial hf₂ he₂ (by rw [hn₂]; rfl) hc₂
  have t₆ := TSession.call (TSession.of_core_steps t₅ st₆.steps) hd₃
  have hco₂ : calloutAt? blobEcho (some 0) ⟨s₁, {}, (SingleThreaded.Ctx.frame [] 0 F₁
      (.label [] 0 [] (.top [.i32 2] (expression [.call ⟨2⟩])) []) []).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨"sexp", "blob", .func ⟨0⟩⟩ (some 0) s₁ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? blobEcho (some 0) ⟨s₁, {}, (bodyCtx F₁ []).fill
      (vals [.i32 2, .i32 h] ++ [.ref (.func 2), .callRefType f₂.type])⟩ =
      some (calloutIn ⟨"input", "finish", .func ⟨1⟩⟩ (some 0) s₁ [.i32 2, .i32 h]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hb : (calloutIn ⟨"sexp", "blob", .func ⟨0⟩⟩ (some 0) s₁ [.i32 0, .i32 2]).bytes32 =
      some cs := by
    simp only [Callout.bytes32, calloutIn, Callout.args2, Callout.i32?, Val.i32,
      Option.bind_eq_bind, Option.bind_some, Callout.segment, hm]
    exact hseg
  have hbl : mixAnswer {} {} (calloutIn ⟨"sexp", "blob", .func ⟨0⟩⟩ (some 0) s₁
      [.i32 0, .i32 2]) ⟨.values [.i32 h], memOf (some 0) s₁⟩ =
      some (.w (.write (.atom ⟨.bytes, by decide, cs⟩) [] h)) :=
    mixAnswer_w (memWrite_blob rfl hb)
  have hfin : mixCall {} {} (calloutIn ⟨"input", "finish", .func ⟨1⟩⟩ (some 0) s₁
      [.i32 2, .i32 h]) = some (.p (.finish 2 h)) := by
    simp only [mixCall, pullFinish, calloutIn, Val.i32, usedOfI32, ↓reduceIte]
    rfl
  have e₄ : mR.answerTags (calloutIn ⟨"sexp", "blob", .func ⟨0⟩⟩ (some 0) s₁
      [.i32 0, .i32 2]) ⟨.values [.i32 h], memOf (some 0) s₁⟩ =
      [.inp (.w (.write (.atom ⟨.bytes, by decide, cs⟩) [] h))] := by
    rw [answerTags_mR, hbl]; rfl
  have e₅ : mR.callTags (calloutIn ⟨"input", "finish", .func ⟨1⟩⟩ (some 0) s₁
      [.i32 2, .i32 h]) = [.inp (.p (.finish 2 h))] := by
    rw [callTags_mR, hfin]; rfl
  rw [hco₂, hco₃] at t₆
  simp only [Option.elim, e₄, e₅] at t₆
  exact ⟨_, by simpa using t₆⟩

/-- **One invocation of `run` whose `blob` call traps**: after `read(0, 16)` answered in `s₁`
over the chunk `cs`, the trap ends the invocation; the chunk is decoded, nothing else. -/
theorem be_trap_round (hI : IsSpecInstance blobEcho mt Is c)
    (hp : prep blobEcho = some (c, none))
    (t : TSession P L blobEcho (some 0) mR c q₀ Is.addrs p w (c', k₀) ts)
    (hp' : p ≠ .run) (fin : Finished p.started c') (hfs : c'.store.funcs = c.store.funcs)
    (hs₁ : s₁.funcs = c.store.funcs) (hm : memOf (some 0) s₁ = some b)
    (hseg : segOf b 0 2 = some cs)
    (hA₀ : L.Ans k₀ ⟨0, c'.store, [.i32 0, .i32 16]⟩ ⟨s₁, .values [.i32 2]⟩ k₁)
    (hA₁ : L.Ans k₁ ⟨1, s₁, [.i32 0, .i32 2]⟩ ⟨s₁, .trap⟩ k₂) :
    TSession P L blobEcho (some 0) mR c q₀ Is.addrs .idle false (⟨s₁, {}, [.trap]⟩, k₂)
      (ts ++ [.enter none, .inp (.p (.feed cs)), .exit none]) := by
  obtain ⟨E, F₁, f₁, f₂, rfl, -, -, -, -, -, hd₂, t₄⟩ :=
    be_prefix hI hp t hp' fin hfs hs₁ hm hseg hA₀
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₁, .trap⟩) hA₁
  have st₆ : Step P NH ⟨s₁, {}, (SingleThreaded.Ctx.frame [] 0 F₁
      (.label [] 0 [] (.top [.i32 2] (expression [.call ⟨2⟩])) []) []).fill
        (Result.trap).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] [.trap]]]⟩ :=
    step_body (Step.trapInstrs (vs := [.i32 2]) (rest := expression [.call ⟨2⟩]) (.inl (by simp)))
  have st₇ : Step P NH ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] [.trap]]]⟩
      ⟨s₁, {}, [.frame 0 F₁ [.trap]]⟩ := .ctxtFrame .trapLabel
  have st₈ : Step P NH ⟨s₁, {}, [.frame 0 F₁ [.trap]]⟩ ⟨s₁, {}, [.trap]⟩ := .trapFrame
  have t₆ := TSession.ret (r := .trap)
    (TSession.of_core_steps t₅ ((st₆.steps.trans st₇.steps).trans st₈.steps)) rfl
  have hco₂ : calloutAt? blobEcho (some 0) ⟨s₁, {}, (SingleThreaded.Ctx.frame [] 0 F₁
      (.label [] 0 [] (.top [.i32 2] (expression [.call ⟨2⟩])) []) []).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨"sexp", "blob", .func ⟨0⟩⟩ (some 0) s₁ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hbl : mixAnswer {} {} (calloutIn ⟨"sexp", "blob", .func ⟨0⟩⟩ (some 0) s₁
      [.i32 0, .i32 2]) ⟨.trap, memOf (some 0) s₁⟩ = none := by
    simp [mixAnswer, memWrite, replyI32, pullRead, calloutIn]
  have e₄ : mR.answerTags (calloutIn ⟨"sexp", "blob", .func ⟨0⟩⟩ (some 0) s₁
      [.i32 0, .i32 2]) ⟨.trap, memOf (some 0) s₁⟩ = [] := by
    rw [answerTags_mR, hbl]; rfl
  have e₅ : mR.exitVal .trap (memOf (some 0) s₁) = none := rfl
  rw [hco₂] at t₆
  simp only [Option.elim, e₄, e₅] at t₆
  simpa using t₆

end Round

/-- **The mixed trace of the session.** -/
theorem be_traces (P : Profile) (q : BitVec 32) :
    [.w .enter, .p (.feed [0x68, 0x69]), .w (.write (.atom hiBytes) [] q), .p (.finish 2 q)] ∈
      mixTraces P (ReplyEnvs blobReply) 0 blobEcho {} {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists beSpec_some
  obtain ⟨c, st, hp, rfl, -, -⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, -, hml, -⟩ := be_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page beMem hp
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := 0) (n := PackSize.i16.width / 8)
    ((0x6968 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  have hs₁ : hiStore c.store = c.store.setMem 0 { mi with bytes := b } := by
    simp only [hiStore, hmi, hst, Option.bind_some, Option.map_some, Option.getD_some]
  have hm : memOf (some 0) (hiStore c.store) = some b := by rw [hs₁]; exact memOf_setMem hml
  have hseg : segOf b 0 2 = some [0x68, 0x69] := by
    have hz : b.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst).trans hsize
    unfold segOf
    rw [readBytes_toList (by rw [hz]; decide)]
    exact congrArg some ((Silmaril.Wasm.Logic.Core.bytesAt_store_same hst).trans (by decide))
  have t₀ : TSession P (blobEnv q) blobEcho (some 0) mR c () Is.addrs .inst false (c, ()) [] :=
    .start
  obtain ⟨c'', t⟩ := be_round (L := blobEnv q) (k₁ := ()) (k₂ := ()) hI hp t₀ (by decide)
    ⟨[], hcode⟩ rfl
    (hiStore_keeps c.store).1 hm hseg (h := q) (.inl ⟨rfl, rfl, rfl⟩) (.inr (.inl ⟨rfl, rfl⟩))
  refine ⟨_, ⟨mt, Is, c, hI, blobEnv q, (), blobEnv_reply q _, .run, true, _,
    by rw [hmem0]; exact t⟩, ?_⟩
  rfl

/-- **`blobEcho` relates `68 69` to the byte atom `68 69`**, for every profile and every pair of
policies whose sentinels are not the handle `q` the host returns. -/
theorem be_live (P : Profile) (pol : Policy (BitVec 32)) (ppol : PPolicy (BitVec 32))
    {q : BitVec 32} (hq : pol.sentinel ≠ some q) (hpq : ppol.sentinel ≠ q) :
    (([0x68, 0x69] : List UInt8), bytesAtom [0x68, 0x69]) ∈
      memMixedRel P (ReplyEnvs blobReply) 0 blobEcho {} {} pol ppol := by
  let σ : Env (BitVec 32) SymStrBytesSExp :=
    Function.update Env.empty q (some (.atom hiBytes))
  have hres : resolve ppol σ ([0x68, 0x69] : List UInt8) q =
      some {(([0x68, 0x69] : List UInt8), bytesAtom [0x68, 0x69])} := by
    unfold resolve
    split_ifs with h
    · exact absurd h.symm hpq
    · simp [σ, bytesAtom]
  let B : Set SymStrBytesSExp := insert (.atom hiBytes) ∅
  let H := mixed (V := UInt8) (sexpW MemAtom) pol ppol
  have r₄ : H.Run ⟨⟨σ, B, .live⟩, ⟨[], [0x68, 0x69], .live⟩⟩ [.p (.finish 2 q)]
      ⟨⟨σ, B, .live⟩, ⟨[], [], .live⟩⟩
      ({(([0x68, 0x69] : List UInt8), bytesAtom [0x68, 0x69])} ∪ ∅) :=
    .cons (.p rfl (.ret (s := ⟨[], [0x68, 0x69], .live⟩) (e := .finish 2 q)
      (w := [0x68, 0x69]) (h := q) rfl ⟨by decide, rfl, rfl, rfl⟩ hres)) (.nil _)
  have r₃ : H.Run ⟨⟨Env.empty, ∅, .live⟩, ⟨[], [0x68, 0x69], .live⟩⟩
      [.w (.write (.atom hiBytes) [] q), .p (.finish 2 q)] ⟨⟨σ, B, .live⟩, ⟨[], [], .live⟩⟩
      (chaosPairs .live ∪
        ({(([0x68, 0x69] : List UInt8), bytesAtom [0x68, 0x69])} ∪ ∅)) :=
    .cons (.w (.writeOk (t := (.atom hiBytes : SymStrBytesSExp)) rfl ⟨hq, .inl rfl⟩
      fun _ h => by cases h)) r₄
  have hrun : H.Run MState.init
      [.w .enter, .p (.feed [0x68, 0x69]), .w (.write (.atom hiBytes) [] q), .p (.finish 2 q)]
      ⟨⟨σ, B, .live⟩, ⟨[], [], .live⟩⟩
      (chaosPairs .live ∪ (∅ ∪ (chaosPairs .live ∪
        ({(([0x68, 0x69] : List UInt8), bytesAtom [0x68, 0x69])} ∪ ∅)))) :=
    .cons (.w .enter) (.cons (.p (ws := WState.init) rfl (.feed _)) r₃)
  simp only [memMixedRel, mixedRel, Host.lang]
  exact Set.mem_biUnion (be_traces P q) ⟨_, _, hrun, by simp⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix
