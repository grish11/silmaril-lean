module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMixStale

/-!
# Proofs: live sessions of `drainEcho`

Concrete traced sessions, for every profile and every sentinel whose shape `deOk z` holds (all
of them, `deOk_all`):

* `de_drains`: from the start of `run`, the five drain calls `finish(k, z)` are decoded at their
  calls (`k = 16, 8, 4, 2, 1`) and answered with nothing;
* `de_round_call`, `de_round`: one invocation after a finished run: drains, `read(0, 16)`
  answered over a chunk, `blob(0, 2)` answered with `h`, the call `finish(2, h)` (and, for
  `de_round`, its answer and the return of `run`);
* `de_trap_round`: one invocation whose `blob` call traps after `read` was answered.

The traces: `hiEnv q` (one invocation reading `68 69`), `twoEnv q₁ q₂` (two invocations reading
`68 69`, then `69 68`), `trapEnv q` (the stale-chunk host of `blobEcho`: the first `blob` traps,
leaving `68 69` buffered; the second invocation drains it, reads `69 68`). Their mixed runs relate
`(68 69, bytes 68 69)`, resp. also `(69 68, bytes 69 68)`, resp. `(69 68, bytes 69 68)`: the
drains overrun on an empty buffer (`onOverrun` `callTrap` or `ignore`), and in the stale session
`finish(2, z)` consumes the two stale bytes.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats
  Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pull
  Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix Silmaril.Wasm.Game.HandleAccept.MemSound.Exact
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
open Silmaril.Wasm.Logic.Core (bytesAt)

/-! ## Admitted hosts -/

theorem deEnv_reply {rd : Nat → Store Nat → Store Nat} {bl : Nat → Result}
    (hrd : ∀ k s, KeepsCode s (rd k s) ∧ MemGrows s (rd k s))
    (hbl : ∀ k vs, bl k = .values vs → ∃ h, vs = [.i32 h]) (s : Store Nat) :
    ReplyEnvs blobReply s (deEnv rd bl) := by
  rintro k e a k' (⟨h2, rfl, -⟩ | ⟨h0, ha, rfl, -⟩ | ⟨h1, rfl, -⟩)
  · refine ⟨⟨rfl, rfl⟩, fun mi h => ⟨mi, h, le_rfl⟩, fun vs hv => ?_⟩
    cases hv
    refine ⟨fun h => ?_, fun h => ?_, fun _ => rfl⟩
    · rw [h2] at h; cases h
    · rw [h2] at h; cases h
  · refine ⟨(hrd k _).1, (hrd k _).2, fun vs hv => ?_⟩
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
    obtain ⟨h, rfl⟩ := hbl k vs hv
    refine ⟨fun h' => ?_, fun _ => ⟨h, rfl⟩, fun h' => ?_⟩
    · rw [h1] at h'; cases h'
    · rw [h1] at h'; cases h'

theorem hiihStore_ok (k : Nat) (s : Store Nat) :
    KeepsCode s ((if k = 0 then hiStore else ihStore) s) ∧
      MemGrows s ((if k = 0 then hiStore else ihStore) s) := by
  split
  · exact ⟨Pull.hiStore_keeps s, PullMix.hiStore_grows s⟩
  · exact ⟨PullMix.ihStore_keeps s, PullMix.ihStore_grows s⟩

theorem hiEnv_reply (q : BitVec 32) (s : Store Nat) : ReplyEnvs blobReply s (hiEnv q) :=
  deEnv_reply (fun _ s => ⟨Pull.hiStore_keeps s, PullMix.hiStore_grows s⟩)
    (fun _ _ hv => ⟨q, (Result.values.inj hv).symm⟩) s

theorem twoEnv_reply (q₁ q₂ : BitVec 32) (s : Store Nat) :
    ReplyEnvs blobReply s (twoEnv q₁ q₂) :=
  deEnv_reply hiihStore_ok (fun k vs hv => by
    split at hv
    · exact ⟨q₁, (Result.values.inj hv).symm⟩
    · exact ⟨q₂, (Result.values.inj hv).symm⟩) s

theorem trapEnv_reply (q : BitVec 32) (s : Store Nat) : ReplyEnvs blobReply s (trapEnv q) :=
  deEnv_reply hiihStore_ok (fun k vs hv => by
    split at hv
    · cases hv
    · exact ⟨q, (Result.values.inj hv).symm⟩) s

/-! ## Sessions -/

/-- The configuration of the body of `run` in frame `F`. -/
abbrev bodyCfg (s : Store Nat) (F : Frame) (code : List Admin) : Config Nat :=
  ⟨s, {}, [.frame 0 F [.label 0 [] code]]⟩

/-- The tags of the drain. -/
abbrev drainTags (z : BitVec 32) : List (Tag Unit MixEv Unit Unit) :=
  [.inp (.p (.finish 16 z)), .inp (.p (.finish 8 z)), .inp (.p (.finish 4 z)),
    .inp (.p (.finish 2 z)), .inp (.p (.finish 1 z))]

theorem callTags_mR' (o : Callout) : mR.callTags o = (mixCall {} {} o).toList.map Tag.inp := by
  simp [Roles.callTags, mR, mixRoles]

theorem answerTags_mR' (o : Callout) (w : HostReply) :
    mR.answerTags o w = (mixAnswer {} {} o w).toList.map Tag.inp := rfl

section Session

variable {P : Profile} {z : BitVec 32} {L : SEnv UImp} {c : Config Nat} {q₀ : L.S}
  {addrs : List Nat} {mt : CModuleType} {Is : ScalarInstance}

/-- **One drain call** `finish(k, z)`, answered with nothing. -/
theorem de_drain_step (hz : deOk z = true) (hp : prep (drainEcho z) = some (c, none))
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3]) {s : Store Nat}
    (hs : s.funcs = c.store.funcs) {k : BitVec 32} {kn : Nat} (hk : usedOfI32 k = some kn)
    {rest : List Instr} {q q' : L.S} {ts : List (Tag Unit MixEv Unit Unit)}
    (t : TSession P L (drainEcho z) (some 0) mR c q₀ addrs .run false
      (bodyCfg s F (expression (drainCall k z ++ rest)), q) ts)
    (hA : L.Ans q ⟨2, s, [.i32 k, .i32 z]⟩ ⟨s, .values []⟩ q') :
    TSession P L (drainEcho z) (some 0) mR c q₀ addrs .run false
      (bodyCfg s F (expression rest), q') (ts ++ [.inp (.p (.finish kn z))]) := by
  obtain ⟨-, -, -, -, -, -, f₀, f₁, f₂, f₃, hf, -, -, h2, -⟩ := de_facts hz hp
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  have hf₂ : s.funcs[2]? = some f₂ := by rw [hs, hf]; rfl
  have st : Step P NH (bodyCfg s F (expression (drainCall k z ++ rest)))
      ⟨s, {}, (bodyCtx F (expression rest)).fill
        (vals [.i32 k, .i32 z] ++ [.ref (.func 2), .callRefType f₂.type])⟩ :=
    step_body (step_mid [.i32 k, .i32 z] (expression rest)
      (step_call (x := ⟨2⟩) (by rw [hFf]; rfl) hf₂))
  have hd : decompose? s ((bodyCtx F (expression rest)).fill
      (vals [.i32 k, .i32 z] ++ [.ref (.func 2), .callRefType f₂.type])) =
      some (bodyCtx F (expression rest), 2, 2, [.i32 k, .i32 z]) :=
    decompose_fill _ trivial hf₂ he₂ (by rw [hn₂]; rfl) hc₂
  have t₁ := TSession.call (TSession.of_core_steps t st.steps) hd
  have t₂ := TSession.answer t₁ hd (a := ⟨s, .values []⟩) hA
  have hco : calloutAt? (drainEcho z) (some 0) ⟨s, {}, (bodyCtx F (expression rest)).fill
      (vals [.i32 k, .i32 z] ++ [.ref (.func 2), .callRefType f₂.type])⟩ =
      some (calloutIn finImp (some 0) s [.i32 k, .i32 z]) := by
    unfold calloutAt?; rw [hd]; rfl
  have hfin : mixCall {} {} (calloutIn finImp (some 0) s [.i32 k, .i32 z]) =
      some (.p (.finish kn z)) := by
    simp [mixCall, memAccept, pullFinish, calloutIn, Val.i32, hk]
  have hans : mixAnswer {} {} (calloutIn finImp (some 0) s [.i32 k, .i32 z])
      ⟨.values [], memOf (some 0) s⟩ = none := by
    unfold mixAnswer; rw [memWrite_fin]; simp [pullRead, calloutIn]
  rw [hco] at t₂
  simp only [Option.elim, callTags_mR', answerTags_mR', hfin, hans, Option.toList_some,
    Option.toList_none, List.map_cons, List.map_nil, List.append_nil] at t₂
  exact t₂

/-- **The drain**, answered with nothing. -/
theorem de_drains (hz : deOk z = true) (hp : prep (drainEcho z) = some (c, none))
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3]) {s : Store Nat}
    (hs : s.funcs = c.store.funcs) {q : L.S} {ts : List (Tag Unit MixEv Unit Unit)}
    (t : TSession P L (drainEcho z) (some 0) mR c q₀ addrs .run false
      (bodyCfg s F (expression (drainBody z)), q) ts)
    (hA : ∀ k, L.Ans q ⟨2, s, [.i32 k, .i32 z]⟩ ⟨s, .values []⟩ q) :
    TSession P L (drainEcho z) (some 0) mR c q₀ addrs .run false
      (bodyCfg s F (expression blobEchoBody), q) (ts ++ drainTags z) := by
  simp only [drainBody, List.append_assoc] at t
  have t₁ := de_drain_step hz hp hFf hs (k := 16) (kn := 16) (by decide) t (hA _)
  have t₂ := de_drain_step hz hp hFf hs (k := 8) (kn := 8) (by decide) t₁ (hA _)
  have t₃ := de_drain_step hz hp hFf hs (k := 4) (kn := 4) (by decide) t₂ (hA _)
  have t₄ := de_drain_step hz hp hFf hs (k := 2) (kn := 2) (by decide) t₃ (hA _)
  have t₅ := de_drain_step hz hp hFf hs (k := 1) (kn := 1) (by decide) t₄ (hA _)
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using t₅

/-- The invocation of `run` after a finished run: the body in its frame. -/
theorem de_invoke (hz : deOk z = true) (hI : IsSpecInstance (drainEcho z) mt Is c)
    (hp : prep (drainEcho z) = some (c, none)) {p : IOAccept.Phase} {w : Bool} {c' : Config Nat}
    {q : L.S} {ts : List (Tag Unit MixEv Unit Unit)}
    (t : TSession P L (drainEcho z) (some 0) mR c q₀ Is.addrs p w (c', q) ts)
    (hp' : p ≠ .run) (fin : Finished p.started c') (hfs : c'.store.funcs = c.store.funcs) :
    ∃ F : Frame, F.module.funcs = [0, 1, 2, 3] ∧ F.locals = deD ∧
      TSession P L (drainEcho z) (some 0) mR c q₀ Is.addrs .run false
        (bodyCfg c'.store F (expression (drainBody z)), q) (ts ++ [.enter none]) := by
  obtain ⟨-, -, -, hexp, -, -, f₀, f₁, f₂, f₃, hf, -, -, -, h3⟩ := de_facts hz hp
  obtain ⟨code, ps, rs, hcode3, hloc, hbody, he, hps, hrs, hfuncs, -, hD⟩ := fnOk_spec h3
  obtain ⟨cc, st', hp'', -, -, haddr⟩ := prep_of_spec hI
  obtain ⟨hcc, -⟩ := Prod.mk.inj (Option.some.inj (hp''.symm.trans hp))
  rw [hcc] at haddr
  have hf3 : c'.store.funcs[3]? = some f₃ := by rw [hfs, hf]; rfl
  have hok : InvokeOk c'.store 3 [] := ⟨f₃, ps, rs, hf3, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 3 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t hp' fin ha hok
  have st₀ : Step P NH (invoke c'.store 3 [])
      ⟨c'.store, {}, [.frame 0 (Frame.forCall f₃.module [] [.i32])
        [.label 0 [] (expression (drainBody z))]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c'.store) (f := {})
      (c := .callRefType ((c'.store.funcs[3]?.map FuncInst.type).getD default)) (vs := [])
      (a := 3) (fi := f₃) (code := code) trivial hf3 he (by rw [hps]; rfl) hcode3
    rw [hrs, hloc, hbody] at h
    exact h
  refine ⟨Frame.forCall f₃.module [] [.i32], by simp [Frame.forCall, hfuncs],
    by simp [Frame.forCall, hD], ?_⟩
  exact TSession.of_core_steps t₁ st₀.steps

/-- The tail up to the call of `blob(0, 2)`: `read(0, 16)` answered in `s₁` with `2` over the
chunk `cs`. -/
theorem de_tail_prefix (hz : deOk z = true) (hp : prep (drainEcho z) = some (c, none))
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3]) (hFl : F.locals = deD) {s s₁ : Store Nat}
    (hs : s.funcs = c.store.funcs) (hs₁ : s₁.funcs = c.store.funcs) {b : ByteArray}
    (hm : memOf (some 0) s₁ = some b) {cs : List UInt8} (hseg : segOf b 0 2 = some cs)
    {k₀ k₁ : L.S} {ts : List (Tag Unit MixEv Unit Unit)}
    (t : TSession P L (drainEcho z) (some 0) mR c q₀ addrs .run false
      (bodyCfg s F (expression blobEchoBody), k₀) ts)
    (hA₀ : L.Ans k₀ ⟨0, s, [.i32 0, .i32 16]⟩ ⟨s₁, .values [.i32 2]⟩ k₁) :
    ∃ (E : SingleThreaded.Ctx) (F₁ : Frame) (f₁ f₂ : FuncInst Nat),
      E = .frame [] 0 F₁ (.label [] 0 [] (.top [.i32 2] (expression [.call ⟨2⟩])) []) [] ∧
      F₁.module.funcs = [0, 1, 2, 3] ∧ s₁.funcs[1]? = some f₁ ∧ s₁.funcs[2]? = some f₂ ∧
      stubOk 1 2 f₁ = true ∧ stubOk 2 2 f₂ = true ∧
      decompose? s₁ (E.fill (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])) =
        some (E, 1, 1, [.i32 0, .i32 2]) ∧
      TSession P L (drainEcho z) (some 0) mR c q₀ addrs .run true
        (⟨s₁, {}, E.fill (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩, k₁)
        (ts ++ [.inp (.p (.feed cs))]) := by
  obtain ⟨-, -, -, -, -, -, f₀, f₁, f₂, f₃, hf, h0, h1, h2, -⟩ := de_facts hz hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  have hfs' : ∀ s : Store Nat, s.funcs = c.store.funcs → s.funcs[0]? = some f₀ ∧
      s.funcs[1]? = some f₁ ∧ s.funcs[2]? = some f₂ := by
    intro s h; rw [h, hf]; exact ⟨rfl, rfl, rfl⟩
  let F₁ := F.setLocal ⟨0⟩ (.i32 2)
  have hF₁f : F₁.module.funcs = [0, 1, 2, 3] := hFf
  have hs₁f := hfs' _ hs₁
  -- read(0, 16)
  have st₁ : Step P NH (bodyCfg s F (expression blobEchoBody))
      ⟨s, {}, (bodyCtx F (expression (blobEchoBody.drop 3))).fill
        (vals [.i32 0, .i32 16] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 16] (expression (blobEchoBody.drop 3))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) (hfs' _ hs).1))
  have hd₁ : decompose? s ((bodyCtx F (expression (blobEchoBody.drop 3))).fill
      (vals [.i32 0, .i32 16] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (blobEchoBody.drop 3)), 0, 0, [.i32 0, .i32 16]) :=
    decompose_fill _ trivial (hfs' _ hs).1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t st₁.steps) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 2]⟩) hA₀
  -- local.set 0; local.get 0; i32.const 0; local.get 0; blob(0, 2)
  have st₂ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (blobEchoBody.drop 3))).fill
      (Result.values [.i32 2]).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (blobEchoBody.drop 4))]]⟩ :=
    step_body (step_mid [] (expression (blobEchoBody.drop 4))
      (step_localSet (x := ⟨0⟩) (v := .i32 2) (by simp [hFl, deD, Idx.toNat])))
  have hv : F₁.local? ⟨0⟩ = some (some (.i32 2)) := by
    simp [F₁, Frame.local?, Frame.setLocal, hFl, deD, Idx.toNat]
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
  have hco₁ : calloutAt? (drainEcho z) (some 0) ⟨s, {},
      (bodyCtx F (expression (blobEchoBody.drop 3))).fill
        (vals [.i32 0, .i32 16] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn readImp (some 0) s [.i32 0, .i32 16]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? (drainEcho z) (some 0) ⟨s₁, {}, E₂.fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn blobImp (some 0) s₁ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hrd : mixAnswer {} {} (calloutIn readImp (some 0) s [.i32 0, .i32 16])
      ⟨.values [.i32 2], memOf (some 0) s₁⟩ = some (.p (.feed cs)) := by
    have hr : pullRead {} (calloutIn readImp (some 0) s [.i32 0, .i32 16])
        ⟨.values [.i32 2], memOf (some 0) s₁⟩ = some (.feed cs) := by
      simp [pullRead, calloutIn, Val.i32, replyI32, hm]
      exact hseg
    unfold mixAnswer
    rw [memWrite_read]
    dsimp only
    rw [hr]
    rfl
  have hn₁' : mixCall {} {} (calloutIn readImp (some 0) s [.i32 0, .i32 16]) = none := by
    simp [mixCall, memAccept, pullFinish, calloutIn]
  have hn₂' : mixCall {} {} (calloutIn blobImp (some 0) s₁ [.i32 0, .i32 2]) = none := by
    simp [mixCall, memAccept, pullFinish, calloutIn]
  rw [hco₁, hco₂] at t₄
  have e₁ : mR.callTags (calloutIn readImp (some 0) s [.i32 0, .i32 16]) = [] := by
    rw [callTags_mR', hn₁']; rfl
  have e₂ : mR.answerTags (calloutIn readImp (some 0) s [.i32 0, .i32 16])
      ⟨.values [.i32 2], memOf (some 0) s₁⟩ = [.inp (.p (.feed cs))] := by
    rw [answerTags_mR', hrd]; rfl
  have e₃ : mR.callTags (calloutIn blobImp (some 0) s₁ [.i32 0, .i32 2]) = [] := by
    rw [callTags_mR', hn₂']; rfl
  refine ⟨E₂, F₁, f₁, f₂, rfl, hF₁f, hs₁f.2.1, hs₁f.2.2, h1, h2, hd₂, ?_⟩
  simp only [Option.elim, e₁, e₂, e₃] at t₄
  simpa using t₄

/-- The events of the tail: the chunk, the write of its atom with handle `h`, `finish(2, h)`. -/
abbrev tailTags (cs : List UInt8) (h : BitVec 32) : List (Tag Unit MixEv Unit Unit) :=
  [.inp (.p (.feed cs)), .inp (.w (.write (.atom ⟨.bytes, by decide, cs⟩) [] h)),
    .inp (.p (.finish 2 h))]

/-- **The tail up to the call of `finish(2, h)`**, `blob(0, 2)` answered with `h` in `s₁`. -/
theorem de_tail_call (hz : deOk z = true) (hp : prep (drainEcho z) = some (c, none))
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3]) (hFl : F.locals = deD) {s s₁ : Store Nat}
    (hs : s.funcs = c.store.funcs) (hs₁ : s₁.funcs = c.store.funcs) {b : ByteArray}
    (hm : memOf (some 0) s₁ = some b) {cs : List UInt8} (hseg : segOf b 0 2 = some cs)
    {h : BitVec 32} {k₀ k₁ k₂ : L.S} {ts : List (Tag Unit MixEv Unit Unit)}
    (t : TSession P L (drainEcho z) (some 0) mR c q₀ addrs .run false
      (bodyCfg s F (expression blobEchoBody), k₀) ts)
    (hA₀ : L.Ans k₀ ⟨0, s, [.i32 0, .i32 16]⟩ ⟨s₁, .values [.i32 2]⟩ k₁)
    (hA₁ : L.Ans k₁ ⟨1, s₁, [.i32 0, .i32 2]⟩ ⟨s₁, .values [.i32 h]⟩ k₂) :
    ∃ (F₁ : Frame) (f₂ : FuncInst Nat),
      decompose? s₁ ((bodyCtx F₁ []).fill
        (vals [.i32 2, .i32 h] ++ [.ref (.func 2), .callRefType f₂.type])) =
        some (bodyCtx F₁ [], 2, 2, [.i32 2, .i32 h]) ∧
      TSession P L (drainEcho z) (some 0) mR c q₀ addrs .run true
        (⟨s₁, {}, (bodyCtx F₁ []).fill
          (vals [.i32 2, .i32 h] ++ [.ref (.func 2), .callRefType f₂.type])⟩, k₂)
        (ts ++ tailTags cs h) := by
  obtain ⟨E, F₁, f₁, f₂, rfl, hF₁f, -, hf₂, -, h2, hd₂, t₄⟩ :=
    de_tail_prefix hz hp hFf hFl hs hs₁ hm hseg t hA₀
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
  have hco₂ : calloutAt? (drainEcho z) (some 0) ⟨s₁, {}, (SingleThreaded.Ctx.frame [] 0 F₁
      (.label [] 0 [] (.top [.i32 2] (expression [.call ⟨2⟩])) []) []).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn blobImp (some 0) s₁ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? (drainEcho z) (some 0) ⟨s₁, {}, (bodyCtx F₁ []).fill
      (vals [.i32 2, .i32 h] ++ [.ref (.func 2), .callRefType f₂.type])⟩ =
      some (calloutIn finImp (some 0) s₁ [.i32 2, .i32 h]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hb : (calloutIn blobImp (some 0) s₁ [.i32 0, .i32 2]).bytes32 = some cs := by
    simp only [Callout.bytes32, calloutIn, Callout.args2, Callout.i32?, Val.i32,
      Option.bind_eq_bind, Option.bind_some, Callout.segment, hm]
    exact hseg
  have hbl : mixAnswer {} {} (calloutIn blobImp (some 0) s₁ [.i32 0, .i32 2])
      ⟨.values [.i32 h], memOf (some 0) s₁⟩ =
      some (.w (.write (.atom ⟨.bytes, by decide, cs⟩) [] h)) :=
    PullMix.mixAnswer_w (PullMix.memWrite_blob rfl hb)
  have hfin : mixCall {} {} (calloutIn finImp (some 0) s₁ [.i32 2, .i32 h]) =
      some (.p (.finish 2 h)) := by
    simp only [mixCall, pullFinish, calloutIn, Val.i32, usedOfI32, ↓reduceIte]
    rfl
  have e₄ : mR.answerTags (calloutIn blobImp (some 0) s₁ [.i32 0, .i32 2])
      ⟨.values [.i32 h], memOf (some 0) s₁⟩ =
      [.inp (.w (.write (.atom ⟨.bytes, by decide, cs⟩) [] h))] := by
    rw [answerTags_mR', hbl]; rfl
  have e₅ : mR.callTags (calloutIn finImp (some 0) s₁ [.i32 2, .i32 h]) =
      [.inp (.p (.finish 2 h))] := by
    rw [callTags_mR', hfin]; rfl
  rw [hco₂, hco₃] at t₆
  simp only [Option.elim, e₄, e₅] at t₆
  exact ⟨F₁, f₂, hd₃, by simpa using t₆⟩

/-- **The tail to the return of `run`**: `finish(2, h)` answered with nothing. -/
theorem de_tail_ret (hz : deOk z = true) (hp : prep (drainEcho z) = some (c, none))
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3]) (hFl : F.locals = deD) {s s₁ : Store Nat}
    (hs : s.funcs = c.store.funcs) (hs₁ : s₁.funcs = c.store.funcs) {b : ByteArray}
    (hm : memOf (some 0) s₁ = some b) {cs : List UInt8} (hseg : segOf b 0 2 = some cs)
    {h : BitVec 32} {k₀ k₁ k₂ k₃ : L.S} {ts : List (Tag Unit MixEv Unit Unit)}
    (t : TSession P L (drainEcho z) (some 0) mR c q₀ addrs .run false
      (bodyCfg s F (expression blobEchoBody), k₀) ts)
    (hA₀ : L.Ans k₀ ⟨0, s, [.i32 0, .i32 16]⟩ ⟨s₁, .values [.i32 2]⟩ k₁)
    (hA₁ : L.Ans k₁ ⟨1, s₁, [.i32 0, .i32 2]⟩ ⟨s₁, .values [.i32 h]⟩ k₂)
    (hA₂ : L.Ans k₂ ⟨2, s₁, [.i32 2, .i32 h]⟩ ⟨s₁, .values []⟩ k₃) :
    TSession P L (drainEcho z) (some 0) mR c q₀ addrs .idle false (⟨s₁, {}, []⟩, k₃)
      (ts ++ tailTags cs h ++ [.exit none]) := by
  obtain ⟨F₁, f₂, hd₃, t₆⟩ := de_tail_call hz hp hFf hFl hs hs₁ hm hseg t hA₀ hA₁
  have t₇ := TSession.answer t₆ hd₃ (a := ⟨s₁, .values []⟩) hA₂
  have hans : mixAnswer {} {} (calloutIn finImp (some 0) s₁ [.i32 2, .i32 h])
      ⟨.values [], memOf (some 0) s₁⟩ = none := by
    unfold mixAnswer; rw [memWrite_fin]; simp [pullRead, calloutIn]
  have hco₃ : calloutAt? (drainEcho z) (some 0) ⟨s₁, {}, (bodyCtx F₁ []).fill
      (vals [.i32 2, .i32 h] ++ [.ref (.func 2), .callRefType f₂.type])⟩ =
      some (calloutIn finImp (some 0) s₁ [.i32 2, .i32 h]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have st₇ : Step P NH ⟨s₁, {}, (bodyCtx F₁ []).fill (Result.values []).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F₁ (vals [])]⟩ :=
    .ctxtFrame (Step.labelVals (vs := []))
  have st₈ : Step P NH ⟨s₁, {}, [.frame 0 F₁ (vals [])]⟩ ⟨s₁, {}, vals []⟩ :=
    Step.frameVals (vs := []) rfl
  have t₈ := TSession.ret (r := .values [])
    (TSession.of_core_steps t₇ (st₇.steps.trans st₈.steps)) rfl
  rw [hco₃] at t₈
  have e₆ : mR.answerTags (calloutIn finImp (some 0) s₁ [.i32 2, .i32 h])
      ⟨.values [], memOf (some 0) s₁⟩ = [] := by
    rw [answerTags_mR', hans]; rfl
  have e₇ : mR.exitVal (.values []) (memOf (some 0) s₁) = none := rfl
  simp only [Option.elim, e₆, e₇, List.append_nil] at t₈
  exact t₈

/-- **The tail whose `blob` call traps.** -/
theorem de_tail_trap (hz : deOk z = true) (hp : prep (drainEcho z) = some (c, none))
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3]) (hFl : F.locals = deD) {s s₁ : Store Nat}
    (hs : s.funcs = c.store.funcs) (hs₁ : s₁.funcs = c.store.funcs) {b : ByteArray}
    (hm : memOf (some 0) s₁ = some b) {cs : List UInt8} (hseg : segOf b 0 2 = some cs)
    {k₀ k₁ k₂ : L.S} {ts : List (Tag Unit MixEv Unit Unit)}
    (t : TSession P L (drainEcho z) (some 0) mR c q₀ addrs .run false
      (bodyCfg s F (expression blobEchoBody), k₀) ts)
    (hA₀ : L.Ans k₀ ⟨0, s, [.i32 0, .i32 16]⟩ ⟨s₁, .values [.i32 2]⟩ k₁)
    (hA₁ : L.Ans k₁ ⟨1, s₁, [.i32 0, .i32 2]⟩ ⟨s₁, .trap⟩ k₂) :
    TSession P L (drainEcho z) (some 0) mR c q₀ addrs .idle false (⟨s₁, {}, [.trap]⟩, k₂)
      (ts ++ [.inp (.p (.feed cs)), .exit none]) := by
  obtain ⟨E, F₁, f₁, f₂, rfl, -, -, -, -, -, hd₂, t₄⟩ :=
    de_tail_prefix hz hp hFf hFl hs hs₁ hm hseg t hA₀
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
  have hco₂ : calloutAt? (drainEcho z) (some 0) ⟨s₁, {}, (SingleThreaded.Ctx.frame [] 0 F₁
      (.label [] 0 [] (.top [.i32 2] (expression [.call ⟨2⟩])) []) []).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn blobImp (some 0) s₁ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hbl : mixAnswer {} {} (calloutIn blobImp (some 0) s₁ [.i32 0, .i32 2])
      ⟨.trap, memOf (some 0) s₁⟩ = none := by
    simp [mixAnswer, memWrite, replyI32, pullRead, calloutIn]
  have e₄ : mR.answerTags (calloutIn blobImp (some 0) s₁ [.i32 0, .i32 2])
      ⟨.trap, memOf (some 0) s₁⟩ = [] := by
    rw [answerTags_mR', hbl]; rfl
  have e₅ : mR.exitVal .trap (memOf (some 0) s₁) = none := rfl
  rw [hco₂] at t₆
  simp only [Option.elim, e₄, e₅] at t₆
  simpa using t₆

end Session

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact
