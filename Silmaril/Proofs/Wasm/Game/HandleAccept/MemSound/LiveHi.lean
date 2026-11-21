module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hi

/-!
# Proofs: `hiMod` accepts the symbol `hi`

Against the counting host `countEnv hiOut` started at `q` (it answers `symbol` with the handle
`q`, `accept` with nothing, in the caller's store), the traced session of `hiMod`

1. invokes `run` (address `2`) from the instantiated configuration (`enter`);
2. runs `i32.store16` (the memory has one page) and reaches `symbol(0, 2)`, whose callout reads
   `68 69`; the host answers `q`, decoded as the write of the symbol `hi` with handle `q`;
3. reaches `accept(q)`, decoded at the call.

Its writer trace is `[enter, write hi [] q, accept q]`; in the store semantics, with `q` not the
policy's sentinel, `q` denotes `hi` and is accepted.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Hi

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live

theorem hiSpec_some : (Silmaril.Wasm.Verify.specInstance? hiMod).isSome = true := by
  decide +kernel

theorem hiMem : memSizes hiMod = [65536] := by decide +kernel

theorem hiOut_shape (k : Nat) (q : BitVec 32) : hiShape k (hiOut k q) := by
  rcases k with _ | _ | k <;> simp [hiShape, hiOut]

/-- **The writer trace of the session.** -/
theorem hi_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write (.atom hiAtom) [] q, .accept q] ∈
      memTraces P (ReplyEnvs hiReply) 0 hiMod {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists hiSpec_some
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := hi_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page hiMem hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, -⟩ := fnOk_spec h2
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  -- the store and frame
  have hf0 : c.store.funcs[0]? = some f₀ := by rw [hf]; rfl
  have hf1 : c.store.funcs[1]? = some f₁ := by rw [hf]; rfl
  have hf2 : c.store.funcs[2]? = some f₂ := by rw [hf]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  let F : Frame := Frame.forCall f₂.module [] []
  have hFf : F.module.funcs = [0, 1, 2] := by simp [F, Frame.forCall, hfuncs]
  have hFm : F.module.mems = [0] := by simp [F, Frame.forCall, hmems2]
  -- the session
  let L := countEnv hiOut
  let R := memRoles {}
  have t₀ : TSession P L hiMod (some 0) R c q Is.addrs .inst false (c, q) [] := .start
  have hok : InvokeOk c.store 2 [] := ⟨f₂, ps, rs, hf2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 2 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  -- enter `run`
  have st₀ : Step P NH (invoke c.store 2 [])
      ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression hiBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[2]?.map FuncInst.type).getD default)) (vs := [])
      (a := 2) (fi := f₂) (code := code) trivial hf2 he (by rw [hps]; rfl) hcode2
    rw [hrs, hloc, hbody] at h
    exact h
  -- `i32.store16`
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i16.width / 8) ((0x6968 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  let s₁ := c.store.setMem 0 { mi with bytes := b }
  obtain ⟨-, hl₁, hfs₁⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  have hf0' : s₁.funcs[0]? = some f₀ := by rw [hfs₁]; exact hf0
  have hf1' : s₁.funcs[1]? = some f₁ := by rw [hfs₁]; exact hf1
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression hiBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression [.intConst .i32 0, .intConst .i32 2,
        .call ⟨0⟩, .call ⟨1⟩])]]⟩ :=
    step_body (step_mid [] _ (step_storePack hFm hmi hst))
  -- `call 0`
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression [.intConst .i32 0,
      .intConst .i32 2, .call ⟨0⟩, .call ⟨1⟩])]]⟩
      ⟨s₁, {}, (bodyCtx F [.plain (.call ⟨1⟩)]).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 2] [.plain (.call ⟨1⟩)]
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hf0'))
  have hd₁ : decompose? s₁ ((bodyCtx F [.plain (.call ⟨1⟩)]).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F [.plain (.call ⟨1⟩)], 0, 0, [.i32 0, .i32 2]) :=
    decompose_fill _ trivial hf0' he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  -- `call 1`
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F [.plain (.call ⟨1⟩)]).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, (bodyCtx F []).fill (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 q] [] (step_call (x := ⟨1⟩) (by rw [hFf]; rfl) hf1'))
  have hd₂ : decompose? s₁ ((bodyCtx F []).fill
      (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F [], 1, 1, [.i32 q]) :=
    decompose_fill _ trivial hf1' he₁ (by rw [hn₁]; rfl) hc₁
  have t₄ := TSession.call (TSession.of_core_steps t₃ st₃.steps) hd₂
  -- the decoded events
  have hco₁ : calloutAt? hiMod (some 0) ⟨s₁, {}, (bodyCtx F [.plain (.call ⟨1⟩)]).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn ⟨"sexp", "symbol", .func ⟨0⟩⟩ (some 0) s₁ [.i32 0, .i32 2]) := by
    unfold calloutAt?
    rw [hd₁]
    rfl
  have hco₂ : calloutAt? hiMod (some 0) ⟨s₁, {}, (bodyCtx F []).fill
      (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨"sexp", "accept", .func ⟨1⟩⟩ (some 0) s₁ [.i32 q]) := by
    unfold calloutAt?
    rw [hd₂]
    rfl
  have hb : (calloutIn ⟨"sexp", "symbol", .func ⟨0⟩⟩ (some 0) s₁ [.i32 0, .i32 2]).bytes32 =
      some [0x68, 0x69] := by
    rw [bytes32_of_store hml hst rfl]
    decide
  have hw : memWrite {} (calloutIn ⟨"sexp", "symbol", .func ⟨0⟩⟩ (some 0) s₁ [.i32 0, .i32 2])
      ⟨.values [.i32 q], memOf (some 0) s₁⟩ = some (.write (.atom hiAtom) [] q) :=
    memWrite_symbol_eq rfl hb utf8_hi rfl
  have hna : memAccept {} (calloutIn ⟨"sexp", "symbol", .func ⟨0⟩⟩ (some 0) s₁
      [.i32 0, .i32 2]) = none :=
    memAccept_eq_none (by show ("sexp", "symbol") ≠ ("sexp", "accept"); decide)
  have hac : memAccept {} (calloutIn ⟨"sexp", "accept", .func ⟨1⟩⟩ (some 0) s₁ [.i32 q]) =
      some (.accept q) := by
    simp [memAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  rw [hco₁, hco₂] at t₄
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply hiOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₄⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, memRoles]
  rw [hna, hw, hac]
  rfl

/-- **`hiMod` accepts the symbol `hi`**, for every profile and policy. -/
theorem hiMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom hiAtom ∈ memWriterLang P (ReplyEnvs hiReply) 0 hiMod {} pol := by
  have hne : pol.sentinel ≠ some (base pol) := by
    simpa using base_ne pol (k := 0) (by decide)
  simp only [memWriterLang, writerLang, Host.lang]
  refine Set.mem_biUnion (hi_traces P (base pol)) ⟨_, _, .cons .enter
    (.cons (.writeOk rfl ⟨hne, .inl rfl⟩ fun _ h => by cases h)
      (.cons (.acceptOk (t := .atom hiAtom) (by simp)) (.nil _))), by simp⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Hi
