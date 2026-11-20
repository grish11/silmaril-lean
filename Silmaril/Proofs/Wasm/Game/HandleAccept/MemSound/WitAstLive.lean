module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst

/-!
# Proofs: `calcMod` accepts `add(num 1, num 2)`

Against the counting host `countEnv hiOut` started at `q` (it answers `node` with the next
handle, `accept` with nothing, in the caller's store), the traced session of `calcMod` invokes
`run` and runs its body to `accept(q + 1 + 1)`: `node(0, 16, 0, 0)` reads the `s64` `1` stored at
`[16, 24)` (handle `q`), `node(0, 16, 0, 0)` reads `2` (handle `q + 1`), the module stores both
handles at `[0, 8)`, and `node(1, 0, 0, 2)` reads no payload and the children `q, q + 1` (handle
`q + 1 + 1`). Its writer trace is
`[enter, write (num 1) [] q, write (num 2) [] (q + 1), write add [q, q + 1] (q + 1 + 1),
accept (q + 1 + 1)]`, which accepts `add(num 1, num 2)` in the store semantics when no handle is
the policy's sentinel.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitAst

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WordAtom
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
open Silmaril.Wasm.Logic.Core (bytesAt)

theorem calcSpec_some : (Silmaril.Wasm.Verify.specInstance? calcMod).isSome = true := by
  decide +kernel

theorem calcMem : memSizes calcMod = [65536] := by decide +kernel

theorem hiOut_shape (k : Nat) (q : BitVec 32) : hiShape k (hiOut k q) := by
  rcases k with _ | _ | k <;> simp [hiShape, hiOut]

/-- **The writer trace of the session.** -/
theorem calc_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write ⟨CalcTag.num, ((1 : Int64), ())⟩ [] q,
      .write ⟨CalcTag.num, ((2 : Int64), ())⟩ [] (q + 1),
      .write ⟨CalcTag.add, ()⟩ [q, q + 1] (q + 1 + 1), .accept (q + 1 + 1)] ∈
      witTraces calcSig calcTagOf P (ReplyEnvs hiReply) 0 calcMod {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists calcSpec_some
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := calc_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page calcMem hp
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
  let R := calcRoles
  have t₀ : TSession P L calcMod (some 0) R c q Is.addrs .inst false (c, q) [] := .start
  have hok : InvokeOk c.store 2 [] := ⟨f₂, ps, rs, (hfs _ rfl).2.2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 2 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  -- enter `run`
  have st₀ : Step P NH (invoke c.store 2 [])
      ⟨c.store, {}, [.frame 0 (Frame.forCall f₂.module [] [.i32, .i32])
        [.label 0 [] (expression calcBody)]]⟩ := by
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
  let F₂ := F₁.setLocal ⟨1⟩ (.i32 (q + 1))
  have hF₁m : F₁.module.mems = [0] := hFm
  have hF₁f : F₁.module.funcs = [0, 1, 2] := hFf
  have hF₂m : F₂.module.mems = [0] := hFm
  have hF₂f : F₂.module.funcs = [0, 1, 2] := hFf
  -- the payload `1` at 16
  obtain ⟨b₁, hst₁⟩ := store_some (B := mi.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i64.width / 8) ((1 : BitVec 64).setWidth _) (by rw [hsize]; decide)
  have hz₁ : b₁.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₁).trans hsize
  let mi₁ : MemInst := { mi with bytes := b₁ }
  let s₁ := c.store.setMem 0 mi₁
  obtain ⟨hm₁, hl₁, hf₁⟩ := setMem_mems (mi := mi₁) hml
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression calcBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (calcBody.drop 3))]]⟩ :=
    step_body (step_mid [] _ (step_store64 hFm hmi hst₁))
  -- node(0, 16, 0, 0)
  have hs₁f := hfs s₁ hf₁
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (calcBody.drop 3))]]⟩
      ⟨s₁, {}, (bodyCtx F (expression (calcBody.drop 8))).fill
        (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 16, .i32 0, .i32 0] (expression (calcBody.drop 8))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hs₁f.1))
  have hd₁ : decompose? s₁ ((bodyCtx F (expression (calcBody.drop 8))).fill
      (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (calcBody.drop 8)), 0, 0, [.i32 0, .i32 16, .i32 0, .i32 0]) :=
    decompose_fill _ trivial hs₁f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  -- local.set 0; the payload `2` at 16
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (calcBody.drop 8))).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (calcBody.drop 9))]]⟩ :=
    step_body (step_mid [] (expression (calcBody.drop 9))
      (step_localSet (x := ⟨0⟩) (v := .i32 q) (by simp [hFl, calcD, Idx.toNat])))
  obtain ⟨b₂, hst₂⟩ := store_some (B := mi₁.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i64.width / 8) ((2 : BitVec 64).setWidth _) (by rw [hz₁]; decide)
  have hz₂ : b₂.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₂).trans hz₁
  let mi₂ : MemInst := { mi₁ with bytes := b₂ }
  let s₂ := s₁.setMem 0 mi₂
  obtain ⟨hm₂, hl₂, hf₂⟩ := setMem_mems (s := s₁) (mi := mi₂) hl₁
  have st₄ : Step P NH
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (calcBody.drop 9))]]⟩
      ⟨s₂, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (calcBody.drop 12))]]⟩ :=
    step_body (step_mid [] (expression (calcBody.drop 12)) (step_store64 hF₁m hm₁ hst₂))
  -- node(0, 16, 0, 0)
  have hs₂f := hfs s₂ (hf₂.trans hf₁)
  have st₅ : Step P NH
      ⟨s₂, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (calcBody.drop 12))]]⟩
      ⟨s₂, {}, (bodyCtx F₁ (expression (calcBody.drop 17))).fill
        (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 16, .i32 0, .i32 0] (expression (calcBody.drop 17))
      (step_call (x := ⟨0⟩) (by rw [hF₁f]; rfl) hs₂f.1))
  have hd₂ : decompose? s₂ ((bodyCtx F₁ (expression (calcBody.drop 17))).fill
      (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F₁ (expression (calcBody.drop 17)), 0, 0, [.i32 0, .i32 16, .i32 0, .i32 0]) :=
    decompose_fill _ trivial hs₂f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₄ := TSession.call (TSession.of_core_steps t₃
    ((st₃.steps.trans st₄.steps).trans st₅.steps)) hd₂
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₂, .values [.i32 (q + 1)]⟩) (q' := q + 1 + 1)
    ⟨rfl, rfl⟩
  -- local.set 1; the handles at 0 and 4
  have st₆ : Step P NH ⟨s₂, {}, (bodyCtx F₁ (expression (calcBody.drop 17))).fill
      (Result.values [.i32 (q + 1)]).toAdmin⟩
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (calcBody.drop 18))]]⟩ :=
    step_body (step_mid [] (expression (calcBody.drop 18))
      (step_localSet (x := ⟨1⟩) (v := .i32 (q + 1))
        (by simp [F₁, Frame.setLocal, hFl, calcD, Idx.toNat])))
  have hv₀ : F₂.local? ⟨0⟩ = some (some (.i32 q)) := by
    simp [F₂, F₁, Frame.local?, Frame.setLocal, hFl, calcD, Idx.toNat]
  have hv₁ : F₂.local? ⟨1⟩ = some (some (.i32 (q + 1))) := by
    simp [F₂, F₁, Frame.local?, Frame.setLocal, hFl, calcD, Idx.toNat]
  have st₇ : Step P NH
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (calcBody.drop 18))]]⟩
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 0] ++ [(Val.i32 q).toAdmin] ++
        expression (calcBody.drop 20))]]⟩ :=
    step_body (step_mid [.i32 0] (expression (calcBody.drop 20)) (step_localGet hv₀))
  obtain ⟨b₃, hst₃⟩ := store_some (B := mi₂.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i32.width / 8) (q.setWidth _) (by rw [hz₂]; decide)
  have hz₃ : b₃.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₃).trans hz₂
  let mi₃ : MemInst := { mi₂ with bytes := b₃ }
  let s₃ := s₂.setMem 0 mi₃
  obtain ⟨hm₃, hl₃, hf₃⟩ := setMem_mems (s := s₂) (mi := mi₃) hl₂
  have st₈ : Step P NH
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 0] ++ [(Val.i32 q).toAdmin] ++
        expression (calcBody.drop 20))]]⟩
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (calcBody.drop 21))]]⟩ :=
    step_body (step_mid [] (expression (calcBody.drop 21)) (step_store32 hF₂m hm₂ hst₃))
  have st₉ : Step P NH
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (calcBody.drop 21))]]⟩
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 4] ++ [(Val.i32 (q + 1)).toAdmin] ++
        expression (calcBody.drop 23))]]⟩ :=
    step_body (step_mid [.i32 4] (expression (calcBody.drop 23)) (step_localGet hv₁))
  obtain ⟨b₄, hst₄⟩ := store_some (B := mi₃.bytes) (a := effAddr (4 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i32.width / 8) ((q + 1).setWidth _) (by rw [hz₃]; decide)
  have hz₄ : b₄.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₄).trans hz₃
  let mi₄ : MemInst := { mi₃ with bytes := b₄ }
  let s₄ := s₃.setMem 0 mi₄
  obtain ⟨-, hl₄, hf₄⟩ := setMem_mems (s := s₃) (mi := mi₄) hl₃
  have st₁₀ : Step P NH
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 4] ++ [(Val.i32 (q + 1)).toAdmin] ++
        expression (calcBody.drop 23))]]⟩
      ⟨s₄, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (calcBody.drop 24))]]⟩ :=
    step_body (step_mid [] (expression (calcBody.drop 24)) (step_store32 hF₂m hm₃ hst₄))
  -- node(1, 0, 0, 2)
  have hs₄f := hfs s₄ (hf₄.trans (hf₃.trans (hf₂.trans hf₁)))
  have st₁₁ : Step P NH
      ⟨s₄, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (calcBody.drop 24))]]⟩
      ⟨s₄, {}, (bodyCtx F₂ (expression (calcBody.drop 29))).fill
        (vals [.i32 1, .i32 0, .i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 1, .i32 0, .i32 0, .i32 2] (expression (calcBody.drop 29))
      (step_call (x := ⟨0⟩) (by rw [hF₂f]; rfl) hs₄f.1))
  have hd₃ : decompose? s₄ ((bodyCtx F₂ (expression (calcBody.drop 29))).fill
      (vals [.i32 1, .i32 0, .i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F₂ (expression (calcBody.drop 29)), 0, 0, [.i32 1, .i32 0, .i32 0, .i32 2]) :=
    decompose_fill _ trivial hs₄f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₆ := TSession.call (TSession.of_core_steps t₅
    ((((((st₆.steps.trans st₇.steps).trans st₈.steps).trans st₉.steps).trans st₁₀.steps)).trans
      st₁₁.steps)) hd₃
  have t₇ := TSession.answer t₆ hd₃ (a := ⟨s₄, .values [.i32 (q + 1 + 1)]⟩)
    (q' := q + 1 + 1 + 1) ⟨rfl, rfl⟩
  -- accept
  have st₁₂ : Step P NH ⟨s₄, {}, (bodyCtx F₂ (expression (calcBody.drop 29))).fill
      (Result.values [.i32 (q + 1 + 1)]).toAdmin⟩
      ⟨s₄, {}, (bodyCtx F₂ []).fill
        (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 (q + 1 + 1)] [] (step_call (x := ⟨1⟩) (by rw [hF₂f]; rfl) hs₄f.2.1))
  have hd₄ : decompose? s₄ ((bodyCtx F₂ []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F₂ [], 1, 1, [.i32 (q + 1 + 1)]) :=
    decompose_fill _ trivial hs₄f.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₈ := TSession.call (TSession.of_core_steps t₇ st₁₂.steps) hd₄
  -- the decoded events
  have hco₁ : calloutAt? calcMod (some 0) ⟨s₁, {}, (bodyCtx F (expression (calcBody.drop 8))).fill
      (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn impNode (some 0) s₁ [.i32 0, .i32 16, .i32 0, .i32 0]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? calcMod (some 0)
      ⟨s₂, {}, (bodyCtx F₁ (expression (calcBody.drop 17))).fill
        (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn impNode (some 0) s₂ [.i32 0, .i32 16, .i32 0, .i32 0]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? calcMod (some 0)
      ⟨s₄, {}, (bodyCtx F₂ (expression (calcBody.drop 29))).fill
        (vals [.i32 1, .i32 0, .i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn impNode (some 0) s₄ [.i32 1, .i32 0, .i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hco₄ : calloutAt? calcMod (some 0) ⟨s₄, {}, (bodyCtx F₂ []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn WitAst.impAcc (some 0) s₄ [.i32 (q + 1 + 1)]) := by
    unfold calloutAt?; rw [hd₄]; rfl
  have hn₁' : Callout.witNode calcSig calcTagOf
      (calloutIn impNode (some 0) s₁ [.i32 0, .i32 16, .i32 0, .i32 0]) =
      some (⟨CalcTag.num, ((1 : Int64), ())⟩, []) :=
    witNode_eq rfl rfl (segment_of_store hst₁ _ (memOf_setMem hml)) (readVals_one _)
      (segment_nil (memOf_setMem hml) 0 (Nat.zero_le _)) rfl rfl
  have hn₂' : Callout.witNode calcSig calcTagOf
      (calloutIn impNode (some 0) s₂ [.i32 0, .i32 16, .i32 0, .i32 0]) =
      some (⟨CalcTag.num, ((2 : Int64), ())⟩, []) :=
    witNode_eq rfl rfl (segment_of_store hst₂ _ (memOf_setMem hl₁)) (readVals_two _)
      (segment_nil (memOf_setMem hl₁) 0 (Nat.zero_le _)) rfl rfl
  have h₀ : bytesAt b₄ ⟨0, 4⟩ = (Memory.encodeLE 4 q.toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hst₄ (.inr (by decide))]
    exact bytes_of_store32 hst₃
  have h₄ : bytesAt b₄ ⟨4, 4⟩ = (Memory.encodeLE 4 (q + 1).toNat).data.toList :=
    bytes_of_store32 hst₄
  obtain ⟨cs, hcs, hle⟩ := children_pair
    (o := calloutIn impNode (some 0) s₄ [.i32 1, .i32 0, .i32 0, .i32 2]) (memOf_setMem hl₃)
    (by rw [hz₄]; decide) h₀ h₄
  have hn₃' : Callout.witNode calcSig calcTagOf
      (calloutIn impNode (some 0) s₄ [.i32 1, .i32 0, .i32 0, .i32 2]) =
      some (⟨CalcTag.add, ()⟩, [q, q + 1]) :=
    witNode_eq rfl rfl (segment_nil (memOf_setMem hl₃) 0 (Nat.zero_le _)) rfl hcs hle rfl
  have hna : ∀ (s : Store Nat) (args : List Val),
      witAccept calcSig {} (calloutIn impNode (some 0) s args) = none := fun _ _ =>
    witAccept_eq_none (by show ("wit", "node") ≠ ("wit", "accept"); decide)
  have hac : witAccept calcSig {} (calloutIn WitAst.impAcc (some 0) s₄ [.i32 (q + 1 + 1)]) =
      some (.accept (q + 1 + 1)) := by
    simp [witAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  rw [hco₁, hco₂, hco₃, hco₄] at t₈
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply hiOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₈⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, witRoles]
  rw [hna, witWrite_eq rfl hn₁' rfl, hna, witWrite_eq rfl hn₂' rfl, hna, witWrite_eq rfl hn₃' rfl,
    hac]
  rfl

/-- **`calcMod` accepts `add(num 1, num 2)`**, for every profile and policy. -/
theorem calcMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    addTree ∈ witWriterLang calcSig calcTagOf P (ReplyEnvs hiReply) 0 calcMod {} pol := by
  let q := base pol
  have hn₀ : pol.sentinel ≠ some q := by simpa using base_ne pol (k := 0) (by decide)
  have hn₁ : pol.sentinel ≠ some (q + 1) := base_ne pol (k := 1) (by decide)
  have hn₂ : pol.sentinel ≠ some (q + 1 + 1) := by
    have := base_ne pol (k := 2) (by decide)
    rwa [show q + 2 = q + 1 + 1 by bv_omega] at this
  have d₁ : q + 1 ≠ q := by bv_omega
  have d₂ : q + 1 + 1 ≠ q := by bv_omega
  have d₃ : q + 1 + 1 ≠ q + 1 := by bv_omega
  let σ₁ : Env (BitVec 32) (AST calcSig.toAstSig) :=
    Function.update Env.empty q (some (numTree 1))
  let σ₂ := Function.update σ₁ (q + 1) (some (numTree 2))
  have e₁ : σ₁ (q + 1) = none := by
    show Function.update Env.empty q _ (q + 1) = none
    rw [Function.update_of_ne d₁]
    rfl
  have e₂ : σ₂ (q + 1 + 1) = none := by
    show Function.update σ₁ (q + 1) _ (q + 1 + 1) = none
    rw [Function.update_of_ne d₃]
    show Function.update Env.empty q _ (q + 1 + 1) = none
    rw [Function.update_of_ne d₂]
    rfl
  have hq : σ₂ q = some (numTree 1) := by
    show Function.update σ₁ (q + 1) _ q = _
    rw [Function.update_of_ne d₁.symm]
    exact Function.update_self ..
  have hq₁ : σ₂ (q + 1) = some (numTree 2) := Function.update_self ..
  simp only [witWriterLang, writerLang, Host.lang]
  refine Set.mem_biUnion (calc_traces P q) ⟨_, _, .cons .enter
    (.cons (.writeOk (t := numTree 1) (built_num _ 1) ⟨hn₀, .inl rfl⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := numTree 2) (built_num _ 2) ⟨hn₁, .inl e₁⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := addTree) (built_add hq hq₁) ⟨hn₂, .inl e₂⟩ fun _ h => by cases h)
    (.cons (.acceptOk (t := addTree) (by simp)) (.nil _))))), by simp⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitAst
