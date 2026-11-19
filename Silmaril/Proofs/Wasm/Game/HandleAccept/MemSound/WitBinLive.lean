module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAstLive
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAstLive
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitBin

/-!
# Proofs: `binMod` accepts `pair(blob [0xFF], seq [7, 9])`

Against the counting host `countEnv hiOut` started at `q`, the traced session of `binMod` invokes
`run` and runs its body to `accept(q + 1 + 1)`: the module stores the byte `FF` at `[24, 25)` and
the pair `(24, 1)` at `[16, 24)`, and `node(0, 16, 0, 0)` reads the byte string `[0xFF]` (handle
`q`); it stores the `u32`s `7`, `9` at `[24, 32)` and the pair `(24, 2)` at `[16, 24)`, and
`node(1, 16, 0, 0)` reads the `list<u32>` `[7, 9]` (handle `q + 1`); the module stores both
handles at `[0, 8)`, and `node(2, 0, 0, 2)` reads no payload and the children `q, q + 1` (handle
`q + 1 + 1`). Its writer trace is `[enter, write (blob [0xFF]) [] q, write (seq [7, 9]) [] (q + 1),
write pair [q, q + 1] (q + 1 + 1), accept (q + 1 + 1)]`, which accepts
`pair(blob [0xFF], seq [7, 9])` in the store semantics when no handle is the policy's sentinel.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitBin

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
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitApp
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitBin
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitAst
open Silmaril.Wasm.Logic.Core (bytesAt)

theorem binSpec_some : (Silmaril.Wasm.Verify.specInstance? binMod).isSome = true := by
  decide +kernel

theorem binMem : memSizes binMod = [65536] := by decide +kernel

/-- **The writer trace of the session.** -/
theorem bin_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write ⟨BinTag.blob, (([0xFF] : List UInt8), ())⟩ [] q,
      .write ⟨BinTag.seq, (([7, 9] : List UInt32), ())⟩ [] (q + 1),
      .write ⟨BinTag.pair, ()⟩ [q, q + 1] (q + 1 + 1), .accept (q + 1 + 1)] ∈
      witTraces binSig binTagOf P (ReplyEnvs hiReply) 0 binMod {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists binSpec_some
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := bin_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page binMem hp
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
  let R := binRoles
  have t₀ : TSession P L binMod (some 0) R c q Is.addrs .inst false (c, q) [] := .start
  have hok : InvokeOk c.store 2 [] := ⟨f₂, ps, rs, (hfs _ rfl).2.2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 2 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  -- enter `run`
  have st₀ : Step P NH (invoke c.store 2 [])
      ⟨c.store, {}, [.frame 0 (Frame.forCall f₂.module [] [.i32, .i32])
        [.label 0 [] (expression binBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[2]?.map FuncInst.type).getD default)) (vs := [])
      (a := 2) (fi := f₂) (code := code) trivial (hfs _ rfl).2.2 he (by rw [hps]; rfl) hcode2
    rw [hrs, hloc, hbody] at h
    exact h
  have hFf : (Frame.forCall f₂.module [] [.i32, .i32]).module.funcs = [0, 1, 2] := by
    simp [Frame.forCall, hfuncs]
  have hFm : (Frame.forCall f₂.module [] [.i32, .i32]).module.mems = [0] := by
    simp [Frame.forCall, hmems2]
  have hFl : (Frame.forCall f₂.module [] [.i32, .i32]).locals = binD := by
    simp [Frame.forCall, hD]
  generalize Frame.forCall f₂.module [] [.i32, .i32] = F at st₀ hFf hFm hFl
  let F₁ := F.setLocal ⟨0⟩ (.i32 q)
  let F₂ := F₁.setLocal ⟨1⟩ (.i32 (q + 1))
  have hF₁m : F₁.module.mems = [0] := hFm
  have hF₁f : F₁.module.funcs = [0, 1, 2] := hFf
  have hF₂m : F₂.module.mems = [0] := hFm
  have hF₂f : F₂.module.funcs = [0, 1, 2] := hFf
  -- the byte `FF` at 24
  obtain ⟨b₀, hst₀⟩ := store_some (B := mi.bytes) (a := effAddr (24 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i8.width / 8) ((0xFF : BitVec 32).setWidth _) (by rw [hsize]; decide)
  have hz₀ : b₀.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₀).trans hsize
  let mi₀ : MemInst := { mi with bytes := b₀ }
  let s₀ := c.store.setMem 0 mi₀
  obtain ⟨hm₀, hl₀, hf₀⟩ := setMem_mems (mi := mi₀) hml
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression binBody)]]⟩
      ⟨s₀, {}, [.frame 0 F [.label 0 [] (expression (binBody.drop 3))]]⟩ :=
    step_body (step_mid [] _ (step_storePack hFm hmi hst₀))
  -- the pair at 16
  obtain ⟨b₁, hst₁⟩ := store_some (B := mi₀.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i64.width / 8) (strRef.setWidth _) (by rw [hz₀]; decide)
  have hz₁ : b₁.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₁).trans hz₀
  let mi₁ : MemInst := { mi₀ with bytes := b₁ }
  let s₁ := s₀.setMem 0 mi₁
  obtain ⟨hm₁, hl₁, hf₁⟩ := setMem_mems (s := s₀) (mi := mi₁) hl₀
  have st₁' : Step P NH ⟨s₀, {}, [.frame 0 F [.label 0 [] (expression (binBody.drop 3))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (binBody.drop 6))]]⟩ :=
    step_body (step_mid [] (expression (binBody.drop 6)) (step_store64 hFm hm₀ hst₁))
  -- node(0, 16, 0, 0)
  have hs₁f := hfs s₁ (hf₁.trans hf₀)
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (binBody.drop 6))]]⟩
      ⟨s₁, {}, (bodyCtx F (expression (binBody.drop 11))).fill
        (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 16, .i32 0, .i32 0] (expression (binBody.drop 11))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hs₁f.1))
  have hd₁ : decompose? s₁ ((bodyCtx F (expression (binBody.drop 11))).fill
      (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (binBody.drop 11)), 0, 0, [.i32 0, .i32 16, .i32 0, .i32 0]) :=
    decompose_fill _ trivial hs₁f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    (((st₀.steps.trans st₁.steps).trans st₁'.steps).trans st₂.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  -- local.set 0; the words `7`, `9` at 24
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (binBody.drop 11))).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 12))]]⟩ :=
    step_body (step_mid [] (expression (binBody.drop 12))
      (step_localSet (x := ⟨0⟩) (v := .i32 q) (by simp [hFl, binD, Idx.toNat])))
  obtain ⟨b₂, hst₂⟩ := store_some (B := mi₁.bytes) (a := effAddr (24 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i64.width / 8) (seqWords.setWidth _) (by rw [hz₁]; decide)
  have hz₂ : b₂.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₂).trans hz₁
  let mi₂ : MemInst := { mi₁ with bytes := b₂ }
  let s₂ := s₁.setMem 0 mi₂
  obtain ⟨hm₂, hl₂, hf₂⟩ := setMem_mems (s := s₁) (mi := mi₂) hl₁
  have st₄ : Step P NH
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 12))]]⟩
      ⟨s₂, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 15))]]⟩ :=
    step_body (step_mid [] (expression (binBody.drop 15)) (step_store64 hF₁m hm₁ hst₂))
  -- the pair at 16
  obtain ⟨b₃, hst₃⟩ := store_some (B := mi₂.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i64.width / 8) (seqRef.setWidth _) (by rw [hz₂]; decide)
  have hz₃ : b₃.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₃).trans hz₂
  let mi₃ : MemInst := { mi₂ with bytes := b₃ }
  let s₃ := s₂.setMem 0 mi₃
  obtain ⟨hm₃, hl₃, hf₃⟩ := setMem_mems (s := s₂) (mi := mi₃) hl₂
  have st₄' : Step P NH
      ⟨s₂, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 15))]]⟩
      ⟨s₃, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 18))]]⟩ :=
    step_body (step_mid [] (expression (binBody.drop 18)) (step_store64 hF₁m hm₂ hst₃))
  -- node(1, 16, 0, 0)
  have hs₃f := hfs s₃ (hf₃.trans (hf₂.trans (hf₁.trans hf₀)))
  have st₅ : Step P NH
      ⟨s₃, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 18))]]⟩
      ⟨s₃, {}, (bodyCtx F₁ (expression (binBody.drop 23))).fill
        (vals [.i32 1, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 1, .i32 16, .i32 0, .i32 0] (expression (binBody.drop 23))
      (step_call (x := ⟨0⟩) (by rw [hF₁f]; rfl) hs₃f.1))
  have hd₂ : decompose? s₃ ((bodyCtx F₁ (expression (binBody.drop 23))).fill
      (vals [.i32 1, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F₁ (expression (binBody.drop 23)), 0, 0, [.i32 1, .i32 16, .i32 0, .i32 0]) :=
    decompose_fill _ trivial hs₃f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₄ := TSession.call (TSession.of_core_steps t₃
    (((st₃.steps.trans st₄.steps).trans st₄'.steps).trans st₅.steps)) hd₂
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₃, .values [.i32 (q + 1)]⟩) (q' := q + 1 + 1)
    ⟨rfl, rfl⟩
  -- local.set 1; the handles at 0 and 4
  have st₆ : Step P NH ⟨s₃, {}, (bodyCtx F₁ (expression (binBody.drop 23))).fill
      (Result.values [.i32 (q + 1)]).toAdmin⟩
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 24))]]⟩ :=
    step_body (step_mid [] (expression (binBody.drop 24))
      (step_localSet (x := ⟨1⟩) (v := .i32 (q + 1))
        (by simp [F₁, Frame.setLocal, hFl, binD, Idx.toNat])))
  have hv₀ : F₂.local? ⟨0⟩ = some (some (.i32 q)) := by
    simp [F₂, F₁, Frame.local?, Frame.setLocal, hFl, binD, Idx.toNat]
  have hv₁ : F₂.local? ⟨1⟩ = some (some (.i32 (q + 1))) := by
    simp [F₂, F₁, Frame.local?, Frame.setLocal, hFl, binD, Idx.toNat]
  have st₇ : Step P NH
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 24))]]⟩
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 0] ++ [(Val.i32 q).toAdmin] ++
        expression (binBody.drop 26))]]⟩ :=
    step_body (step_mid [.i32 0] (expression (binBody.drop 26)) (step_localGet hv₀))
  obtain ⟨b₄, hst₄⟩ := store_some (B := mi₃.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i32.width / 8) (q.setWidth _) (by rw [hz₃]; decide)
  have hz₄ : b₄.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₄).trans hz₃
  let mi₄ : MemInst := { mi₃ with bytes := b₄ }
  let s₄ := s₃.setMem 0 mi₄
  obtain ⟨hm₄, hl₄, hf₄⟩ := setMem_mems (s := s₃) (mi := mi₄) hl₃
  have st₈ : Step P NH
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 0] ++ [(Val.i32 q).toAdmin] ++
        expression (binBody.drop 26))]]⟩
      ⟨s₄, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 27))]]⟩ :=
    step_body (step_mid [] (expression (binBody.drop 27)) (step_store32 hF₂m hm₃ hst₄))
  have st₉ : Step P NH
      ⟨s₄, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 27))]]⟩
      ⟨s₄, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 4] ++ [(Val.i32 (q + 1)).toAdmin] ++
        expression (binBody.drop 29))]]⟩ :=
    step_body (step_mid [.i32 4] (expression (binBody.drop 29)) (step_localGet hv₁))
  obtain ⟨b₅, hst₅⟩ := store_some (B := mi₄.bytes) (a := effAddr (4 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i32.width / 8) ((q + 1).setWidth _) (by rw [hz₄]; decide)
  have hz₅ : b₅.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₅).trans hz₄
  let mi₅ : MemInst := { mi₄ with bytes := b₅ }
  let s₅ := s₄.setMem 0 mi₅
  obtain ⟨-, hl₅, hf₅⟩ := setMem_mems (s := s₄) (mi := mi₅) hl₄
  have st₁₀ : Step P NH
      ⟨s₄, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 4] ++ [(Val.i32 (q + 1)).toAdmin] ++
        expression (binBody.drop 29))]]⟩
      ⟨s₅, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 30))]]⟩ :=
    step_body (step_mid [] (expression (binBody.drop 30)) (step_store32 hF₂m hm₄ hst₅))
  -- node(2, 0, 0, 2)
  have hs₅f := hfs s₅ (hf₅.trans (hf₄.trans (hf₃.trans (hf₂.trans (hf₁.trans hf₀)))))
  have st₁₁ : Step P NH
      ⟨s₅, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (binBody.drop 30))]]⟩
      ⟨s₅, {}, (bodyCtx F₂ (expression (binBody.drop 35))).fill
        (vals [.i32 2, .i32 0, .i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 2, .i32 0, .i32 0, .i32 2] (expression (binBody.drop 35))
      (step_call (x := ⟨0⟩) (by rw [hF₂f]; rfl) hs₅f.1))
  have hd₃ : decompose? s₅ ((bodyCtx F₂ (expression (binBody.drop 35))).fill
      (vals [.i32 2, .i32 0, .i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F₂ (expression (binBody.drop 35)), 0, 0, [.i32 2, .i32 0, .i32 0, .i32 2]) :=
    decompose_fill _ trivial hs₅f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₆ := TSession.call (TSession.of_core_steps t₅
    ((((((st₆.steps.trans st₇.steps).trans st₈.steps).trans st₉.steps).trans st₁₀.steps)).trans
      st₁₁.steps)) hd₃
  have t₇ := TSession.answer t₆ hd₃ (a := ⟨s₅, .values [.i32 (q + 1 + 1)]⟩)
    (q' := q + 1 + 1 + 1) ⟨rfl, rfl⟩
  -- accept
  have st₁₂ : Step P NH ⟨s₅, {}, (bodyCtx F₂ (expression (binBody.drop 35))).fill
      (Result.values [.i32 (q + 1 + 1)]).toAdmin⟩
      ⟨s₅, {}, (bodyCtx F₂ []).fill
        (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 (q + 1 + 1)] [] (step_call (x := ⟨1⟩) (by rw [hF₂f]; rfl) hs₅f.2.1))
  have hd₄ : decompose? s₅ ((bodyCtx F₂ []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F₂ [], 1, 1, [.i32 (q + 1 + 1)]) :=
    decompose_fill _ trivial hs₅f.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₈ := TSession.call (TSession.of_core_steps t₇ st₁₂.steps) hd₄
  -- the decoded events
  have hco₁ : calloutAt? binMod (some 0) ⟨s₁, {}, (bodyCtx F (expression (binBody.drop 11))).fill
      (vals [.i32 0, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn impNode (some 0) s₁ [.i32 0, .i32 16, .i32 0, .i32 0]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? binMod (some 0)
      ⟨s₃, {}, (bodyCtx F₁ (expression (binBody.drop 23))).fill
        (vals [.i32 1, .i32 16, .i32 0, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn impNode (some 0) s₃ [.i32 1, .i32 16, .i32 0, .i32 0]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? binMod (some 0)
      ⟨s₅, {}, (bodyCtx F₂ (expression (binBody.drop 35))).fill
        (vals [.i32 2, .i32 0, .i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn impNode (some 0) s₅ [.i32 2, .i32 0, .i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hco₄ : calloutAt? binMod (some 0) ⟨s₅, {}, (bodyCtx F₂ []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn WitAst.impAcc (some 0) s₅ [.i32 (q + 1 + 1)]) := by
    unfold calloutAt?; rw [hd₄]; rfl
  have hn₁' : Callout.witNode binSig binTagOf
      (calloutIn impNode (some 0) s₁ [.i32 0, .i32 16, .i32 0, .i32 0]) =
      some (⟨BinTag.blob, (([0xFF] : List UInt8), ())⟩, []) :=
    blob_node hst₀ hst₁ (memOf_setMem hl₀) rfl
  have hn₂' : Callout.witNode binSig binTagOf
      (calloutIn impNode (some 0) s₃ [.i32 1, .i32 16, .i32 0, .i32 0]) =
      some (⟨BinTag.seq, (([7, 9] : List UInt32), ())⟩, []) :=
    seq_node hst₂ hst₃ (memOf_setMem hl₂) rfl
  have h₀ : bytesAt b₅ ⟨0, 4⟩ = (Memory.encodeLE 4 q.toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hst₅ (.inr (by decide))]
    exact bytes_of_store32 hst₄
  have h₄ : bytesAt b₅ ⟨4, 4⟩ = (Memory.encodeLE 4 (q + 1).toNat).data.toList :=
    bytes_of_store32 hst₅
  obtain ⟨cs, hcs, hle⟩ := children_pair
    (o := calloutIn impNode (some 0) s₅ [.i32 2, .i32 0, .i32 0, .i32 2]) (memOf_setMem hl₄)
    (by rw [hz₅]; decide) h₀ h₄
  have hn₃' : Callout.witNode binSig binTagOf
      (calloutIn impNode (some 0) s₅ [.i32 2, .i32 0, .i32 0, .i32 2]) =
      some (⟨BinTag.pair, ()⟩, [q, q + 1]) :=
    witNode_eq rfl rfl (segment_nil (memOf_setMem hl₄) 0 (Nat.zero_le _)) rfl hcs hle rfl
  have hna : ∀ (s : Store Nat) (args : List Val),
      witAccept binSig {} (calloutIn impNode (some 0) s args) = none := fun _ _ =>
    witAccept_eq_none (by show ("wit", "node") ≠ ("wit", "accept"); decide)
  have hac : witAccept binSig {} (calloutIn WitAst.impAcc (some 0) s₅ [.i32 (q + 1 + 1)]) =
      some (.accept (q + 1 + 1)) := by
    simp [witAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  rw [hco₁, hco₂, hco₃, hco₄] at t₈
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply hiOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₈⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, witRoles]
  rw [hna, witWrite_eq rfl hn₁' rfl, hna, witWrite_eq rfl hn₂' rfl, hna, witWrite_eq rfl hn₃' rfl,
    hac]
  rfl

/-- **`binMod` accepts `pair(blob [0xFF], seq [7, 9])`**, for every profile and policy. -/
theorem binMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    binTree ∈ witWriterLang binSig binTagOf P (ReplyEnvs hiReply) 0 binMod {} pol := by
  let q := base pol
  have hn₀ : pol.sentinel ≠ some q := by simpa using base_ne pol (k := 0) (by decide)
  have hn₁ : pol.sentinel ≠ some (q + 1) := base_ne pol (k := 1) (by decide)
  have hn₂ : pol.sentinel ≠ some (q + 1 + 1) := by
    have := base_ne pol (k := 2) (by decide)
    rwa [show q + 2 = q + 1 + 1 by bv_omega] at this
  have d₁ : q + 1 ≠ q := by bv_omega
  have d₂ : q + 1 + 1 ≠ q := by bv_omega
  have d₃ : q + 1 + 1 ≠ q + 1 := by bv_omega
  let σ₁ : Env (BitVec 32) (AST binSig.toAstSig) :=
    Function.update Env.empty q (some (blobTree [0xFF]))
  let σ₂ := Function.update σ₁ (q + 1) (some (seqTree [7, 9]))
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
  have hq : σ₂ q = some (blobTree [0xFF]) := by
    show Function.update σ₁ (q + 1) _ q = _
    rw [Function.update_of_ne d₁.symm]
    exact Function.update_self ..
  have hq₁ : σ₂ (q + 1) = some (seqTree [7, 9]) := Function.update_self ..
  simp only [witWriterLang, writerLang, Host.lang]
  refine Set.mem_biUnion (bin_traces P q) ⟨_, _, .cons .enter
    (.cons (.writeOk (t := blobTree [0xFF]) (built_blob _ _) ⟨hn₀, .inl rfl⟩
      fun _ h => by cases h)
    (.cons (.writeOk (t := seqTree [7, 9]) (built_seq _ _) ⟨hn₁, .inl e₁⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := binTree) (built_pair hq hq₁) ⟨hn₂, .inl e₂⟩ fun _ h => by cases h)
    (.cons (.acceptOk (t := binTree) (by simp)) (.nil _))))), by simp⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitBin
