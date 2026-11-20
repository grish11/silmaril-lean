module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pair

/-!
# Proofs: `pairMod` accepts the list `(a b)`

Against the counting host `countEnv pairOut` started at `q` (it answers `symbol` and `sexp` with
the next handle, `accept` with nothing, in the caller's store), the traced session of `pairMod`
invokes `run` and runs its body to `accept(q + 2)`: `symbol(16, 1)` observes `61` (handle `q`),
`symbol(16, 1)` observes `62` (handle `q + 1`), `sexp(0, 2)` observes the little-endian handles
`q, q + 1` (handle `q + 2`). Its writer trace is
`[enter, write a [] q, write b [] (q+1), write list [q, q+1] (q+2), accept (q+2)]`, which accepts
`(a b)` in the store semantics when none of the three handles is the policy's sentinel.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Pair

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pair
  Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pair
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
open Silmaril.Wasm.Logic.Core (bytesAt)

theorem pairSpec_some : (Silmaril.Wasm.Verify.specInstance? pairMod).isSome = true := by
  decide +kernel

theorem pairMem : memSizes pairMod = [65536] := by decide +kernel

theorem pairOut_shape (k : Nat) (q : BitVec 32) : pairShape k (pairOut k q) := by
  rcases k with _ | _ | _ | k <;> simp [pairShape, pairOut]

/-- The callout of `name(args)` in the store `s` (memory `0`). -/
abbrev co (name : String) (k : TypeIdx) (s : Store Nat) (args : List Val) : Callout :=
  calloutIn ⟨"sexp", name, .func k⟩ (some 0) s args

/-- **The writer trace of the session.** -/
theorem pair_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write (.atom symA) [] q, .write (.atom symB) [] (q + 1),
      .write .list [q, q + 1] (q + 1 + 1), .accept (q + 1 + 1)] ∈
      memTraces P (ReplyEnvs pairReply) 0 pairMod {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists pairSpec_some
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, hf, h0, h1, h2, h3⟩ := pair_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page pairMem hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  obtain ⟨code, ps, rs, hcode3, hloc, hbody, he, hps, hrs, hfuncs, hmems3, hD⟩ := fnOk_spec h3
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hfs : ∀ s : Store Nat, s.funcs = c.store.funcs → s.funcs[0]? = some f₀ ∧
      s.funcs[1]? = some f₁ ∧ s.funcs[2]? = some f₂ ∧ s.funcs[3]? = some f₃ := by
    intro s h; rw [h, hf]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  let L := countEnv pairOut
  let R := memRoles {}
  have t₀ : TSession P L pairMod (some 0) R c q Is.addrs .inst false (c, q) [] := .start
  have hok : InvokeOk c.store 3 [] := ⟨f₃, ps, rs, (hfs _ rfl).2.2.2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 3 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  -- enter `run`
  have st₀ : Step P NH (invoke c.store 3 [])
      ⟨c.store, {}, [.frame 0 (Frame.forCall f₃.module [] [.i32, .i32])
        [.label 0 [] (expression pairBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[3]?.map FuncInst.type).getD default)) (vs := [])
      (a := 3) (fi := f₃) (code := code) trivial (hfs _ rfl).2.2.2 he (by rw [hps]; rfl) hcode3
    rw [hrs, hloc, hbody] at h
    exact h
  have hFf : (Frame.forCall f₃.module [] [.i32, .i32]).module.funcs = [0, 1, 2, 3] := by
    simp [Frame.forCall, hfuncs]
  have hFm : (Frame.forCall f₃.module [] [.i32, .i32]).module.mems = [0] := by
    simp [Frame.forCall, hmems3]
  have hFl : (Frame.forCall f₃.module [] [.i32, .i32]).locals = pairD := by
    simp [Frame.forCall, hD]
  generalize Frame.forCall f₃.module [] [.i32, .i32] = F at st₀ hFf hFm hFl
  let F₁ := F.setLocal ⟨0⟩ (.i32 q)
  let F₂ := F₁.setLocal ⟨1⟩ (.i32 (q + 1))
  -- "a" at 16
  obtain ⟨b₁, hst₁⟩ := store_some (B := mi.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i8.width / 8) ((0x61 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  have hz₁ : b₁.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₁).trans hsize
  let mi₁ : MemInst := { mi with bytes := b₁ }
  let s₁ := c.store.setMem 0 mi₁
  obtain ⟨hm₁, hl₁, hf₁⟩ := setMem_mems (mi := mi₁) hml
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression pairBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (pairBody.drop 3))]]⟩ :=
    step_body (step_mid [] _ (step_storePack hFm hmi hst₁))
  -- symbol(16, 1)
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (pairBody.drop 3))]]⟩
      ⟨s₁, {}, (bodyCtx F (expression (pairBody.drop 6))).fill
        (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 16, .i32 1] (expression (pairBody.drop 6))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) (hfs _ hf₁).1))
  have hd₁ : decompose? s₁ ((bodyCtx F (expression (pairBody.drop 6))).fill
      (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (pairBody.drop 6)), 0, 0, [.i32 16, .i32 1]) :=
    decompose_fill _ trivial (hfs _ hf₁).1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    (((st₀.steps.trans st₁.steps).trans st₂.steps))) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  -- local.set 0; "b" at 16
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (pairBody.drop 6))).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 7))]]⟩ :=
    step_body (step_mid [] (expression (pairBody.drop 7))
      (step_localSet (x := ⟨0⟩) (v := .i32 q) (by simp [hFl, pairD, Idx.toNat])))
  obtain ⟨b₂, hst₂⟩ := store_some (B := mi₁.bytes) (a := effAddr (16 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i8.width / 8) ((0x62 : BitVec 32).setWidth _) (by rw [hz₁]; decide)
  have hz₂ : b₂.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₂).trans hz₁
  let mi₂ : MemInst := { mi₁ with bytes := b₂ }
  let s₂ := s₁.setMem 0 mi₂
  obtain ⟨hm₂, hl₂, hf₂⟩ := setMem_mems (s := s₁) (mi := mi₂) hl₁
  have hF₁m : F₁.module.mems = [0] := hFm
  have hF₁f : F₁.module.funcs = [0, 1, 2, 3] := hFf
  have st₄ : Step P NH
      ⟨s₁, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 7))]]⟩
      ⟨s₂, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 10))]]⟩ :=
    step_body (step_mid [] (expression (pairBody.drop 10)) (step_storePack hF₁m hm₁ hst₂))
  -- symbol(16, 1)
  have hs₂f := hfs s₂ (hf₂.trans hf₁)
  have st₅ : Step P NH
      ⟨s₂, {}, [.frame 0 F₁ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 10))]]⟩
      ⟨s₂, {}, (bodyCtx F₁ (expression (pairBody.drop 13))).fill
        (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 16, .i32 1] (expression (pairBody.drop 13))
      (step_call (x := ⟨0⟩) (by rw [hF₁f]; rfl) hs₂f.1))
  have hd₂ : decompose? s₂ ((bodyCtx F₁ (expression (pairBody.drop 13))).fill
      (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F₁ (expression (pairBody.drop 13)), 0, 0, [.i32 16, .i32 1]) :=
    decompose_fill _ trivial hs₂f.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₄ := TSession.call (TSession.of_core_steps t₃
    ((st₃.steps.trans st₄.steps).trans st₅.steps)) hd₂
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₂, .values [.i32 (q + 1)]⟩) (q' := q + 1 + 1)
    ⟨rfl, rfl⟩
  -- local.set 1; the handles at 0 and 4
  have st₆ : Step P NH ⟨s₂, {}, (bodyCtx F₁ (expression (pairBody.drop 13))).fill
      (Result.values [.i32 (q + 1)]).toAdmin⟩
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 14))]]⟩ :=
    step_body (step_mid [] (expression (pairBody.drop 14))
      (step_localSet (x := ⟨1⟩) (v := .i32 (q + 1))
        (by simp [F₁, Frame.setLocal, hFl, pairD, Idx.toNat])))
  have hv₀ : F₂.local? ⟨0⟩ = some (some (.i32 q)) := by
    simp [F₂, F₁, Frame.local?, Frame.setLocal, hFl, pairD, Idx.toNat]
  have hv₁ : F₂.local? ⟨1⟩ = some (some (.i32 (q + 1))) := by
    simp [F₂, F₁, Frame.local?, Frame.setLocal, hFl, pairD, Idx.toNat]
  have hF₂m : F₂.module.mems = [0] := hFm
  have hF₂f : F₂.module.funcs = [0, 1, 2, 3] := hFf
  have st₇ : Step P NH
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 14))]]⟩
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 0] ++ [(Val.i32 q).toAdmin] ++
        expression (pairBody.drop 16))]]⟩ :=
    step_body (step_mid [.i32 0] (expression (pairBody.drop 16)) (step_localGet hv₀))
  obtain ⟨b₃, hst₃⟩ := store_some (B := mi₂.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i32.width / 8) (q.setWidth _) (by rw [hz₂]; decide)
  have hz₃ : b₃.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₃).trans hz₂
  let mi₃ : MemInst := { mi₂ with bytes := b₃ }
  let s₃ := s₂.setMem 0 mi₃
  obtain ⟨hm₃, hl₃, hf₃⟩ := setMem_mems (s := s₂) (mi := mi₃) hl₂
  have st₈ : Step P NH
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 0] ++ [(Val.i32 q).toAdmin] ++
        expression (pairBody.drop 16))]]⟩
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 17))]]⟩ :=
    step_body (step_mid [] (expression (pairBody.drop 17)) (step_store32 hF₂m hm₂ hst₃))
  have st₉ : Step P NH
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 17))]]⟩
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 4] ++ [(Val.i32 (q + 1)).toAdmin] ++
        expression (pairBody.drop 19))]]⟩ :=
    step_body (step_mid [.i32 4] (expression (pairBody.drop 19)) (step_localGet hv₁))
  obtain ⟨b₄, hst₄⟩ := store_some (B := mi₃.bytes) (a := effAddr (4 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i32.width / 8) ((q + 1).setWidth _) (by rw [hz₃]; decide)
  have hz₄ : b₄.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst₄).trans hz₃
  let mi₄ : MemInst := { mi₃ with bytes := b₄ }
  let s₄ := s₃.setMem 0 mi₄
  obtain ⟨-, hl₄, hf₄⟩ := setMem_mems (s := s₃) (mi := mi₄) hl₃
  have st₁₀ : Step P NH
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [.i32 4] ++ [(Val.i32 (q + 1)).toAdmin] ++
        expression (pairBody.drop 19))]]⟩
      ⟨s₄, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 20))]]⟩ :=
    step_body (step_mid [] (expression (pairBody.drop 20)) (step_store32 hF₂m hm₃ hst₄))
  -- sexp(0, 2)
  have hs₄f := hfs s₄ (hf₄.trans (hf₃.trans (hf₂.trans hf₁)))
  have st₁₁ : Step P NH
      ⟨s₄, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++ expression (pairBody.drop 20))]]⟩
      ⟨s₄, {}, (bodyCtx F₂ (expression (pairBody.drop 23))).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 2] (expression (pairBody.drop 23))
      (step_call (x := ⟨1⟩) (by rw [hF₂f]; rfl) hs₄f.2.1))
  have hd₃ : decompose? s₄ ((bodyCtx F₂ (expression (pairBody.drop 23))).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F₂ (expression (pairBody.drop 23)), 1, 1, [.i32 0, .i32 2]) :=
    decompose_fill _ trivial hs₄f.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₆ := TSession.call (TSession.of_core_steps t₅
    (((((st₆.steps.trans st₇.steps).trans st₈.steps).trans st₉.steps).trans
      st₁₀.steps).trans st₁₁.steps)) hd₃
  have t₇ := TSession.answer t₆ hd₃ (a := ⟨s₄, .values [.i32 (q + 1 + 1)]⟩)
    (q' := q + 1 + 1 + 1) ⟨rfl, rfl⟩
  -- accept
  have st₁₂ : Step P NH ⟨s₄, {}, (bodyCtx F₂ (expression (pairBody.drop 23))).fill
      (Result.values [.i32 (q + 1 + 1)]).toAdmin⟩
      ⟨s₄, {}, (bodyCtx F₂ []).fill
        (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 2), .callRefType f₂.type])⟩ :=
    step_body (step_mid [.i32 (q + 1 + 1)] [] (step_call (x := ⟨2⟩) (by rw [hF₂f]; rfl)
      hs₄f.2.2.1))
  have hd₄ : decompose? s₄ ((bodyCtx F₂ []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 2), .callRefType f₂.type])) =
      some (bodyCtx F₂ [], 2, 2, [.i32 (q + 1 + 1)]) :=
    decompose_fill _ trivial hs₄f.2.2.1 he₂ (by rw [hn₂]; rfl) hc₂
  have t₈ := TSession.call (TSession.of_core_steps t₇ st₁₂.steps) hd₄
  -- the decoded events
  have hco₁ : calloutAt? pairMod (some 0) ⟨s₁, {}, (bodyCtx F (expression (pairBody.drop 6))).fill
      (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (co "symbol" ⟨0⟩ s₁ [.i32 16, .i32 1]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? pairMod (some 0) ⟨s₂, {}, (bodyCtx F₁ (expression (pairBody.drop 13))).fill
      (vals [.i32 16, .i32 1] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (co "symbol" ⟨0⟩ s₂ [.i32 16, .i32 1]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? pairMod (some 0) ⟨s₄, {}, (bodyCtx F₂ (expression (pairBody.drop 23))).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (co "sexp" ⟨0⟩ s₄ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hco₄ : calloutAt? pairMod (some 0) ⟨s₄, {}, (bodyCtx F₂ []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 2), .callRefType f₂.type])⟩ =
      some (co "accept" ⟨1⟩ s₄ [.i32 (q + 1 + 1)]) := by
    unfold calloutAt?; rw [hd₄]; rfl
  have hw₁ : memWrite {} (co "symbol" ⟨0⟩ s₁ [.i32 16, .i32 1])
      ⟨.values [.i32 q], memOf (some 0) s₁⟩ = some (.write (.atom symA) [] q) := by
    refine memWrite_symbol_eq rfl ?_ utf8_a rfl
    rw [bytes32_of_store hml hst₁ rfl]
    decide
  have hw₂ : memWrite {} (co "symbol" ⟨0⟩ s₂ [.i32 16, .i32 1])
      ⟨.values [.i32 (q + 1)], memOf (some 0) s₂⟩ = some (.write (.atom symB) [] (q + 1)) := by
    refine memWrite_symbol_eq rfl ?_ utf8_b rfl
    rw [bytes32_of_store hl₁ hst₂ rfl]
    decide
  have h₀ : bytesAt b₄ ⟨0, 4⟩ = (Memory.encodeLE 4 q.toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hst₄ (.inr (by decide))]
    exact bytes_of_store32 hst₃
  have h₄ : bytesAt b₄ ⟨4, 4⟩ = (Memory.encodeLE 4 (q + 1).toNat).data.toList :=
    bytes_of_store32 hst₄
  have hh : handles32 (co "sexp" ⟨0⟩ s₄ [.i32 0, .i32 2]) = some [q, q + 1] :=
    handles32_pair (memOf_setMem hl₃) (by rw [hz₄]; decide) h₀ h₄
  have hw₃ : memWrite {} (co "sexp" ⟨0⟩ s₄ [.i32 0, .i32 2])
      ⟨.values [.i32 (q + 1 + 1)], memOf (some 0) s₄⟩ =
      some (.write .list [q, q + 1] (q + 1 + 1)) :=
    memWrite_sexp_eq rfl (by show ("sexp", "sexp") ≠ ("sexp", "symbol"); decide)
      (by show ("sexp", "sexp") ≠ ("sexp", "string"); decide)
      (by show ("sexp", "sexp") ≠ ("sexp", "blob"); decide) hh rfl
  have hna₁ : memAccept {} (co "symbol" ⟨0⟩ s₁ [.i32 16, .i32 1]) = none :=
    memAccept_eq_none (by show ("sexp", "symbol") ≠ ("sexp", "accept"); decide)
  have hna₂ : memAccept {} (co "symbol" ⟨0⟩ s₂ [.i32 16, .i32 1]) = none :=
    memAccept_eq_none (by show ("sexp", "symbol") ≠ ("sexp", "accept"); decide)
  have hna₃ : memAccept {} (co "sexp" ⟨0⟩ s₄ [.i32 0, .i32 2]) = none :=
    memAccept_eq_none (by show ("sexp", "sexp") ≠ ("sexp", "accept"); decide)
  have hac : memAccept {} (co "accept" ⟨1⟩ s₄ [.i32 (q + 1 + 1)]) =
      some (.accept (q + 1 + 1)) := by
    simp [memAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  rw [hco₁, hco₂, hco₃, hco₄] at t₈
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply pairOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₈⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, memRoles]
  rw [hna₁, hw₁, hna₂, hw₂, hna₃, hw₃, hac]
  rfl

/-- **`pairMod` accepts `(a b)`**, for every profile and policy. -/
theorem pairMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    pairTree ∈ memWriterLang P (ReplyEnvs pairReply) 0 pairMod {} pol := by
  let q := base pol
  have hn₀ : pol.sentinel ≠ some q := by simpa using base_ne pol (k := 0) (by decide)
  have hn₁ : pol.sentinel ≠ some (q + 1) := base_ne pol (k := 1) (by decide)
  have hn₂ : pol.sentinel ≠ some (q + 1 + 1) := by
    rw [BitVec.add_assoc]; exact base_ne pol (k := 1 + 1) (by decide)
  have d₁ : q + 1 ≠ q := by bv_omega
  have d₂ : q + 1 + 1 ≠ q := by bv_omega
  have d₃ : q + 1 + 1 ≠ q + 1 := by bv_omega
  have e₁ : Function.update (Env.empty : Env (BitVec 32) SymStrBytesSExp) q
      (some (.atom symA)) (q + 1) = none := by
    rw [Function.update_of_ne d₁]; rfl
  have e₂ : Function.update (Function.update (Env.empty : Env (BitVec 32) SymStrBytesSExp) q
      (some (.atom symA))) (q + 1) (some (.atom symB)) (q + 1 + 1) = none := by
    rw [Function.update_of_ne d₃, Function.update_of_ne d₂]; rfl
  have hb : (sexpW MemAtom).built (Function.update (Function.update
      (Env.empty : Env (BitVec 32) SymStrBytesSExp) q (some (.atom symA))) (q + 1)
      (some (.atom symB))) .list [q, q + 1] = some pairTree := by
    simp [Writer.built, Env.lookupAll, sexpW, pairTree]
  simp only [memWriterLang, writerLang, Host.lang]
  refine Set.mem_biUnion (pair_traces P q) ⟨_, _, .cons .enter
    (.cons (.writeOk (t := .atom symA) rfl ⟨hn₀, .inl rfl⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := .atom symB) rfl ⟨hn₁, .inl e₁⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := pairTree) hb ⟨hn₂, .inl e₂⟩ fun _ h => by cases h)
    (.cons (.acceptOk (t := pairTree) (by simp)) (.nil _))))), by simp⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Pair
