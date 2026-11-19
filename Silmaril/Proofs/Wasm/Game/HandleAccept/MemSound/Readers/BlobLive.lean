module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.Blob
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveItems

/-!
# Proofs: `blobMod` accepts every blob of two bytes

The session of `Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.KwTextLive` with `blob_bytes`,
for any two bytes `b₀ b₁`: against `itemsEnv (blobWord b₀ b₁) 0` the host writes `(8, 2)` at
`[0, 8)` and the bytes `b₀ b₁` at `[8, 10)` (`take2_blobWord`); `blob_bytes(h, 0)` is decoded as
the read of the blob `[b₀, b₁]`, the length is `2`, and `accept(h)` follows (`blob_traces`).
`blobMod_live_of` accepts every member of `twoByteBlobs` named by some fixed environment.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Wasm.Game.HandleAccept.MemSound.Live Silmaril.Wasm.Game.HandleAccept.MemSound.Text
  Silmaril.Wasm.Game.HandleAccept.MemSound.Readers
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Text
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Items
open Silmaril.Wasm.Logic.Core (bytesAt leNat)

/-- The blob of the bytes `bs`. -/
abbrev blobOf (bs : List UInt8) : MemAtom := ⟨.bytes, by decide, bs⟩

/-- The `i32` whose two low little-endian bytes are `b₀ b₁` (the high bytes zero). -/
def blobWord (b₀ b₁ : UInt8) : BitVec 32 := BitVec.ofNat 32 (b₀.toNat + 256 * b₁.toNat)

/-- The first two little-endian bytes of `blobWord b₀ b₁` are `b₀ b₁`. -/
theorem take2_blobWord (b₀ b₁ : UInt8) :
    ((Memory.encodeLE 4 (blobWord b₀ b₁).toNat).data.toList).take 2 = [b₀, b₁] := by
  have h₀ := b₀.toNat_lt
  have h₁ := b₁.toNat_lt
  have hn : (blobWord b₀ b₁).toNat = b₀.toNat + 256 * b₁.toNat := by
    unfold blobWord
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hn, Silmaril.Wasm.Logic.Core.toList_encodeLE, show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, List.take_succ_cons, List.take_zero]
  refine congrArg₂ (· :: ·) ?_ (congrArg₂ (· :: ·) ?_ rfl) <;> apply UInt8.toNat_inj.mp <;>
    simp; omega

theorem blobSpec_some : (Silmaril.Wasm.Verify.specInstance? blobMod).isSome = true := by
  decide +kernel

theorem blobMem : memSizes blobMod = [65536] := by decide +kernel

/-- The parameter of `check` is an `i32`. -/
def blobParamOk : Bool :=
  match prep blobMod with
  | some (c, _) =>
    match c.store.funcs[2]? with
    | some fi =>
      match fi.type.expand? with
      | some (.func ps _) => decide (ps.toList = [.num (.int .i32)])
      | _ => false
    | none => false
  | none => false

theorem blobParamOk_true : blobParamOk = true := by decide +kernel

theorem blob_param {c : Config Nat} {st : Option FuncIdx} (hp : prep blobMod = some (c, st))
    {fi : FuncInst Nat} (hf : c.store.funcs[2]? = some fi) {ps rs : Ty (.list .val)}
    (he : Expand fi.type (.func ps rs)) : ps.toList = [.num (.int .i32)] := by
  have h := blobParamOk_true
  unfold blobParamOk at h
  rw [hp] at h
  simp only [hf, Expand.iff.1 he] at h
  exact of_decide_eq_true h

/-- **The reader trace of the session.** -/
theorem blob_traces (P : Profile) (h : BitVec 32) (x₀ x₁ : UInt8) :
    [.enter, .read (.atom h) (.atom (blobOf [x₀, x₁])), .accept h] ∈
      blobTraces P (ReplyEnvs itemsReply) 0 blobMod {} := by
  let h₁ : BitVec 32 := blobWord x₀ x₁
  let h₂ : BitVec 32 := 0
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists blobSpec_some
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := blob_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page blobMem hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, -⟩ := fnOk_spec h2
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hfs : ∀ s : Store Nat, s.funcs = c.store.funcs → s.funcs[0]? = some f₀ ∧
      s.funcs[1]? = some f₁ ∧ s.funcs[2]? = some f₂ := by
    intro s hs; rw [hs, hf]; exact ⟨rfl, rfl, rfl⟩
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  have hpar := blob_param hp (hfs _ rfl).2.2 he
  let L := itemsEnv h₁ h₂
  let R := blobRoles {}
  have t₀ : TSession P L blobMod (some 0) R c () Is.addrs .inst false (c, ()) [] := .start
  have hok : InvokeOk c.store 2 [.i32 h] := ⟨f₂, ps, rs, (hfs _ rfl).2.2, he, by
    rw [hpar]; exact .cons (.num _) .nil⟩
  have ha : 2 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  -- enter `check(h)`
  have st₀ : Step P NH (invoke c.store 2 [.i32 h])
      ⟨c.store, {}, [.frame 0 (Frame.forCall f₂.module [.i32 h] [])
        [.label 0 [] (expression itemsBody)]]⟩ := by
    have hst := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[2]?.map FuncInst.type).getD default)) (vs := [.i32 h])
      (a := 2) (fi := f₂) (code := code) trivial (hfs _ rfl).2.2 he (by rw [hps]; rfl) hcode2
    rw [hrs, hloc, hbody] at hst
    exact hst
  have hFf : (Frame.forCall f₂.module [.i32 h] []).module.funcs = [0, 1, 2] := by
    simp [Frame.forCall, hfuncs]
  have hFm : (Frame.forCall f₂.module [.i32 h] []).module.mems = [0] := by
    simp [Frame.forCall, hmems2]
  have hv : (Frame.forCall f₂.module [.i32 h] []).local? ⟨0⟩ = some (some (.i32 h)) := by
    simp [Frame.forCall, Frame.local?, Idx.toNat]
  generalize Frame.forCall f₂.module [.i32 h] [] = F at st₀ hFf hFm hv
  -- items(h, 0)
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression itemsBody)]]⟩
      ⟨c.store, {}, [.frame 0 F [.label 0 [] (vals [] ++ [(Val.i32 h).toAdmin] ++
        expression (itemsBody.drop 1))]]⟩ :=
    step_body (step_mid [] (expression (itemsBody.drop 1)) (step_localGet hv))
  have st₂ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 []
        (vals [] ++ [(Val.i32 h).toAdmin] ++
        expression (itemsBody.drop 1))]]⟩
      ⟨c.store, {}, (bodyCtx F (expression (itemsBody.drop 3))).fill
        (vals [.i32 h, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 h, .i32 0] (expression (itemsBody.drop 3))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) (hfs _ rfl).1))
  have hd₁ : decompose? c.store ((bodyCtx F (expression (itemsBody.drop 3))).fill
      (vals [.i32 h, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (itemsBody.drop 3)), 0, 0, [.i32 h, .i32 0]) :=
    decompose_fill _ trivial (hfs _ rfl).1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  -- the host writes the list
  obtain ⟨b₁, hb₁⟩ := store_some (B := mi.bytes) (a := 0) (n := IntType.i32.width / 8)
    ((8 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  have hz₁ : b₁.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hb₁).trans hsize
  obtain ⟨b₂, hb₂⟩ := store_some (B := b₁) (a := 4) (n := IntType.i32.width / 8)
    ((2 : BitVec 32).setWidth _) (by rw [hz₁]; decide)
  have hz₂ : b₂.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hb₂).trans hz₁
  obtain ⟨b₃, hb₃⟩ := store_some (B := b₂) (a := 8) (n := IntType.i32.width / 8)
    (h₁.setWidth _) (by rw [hz₂]; decide)
  have hz₃ : b₃.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hb₃).trans hz₂
  obtain ⟨b₄, hb₄⟩ := store_some (B := b₃) (a := 12) (n := IntType.i32.width / 8)
    (h₂.setWidth _) (by rw [hz₃]; decide)
  have hz₄ : b₄.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hb₄).trans hz₃
  have hib : itemsBytes h₁ h₂ mi.bytes = some b₄ := by
    simp only [itemsBytes, put32, hb₁, hb₂, hb₃, hb₄, Option.bind_some]
  let s₁ := c.store.setMem 0 { mi with bytes := b₄ }
  have hs₁ : itemsStore h₁ h₂ c.store = s₁ := by
    simp only [itemsStore, hmi, hib, Option.bind_some, Option.map_some, Option.getD_some, s₁]
  obtain ⟨hm₁, hl₁, hf₁⟩ := setMem_mems (mi := { mi with bytes := b₄ }) hml
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values []⟩) (q' := ())
    (by show _ = _; rw [← hs₁]; rfl)
  -- the length
  have h8 : bytesAt b₄ ⟨0, 4⟩ = (Memory.encodeLE 4 (8 : BitVec 32).toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₄ (.inr (by decide)),
      Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₃ (.inr (by decide)),
      Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₂ (.inr (by decide))]
    exact bytes_of_store32 hb₁
  have h2b : bytesAt b₄ ⟨4, 4⟩ = (Memory.encodeLE 4 (2 : BitVec 32).toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₄ (.inr (by decide)),
      Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₃ (.inr (by decide))]
    exact bytes_of_store32 hb₂
  have hh₁ : bytesAt b₄ ⟨8, 4⟩ = (Memory.encodeLE 4 h₁.toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₄ (.inr (by decide))]
    exact bytes_of_store32 hb₃
  have hh₂ : bytesAt b₄ ⟨12, 4⟩ = (Memory.encodeLE 4 h₂.toNat).data.toList :=
    bytes_of_store32 hb₄
  have hld : Memory.load b₄ (effAddr (0 : BitVec 32).toNat ⟨0, 4⟩) (IntType.i32.width / 8) =
      some 2 := by
    rw [show effAddr (0 : BitVec 32).toNat ⟨0, 4⟩ = 4 from rfl,
      show IntType.i32.width / 8 = 4 from rfl,
      Silmaril.Wasm.Logic.Core.load_eq (by rw [hz₄]; decide), h2b]
    decide
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (itemsBody.drop 3))).fill
      (Result.values []).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++
        [.plain (.intConst .i32 ((2 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32))] ++
        expression (itemsBody.drop 5))]]⟩ :=
    step_body (step_mid [] (expression (itemsBody.drop 5))
      (.memory (.loadIntVal (t := .i32) (a := .i32) (i := 0) (mem?_of hFm hm₁) hld)))
  have hne : constI32 (intRelOp IntType.i32 IntRelOp.ne
      ((2 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32) 2) = constI32 0 :=
    congrArg constI32 (by decide)
  have st₄ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++
        [.plain (.intConst .i32 ((2 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32))] ++
        expression (itemsBody.drop 5))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [constI32 0] ++
        expression (itemsBody.drop 7))]]⟩ := by
    have hst := step_body (P := P) (host := NH) (s := s₁) (f := {}) (n := 0) (k := 0)
      (step_mid [] (expression (itemsBody.drop 7)) (Step.numeric (P := P) (host := NH) (s := s₁)
        (f := F) (NumericStep.intRelOp (t := .i32) (op := .ne)
          (x := (2 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32) (y := 2))))
    rw [hne] at hst
    exact hst
  -- `if` (false), the empty `else` block
  have st₅ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [constI32 0] ++
        expression (itemsBody.drop 7))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [.plain (.block .empty [])] ++
        expression (itemsBody.drop 8))]]⟩ :=
    step_body (step_mid [] (expression (itemsBody.drop 8)) Step.ifFalse)
  have st₆ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++
        [.plain (.block .empty [])] ++ expression (itemsBody.drop 8))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [.label 0 [] (vals [] ++ expression [])] ++
        expression (itemsBody.drop 8))]]⟩ :=
    step_body (step_mid [] (expression (itemsBody.drop 8))
      (Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl))
  have st₇ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++
        [.label 0 [] (vals [] ++ expression [])] ++ expression (itemsBody.drop 8))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ vals [] ++
        expression (itemsBody.drop 8))]]⟩ :=
    step_body (step_mid [] (expression (itemsBody.drop 8)) (Step.labelVals (vs := [])))
  -- accept(h)
  have st₈ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ vals [] ++
        expression (itemsBody.drop 8))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [(Val.i32 h).toAdmin] ++
        expression (itemsBody.drop 9))]]⟩ :=
    step_body (step_mid [] (expression (itemsBody.drop 9)) (step_localGet hv))
  have hs₁f := hfs s₁ hf₁
  have st₉ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [(Val.i32 h).toAdmin] ++
        expression (itemsBody.drop 9))]]⟩
      ⟨s₁, {}, (bodyCtx F []).fill
        (vals [.i32 h] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 h] [] (step_call (x := ⟨1⟩) (by rw [hFf]; rfl) hs₁f.2.1))
  have hd₂ : decompose? s₁ ((bodyCtx F []).fill
      (vals [.i32 h] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F [], 1, 1, [.i32 h]) :=
    decompose_fill _ trivial hs₁f.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₄ := TSession.call (TSession.of_core_steps t₃
    ((((((st₃.steps.trans st₄.steps).trans st₅.steps).trans st₆.steps).trans
      st₇.steps).trans st₈.steps).trans st₉.steps)) hd₂
  -- the decoded events
  have hco₁ : calloutAt? blobMod (some 0) ⟨c.store, {},
      (bodyCtx F (expression (itemsBody.drop 3))).fill
        (vals [.i32 h, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn ⟨"sexp", "blob_bytes", .func ⟨0⟩⟩ (some 0) c.store
        [.i32 h, .i32 0]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? blobMod (some 0) ⟨s₁, {}, (bodyCtx F []).fill
      (vals [.i32 h] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨"sexp", "accept", .func ⟨1⟩⟩ (some 0) s₁ [.i32 h]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hlist : bytesList b₄ 0 = some [x₀, x₁] := by
    unfold bytesList
    have e₀ : segOf b₄ 0 8 = some ((Memory.encodeLE 4 (8 : BitVec 32).toNat).data.toList ++
        (Memory.encodeLE 4 (2 : BitVec 32).toNat).data.toList) := by
      unfold segOf
      rw [readBytes_toList (by rw [hz₄]; decide),
        show (8 : Nat) = 4 + 4 from rfl, bytesAt_append, h8, h2b]
    have e₁ : segOf b₄ (8 : BitVec 32).toNat (2 : BitVec 32).toNat = some [x₀, x₁] := by
      unfold segOf
      rw [show (8 : BitVec 32).toNat = 8 from rfl, show (2 : BitVec 32).toNat = 2 from rfl,
        readBytes_toList (by rw [hz₄]; decide)]
      have : bytesAt b₄ ⟨8, 2⟩ = (bytesAt b₄ ⟨8, 4⟩).take 2 := by
        simp [bytesAt, List.take_take]
      rw [this, hh₁]
      exact congrArg some (take2_blobWord x₀ x₁)
    simp only [Option.bind_eq_bind, e₀, Option.bind_some]
    rw [le32s_encode, ← List.append_nil (Memory.encodeLE 4 (2 : BitVec 32).toNat).data.toList,
      le32s_encode]
    simp only [le32s, Option.map_some, Option.bind_some, pair32]
    exact e₁
  have hrd : blobRead {} (calloutIn ⟨"sexp", "blob_bytes", .func ⟨0⟩⟩ (some 0) c.store
      [.i32 h, .i32 0]) ⟨.values [], memOf (some 0) s₁⟩ =
      some (.read (.atom h) (.atom (blobOf [x₀, x₁]))) := by
    have hm : memOf (some 0) s₁ = some b₄ := memOf_setMem hml
    simp [blobRead, calloutIn, Val.i32, blobAns, hm, hlist, blobOf]
  have hna : blobAccept {} (calloutIn ⟨"sexp", "blob_bytes", .func ⟨0⟩⟩ (some 0) c.store
      [.i32 h, .i32 0]) = none := by
    simp [blobAccept, calloutIn]
  have hac : blobAccept {}
      (calloutIn ⟨"sexp", "accept", .func ⟨1⟩⟩ (some 0) s₁ [.i32 h]) =
      some (.accept h) := by
    simp [blobAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  rw [hco₁, hco₂] at t₄
  refine ⟨_, ⟨mt, Is, c, hI, L, (), itemsEnv_reply h₁ h₂ _, .run, true, _,
    by rw [hmem0]; exact t₄⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, blobRoles]
  rw [hna, hrd, hac]
  rfl

/-- **`blobMod` accepts the blob of every two bytes** `b₀ b₁` whenever a fixed
environment of `Rhos` names it, for every profile and accept policy. -/
theorem blobMod_live_of (P : Profile) (oa : OnInvalid)
    {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)} {ρ : Env (BitVec 32) SymStrBytesSExp}
    (hρ : ρ ∈ Rhos) {h : BitVec 32} {b₀ b₁ : UInt8} (e : ρ h = some (.atom (blobOf [b₀, b₁]))) :
    .atom (blobOf [b₀, b₁]) ∈ blobReaderLang P (ReplyEnvs itemsReply) 0 blobMod {} .trap oa Rhos := by
  have hans : answers (sexpR MemAtom (BitVec 32)) .trap ρ (.atom h) =
      some {a | (sexpR MemAtom (BitVec 32)).ok ρ (.atom h) a} := by
    unfold answers
    split_ifs with hv
    · rfl
    · exact absurd ⟨blobOf [b₀, b₁], e⟩ hv
  simp only [blobReaderLang, readerLang, langOver, Host.lang]
  refine Set.mem_iUnion.2 ⟨⟨ρ, hρ⟩, Set.mem_biUnion (blob_traces P h b₀ b₁)
    ⟨_, _, .cons .enter
    (.cons (.read hans e) (.cons (.acceptOk (t := .atom (blobOf [b₀, b₁])) e) (.nil _))), by simp⟩⟩

/-- **Every two-byte blob named in `Rhos` is accepted.** -/
theorem twoByteBlobs_subset (P : Profile) (oa : OnInvalid)
    {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)}
    (hR : ∀ x ∈ twoByteBlobs, ∃ ρ ∈ Rhos, ∃ h, ρ h = some x) :
    twoByteBlobs ⊆ blobReaderLang P (ReplyEnvs itemsReply) 0 blobMod {} .trap oa Rhos := by
  rintro x hx
  obtain ⟨ρ, hρ, h, e⟩ := hR x hx
  obtain ⟨bs, hl, rfl⟩ := hx
  match bs, hl with
  | [b₀, b₁], _ => exact blobMod_live_of P oa hρ e

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers
