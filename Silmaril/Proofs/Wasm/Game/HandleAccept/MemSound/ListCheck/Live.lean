module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Sound
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.SymLive

/-!
# Proofs: the list checkers accept lists of two symbols (two blobs)

Against `listEnv w w` (every `items` and `child` call writes the words `8, 2, w, w` at
`[0, 16)`), the traced session of `listMod ix` invokes `check(h)` and runs: `items(h, 0)`
(decoded as the read of the children `[w, w]`), the load of the length `2`, the empty `else`
block, the loads of the pointer `8` and of the two handles `w` (stored in the locals),
`child(w, 0)` twice (decoded from the memory after each answer, where the `list<u8>` at the return
pointer `0` is the two low bytes of `w`) and `accept(h)` (`list_traces`). With
`w = symWord b₀ b₁`, the child reads are the symbol of the UTF-8 text of `b₀ b₁` (the blob of
`b₀ b₁`); in a fixed environment where `h` denotes the list of two copies of it and `w` denotes
it, every read is correct and `h` is accepted (`symListMod_live_of`, `blobListMod_live_of`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Wasm.Game.HandleAccept.MemSound.Live Silmaril.Wasm.Game.HandleAccept.MemSound.Text
  Silmaril.Wasm.Game.HandleAccept.MemSound.Readers
  Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Items
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers
open Silmaril.Wasm.Logic.Core (bytesAt leNat)

/-! ## The written memory -/

/-- A page holding the words `8, 2, w, w` at `[0, 16)`, little-endian. -/
def Written (w : BitVec 32) (B : ByteArray) : Prop :=
  B.size = 65536 ∧
  bytesAt B ⟨0, 4⟩ = (Memory.encodeLE 4 (8 : BitVec 32).toNat).data.toList ∧
  bytesAt B ⟨4, 4⟩ = (Memory.encodeLE 4 (2 : BitVec 32).toNat).data.toList ∧
  bytesAt B ⟨8, 4⟩ = (Memory.encodeLE 4 w.toNat).data.toList ∧
  bytesAt B ⟨12, 4⟩ = (Memory.encodeLE 4 w.toNat).data.toList

/-- The host's write on a page. -/
theorem written_of (w : BitVec 32) {B : ByteArray} (hB : B.size = 65536) :
    ∃ B', itemsBytes w w B = some B' ∧ Written w B' := by
  obtain ⟨b₁, hb₁⟩ := store_some (B := B) (a := 0) (n := IntType.i32.width / 8)
    ((8 : BitVec 32).setWidth _) (by rw [hB]; decide)
  have hz₁ : b₁.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hb₁).trans hB
  obtain ⟨b₂, hb₂⟩ := store_some (B := b₁) (a := 4) (n := IntType.i32.width / 8)
    ((2 : BitVec 32).setWidth _) (by rw [hz₁]; decide)
  have hz₂ : b₂.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hb₂).trans hz₁
  obtain ⟨b₃, hb₃⟩ := store_some (B := b₂) (a := 8) (n := IntType.i32.width / 8)
    (w.setWidth _) (by rw [hz₂]; decide)
  have hz₃ : b₃.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hb₃).trans hz₂
  obtain ⟨b₄, hb₄⟩ := store_some (B := b₃) (a := 12) (n := IntType.i32.width / 8)
    (w.setWidth _) (by rw [hz₃]; decide)
  have hz₄ : b₄.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hb₄).trans hz₃
  refine ⟨b₄, by simp only [itemsBytes, put32, hb₁, hb₂, hb₃, hb₄, Option.bind_some], hz₄,
    ?_, ?_, ?_, bytes_of_store32 hb₄⟩
  · rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₄ (.inr (by decide)),
      Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₃ (.inr (by decide)),
      Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₂ (.inr (by decide))]
    exact bytes_of_store32 hb₁
  · rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₄ (.inr (by decide)),
      Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₃ (.inr (by decide))]
    exact bytes_of_store32 hb₂
  · rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hb₄ (.inr (by decide))]
    exact bytes_of_store32 hb₃

/-- An `i32` load of an encoded word. -/
theorem load_written {B : ByteArray} {a : Nat} {v : BitVec 32} (hz : a + 4 ≤ B.size)
    (hb : bytesAt B ⟨a, 4⟩ = (Memory.encodeLE 4 v.toNat).data.toList) :
    Memory.load B a 4 = some (v : BitVec (8 * 4)) := by
  rw [Silmaril.Wasm.Logic.Core.load_eq hz, hb,
    Silmaril.Wasm.Logic.Core.leNat_encodeLE]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have := v.isLt
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMul] at this ⊢
  omega

/-- An `i32` load of an encoded word, at the width of the load rule. -/
theorem load_written' {B : ByteArray} {a : Nat} {v : BitVec 32} (hz : a + 4 ≤ B.size)
    (hb : bytesAt B ⟨a, 4⟩ = (Memory.encodeLE 4 v.toNat).data.toList) :
    Memory.load B a (IntType.i32.width / 8) =
      some (BitVec.ofNat (8 * (IntType.i32.width / 8)) v.toNat) := by
  show Memory.load B a 4 = some (BitVec.ofNat (8 * 4) v.toNat)
  rw [load_written hz hb]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

/-- The returned `list<i32>` is `[w, w]`. -/
theorem written_itemsList {w : BitVec 32} {B : ByteArray} (hW : Written w B) :
    itemsList B 0 = some [w, w] := by
  obtain ⟨hz, h8, h2b, hh₁, hh₂⟩ := hW
  unfold itemsList
  have e₀ : segOf B 0 8 = some ((Memory.encodeLE 4 (8 : BitVec 32).toNat).data.toList ++
      (Memory.encodeLE 4 (2 : BitVec 32).toNat).data.toList) := by
    unfold segOf
    rw [readBytes_toList (by rw [hz]; decide),
      show (8 : Nat) = 4 + 4 from rfl, bytesAt_append, h8, h2b]
  have e₁ : segOf B (8 : BitVec 32).toNat (4 * (2 : BitVec 32).toNat) =
      some ((Memory.encodeLE 4 w.toNat).data.toList ++
        (Memory.encodeLE 4 w.toNat).data.toList) := by
    unfold segOf
    rw [show (8 : BitVec 32).toNat = 8 from rfl, show 4 * (2 : BitVec 32).toNat = 4 + 4 from rfl,
      readBytes_toList (by rw [hz]; decide), bytesAt_append, hh₁, hh₂]
  simp only [Option.bind_eq_bind, e₀, Option.bind_some]
  rw [le32s_encode, ← List.append_nil (Memory.encodeLE 4 (2 : BitVec 32).toNat).data.toList,
    le32s_encode]
  simp only [le32s, Option.map_some, Option.bind_some, pair32]
  rw [e₁, Option.bind_some, le32s_encode,
    ← List.append_nil (Memory.encodeLE 4 w.toNat).data.toList, le32s_encode]
  rfl

/-- The returned `list<u8>` is the two low bytes of `w`. -/
theorem written_bytesList {b₀ b₁ : UInt8} {B : ByteArray} (hW : Written (symWord b₀ b₁) B) :
    bytesList B 0 = some [b₀, b₁] := by
  obtain ⟨hz, h8, h2b, hh₁, -⟩ := hW
  unfold bytesList
  have e₀ : segOf B 0 8 = some ((Memory.encodeLE 4 (8 : BitVec 32).toNat).data.toList ++
      (Memory.encodeLE 4 (2 : BitVec 32).toNat).data.toList) := by
    unfold segOf
    rw [readBytes_toList (by rw [hz]; decide),
      show (8 : Nat) = 4 + 4 from rfl, bytesAt_append, h8, h2b]
  have e₁ : segOf B (8 : BitVec 32).toNat (2 : BitVec 32).toNat = some [b₀, b₁] := by
    unfold segOf
    rw [show (8 : BitVec 32).toNat = 8 from rfl, show (2 : BitVec 32).toNat = 2 from rfl,
      readBytes_toList (by rw [hz]; decide)]
    have : bytesAt B ⟨8, 2⟩ = (bytesAt B ⟨8, 4⟩).take 2 := by
      simp [bytesAt, List.take_take]
    rw [this, hh₁]
    exact congrArg some (take2_symWord b₀ b₁)
  simp only [Option.bind_eq_bind, e₀, Option.bind_some]
  rw [le32s_encode, ← List.append_nil (Memory.encodeLE 4 (2 : BitVec 32).toNat).data.toList,
    le32s_encode]
  simp only [le32s, Option.map_some, Option.bind_some, pair32]
  exact e₁

/-! ## Instance facts -/

/-- The spec instance exists, its memory is one page, and the parameter of `check` is an
`i32`. -/
def listLiveOk (ix : ListImports) : Bool :=
  (Silmaril.Wasm.Verify.specInstance? (listMod ix)).isSome &&
  memSizes (listMod ix) == [65536] &&
  match prep (listMod ix) with
  | some (c, _) =>
    match c.store.funcs[3]? with
    | some fi =>
      match fi.type.expand? with
      | some (.func ps _) => decide (ps.toList = [.num (.int .i32)])
      | _ => false
    | none => false
  | none => false

theorem listLiveOk_sym : listLiveOk {} = true := by decide +kernel

theorem listLiveOk_blob : listLiveOk blobImports = true := by decide +kernel

theorem list_live_facts {ix : ListImports} (hok : listLiveOk ix = true) :
    (Silmaril.Wasm.Verify.specInstance? (listMod ix)).isSome = true ∧
    memSizes (listMod ix) = [65536] ∧
    ∀ {c : Config Nat} {st : Option FuncIdx}, prep (listMod ix) = some (c, st) →
      ∀ {fi : FuncInst Nat}, c.store.funcs[3]? = some fi → ∀ {ps rs : Ty (.list .val)},
        Expand fi.type (.func ps rs) → ps.toList = [.num (.int .i32)] := by
  unfold listLiveOk at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨h1, h2⟩, h3⟩ := hok
  refine ⟨h1, h2, ?_⟩
  intro c st hp fi hf ps rs he
  rw [hp] at h3
  simp only [hf, Expand.iff.1 he] at h3
  exact of_decide_eq_true h3

/-- The `listEnv` replies are admitted by `itemsReply`. -/
theorem listEnv_reply (h₁ h₂ : BitVec 32) (s : Store Nat) :
    ReplyEnvs itemsReply s (listEnv h₁ h₂) := by
  rintro q e a q' rfl
  refine ⟨?_, fun vs hv => by cases hv; rfl⟩
  by_cases h0 : e.target = 0 ∨ e.target = 1
  · simp only [h0, ↓reduceIte]
    exact itemsStore_keeps h₁ h₂ e.store
  · simp only [h0, ↓reduceIte]
    exact ⟨rfl, rfl⟩

/-! ## The session -/

/-- **The reader trace of the session**, for a child reader whose answer on every written page
is `a`. -/
theorem list_traces (P : Profile) {ix : ListImports} (hok : listOk ix = true)
    (hlive : listLiveOk ix = true) {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)}
    (h w : BitVec 32) {a : SxA MemAtom (BitVec 32)}
    (hA : ∀ B, Written w B → ans ⟨.values [], some B⟩ 0 = a) :
    [.enter, .read (.items h) (.items [w, w]), .read (.atom w) a, .read (.atom w) a, .accept h] ∈
      listTraces P (ReplyEnvs itemsReply) 0 (listMod ix) ix ans := by
  obtain ⟨hspec, hmem, hparam⟩ := list_live_facts hlive
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists hspec
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨hne, rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, hf, h0, h1, h2, h3⟩ :=
    list_facts hok hp
  obtain ⟨mi, hmis, hsize⟩ := one_page hmem hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  obtain ⟨code, ps, rs, hcode3, hloc, hbody, he, hps, hrs, hfuncs, hmems3, hD⟩ := fnOk_spec h3
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hfs : ∀ s : Store Nat, s.funcs = c.store.funcs → s.funcs[0]? = some f₀ ∧
      s.funcs[1]? = some f₁ ∧ s.funcs[2]? = some f₂ ∧ s.funcs[3]? = some f₃ := by
    intro s hs; rw [hs, hf]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  have hpar := hparam hp (hfs _ rfl).2.2.2 he
  let L := listEnv w w
  let R := listRoles ix ans
  have t₀ : TSession P L (listMod ix) (some 0) R c () Is.addrs .inst false (c, ()) [] := .start
  have hok' : InvokeOk c.store 3 [.i32 h] := ⟨f₃, ps, rs, (hfs _ rfl).2.2.2, he, by
    rw [hpar]; exact .cons (.num _) .nil⟩
  have ha : 3 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok'
  -- enter `check(h)`
  have st₀ : Step P NH (invoke c.store 3 [.i32 h])
      ⟨c.store, {}, [.frame 0 (Frame.forCall f₃.module [.i32 h] code.locals)
        [.label 0 [] (expression listBody)]]⟩ := by
    have hst := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[3]?.map FuncInst.type).getD default)) (vs := [.i32 h])
      (a := 3) (fi := f₃) (code := code) trivial (hfs _ rfl).2.2.2 he (by rw [hps]; rfl) hcode3
    rw [hrs, hbody] at hst
    exact hst
  have hFf : (Frame.forCall f₃.module [.i32 h] code.locals).module.funcs = [0, 1, 2, 3] := by
    simp [Frame.forCall, hfuncs]
  have hFm : (Frame.forCall f₃.module [.i32 h] code.locals).module.mems = [0] := by
    simp [Frame.forCall, hmems3]
  have hFl : (Frame.forCall f₃.module [.i32 h] code.locals).locals =
      [some (.i32 h), some (.i32 0), some (.i32 0)] := by
    unfold Frame.forCall
    dsimp only
    rw [hloc, hD]
    rfl
  generalize Frame.forCall f₃.module [.i32 h] code.locals = F at st₀ hFf hFm hFl
  have hv : F.local? ⟨0⟩ = some (some (.i32 h)) := by simp [Frame.local?, hFl, Idx.toNat]
  -- items(h, 0)
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression listBody)]]⟩
      ⟨c.store, {}, [.frame 0 F [.label 0 [] (vals [] ++ [(Val.i32 h).toAdmin] ++
        expression (listBody.drop 1))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 1)) (step_localGet hv))
  have st₂ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (vals [] ++ [(Val.i32 h).toAdmin] ++
        expression (listBody.drop 1))]]⟩
      ⟨c.store, {}, (bodyCtx F (expression (listBody.drop 3))).fill
        (vals [.i32 h, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 h, .i32 0] (expression (listBody.drop 3))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) (hfs _ rfl).1))
  have hd₁ : decompose? c.store ((bodyCtx F (expression (listBody.drop 3))).fill
      (vals [.i32 h, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (listBody.drop 3)), 0, 0, [.i32 h, .i32 0]) :=
    decompose_fill _ trivial (hfs _ rfl).1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  -- the host writes the list
  obtain ⟨B₁, hib₁, hW₁⟩ := written_of w hsize
  let mi₁ : MemInst := { mi with bytes := B₁ }
  let s₁ := c.store.setMem 0 mi₁
  have hs₁ : itemsStore w w c.store = s₁ := by
    simp only [itemsStore, hmi, hib₁, Option.bind_some, Option.map_some, Option.getD_some, s₁,
      mi₁]
  obtain ⟨hm₁, hl₁, hf₁⟩ := setMem_mems (mi := mi₁) hml
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values []⟩) (q' := ())
    (by show _ = _; rw [← hs₁]; rfl)
  -- the length
  have hld : Memory.load B₁ (effAddr (0 : BitVec 32).toNat ⟨0, 4⟩) (IntType.i32.width / 8) =
      some 2 := load_written (by rw [hW₁.1]; decide) hW₁.2.2.1
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (listBody.drop 3))).fill
      (Result.values []).toAdmin⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++
        [.plain (.intConst .i32 ((2 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32))] ++
        expression (listBody.drop 5))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 5))
      (.memory (.loadIntVal (t := .i32) (a := .i32) (i := 0) (mem?_of hFm hm₁) hld)))
  have hne2 : constI32 (intRelOp IntType.i32 IntRelOp.ne
      ((2 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32) 2) = constI32 0 :=
    congrArg constI32 (by decide)
  have st₄ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++
        [.plain (.intConst .i32 ((2 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32))] ++
        expression (listBody.drop 5))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [constI32 0] ++
        expression (listBody.drop 7))]]⟩ := by
    have hst := step_body (P := P) (host := NH) (s := s₁) (f := {}) (n := 0) (k := 0)
      (step_mid [] (expression (listBody.drop 7)) (Step.numeric (P := P) (host := NH) (s := s₁)
        (f := F) (NumericStep.intRelOp (t := .i32) (op := .ne)
          (x := (2 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32) (y := 2))))
    rw [hne2] at hst
    exact hst
  -- `if` (false), the empty `else` block
  have st₅ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [constI32 0] ++
        expression (listBody.drop 7))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [.plain (.block .empty [])] ++
        expression (listBody.drop 8))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 8)) Step.ifFalse)
  have st₆ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++
        [.plain (.block .empty [])] ++ expression (listBody.drop 8))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [.label 0 [] (vals [] ++ expression [])] ++
        expression (listBody.drop 8))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 8))
      (Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl))
  have st₇ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++
        [.label 0 [] (vals [] ++ expression [])] ++ expression (listBody.drop 8))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ vals [] ++
        expression (listBody.drop 8))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 8)) (Step.labelVals (vs := [])))
  -- the first handle
  have hldp : Memory.load B₁ (effAddr (0 : BitVec 32).toNat ⟨0, 0⟩) (IntType.i32.width / 8) =
      some 8 := load_written (by rw [hW₁.1]; decide) hW₁.2.1
  have st₈ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ vals [] ++
        expression (listBody.drop 8))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++
        [.plain (.intConst .i32 ((8 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32))] ++
        expression (listBody.drop 10))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 10))
      (.memory (.loadIntVal (t := .i32) (a := .i32) (i := 0) (mem?_of hFm hm₁) hldp)))
  have hw : BitVec.setWidth IntType.i32.width
      (BitVec.ofNat (8 * (IntType.i32.width / 8)) w.toNat) = w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := w.isLt
    simp only [IntType.width, Nat.reducePow, Nat.reduceMul, Nat.reduceDiv] at this ⊢
    omega
  have hld₁ : Memory.load B₁
      (effAddr ((8 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32).toNat ⟨0, 0⟩)
      (IntType.i32.width / 8) = some (BitVec.ofNat (8 * (IntType.i32.width / 8)) w.toNat) :=
    load_written' (a := 8) (by rw [hW₁.1]; decide) hW₁.2.2.2.1
  have st₉ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++
        [.plain (.intConst .i32 ((8 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32))] ++
        expression (listBody.drop 10))]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [(Val.i32 w).toAdmin] ++
        expression (listBody.drop 11))]]⟩ := by
    have hst := step_body (P := P) (host := NH) (s := s₁) (f := {}) (n := 0) (k := 0)
      (step_mid [] (expression (listBody.drop 11))
      (.memory (.loadIntVal (t := .i32) (a := .i32)
        (i := (8 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32) (mem?_of hFm hm₁) hld₁)))
    rw [hw] at hst
    exact hst
  have st₁₀ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (vals [] ++ [(Val.i32 w).toAdmin] ++
        expression (listBody.drop 11))]]⟩
      ⟨s₁, {}, [.frame 0 (F.setLocal ⟨1⟩ (.i32 w)) [.label 0 [] (vals [] ++ [] ++
        expression (listBody.drop 12))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 12))
      (step_localSet (by simp [hFl, Idx.toNat])))
  -- the second handle
  have hFm₁ : (F.setLocal ⟨1⟩ (.i32 w)).module.mems = [0] := hFm
  have st₁₁ : Step P NH ⟨s₁, {}, [.frame 0 (F.setLocal ⟨1⟩ (.i32 w)) [.label 0 [] (vals [] ++ [] ++
        expression (listBody.drop 12))]]⟩
      ⟨s₁, {}, [.frame 0 (F.setLocal ⟨1⟩ (.i32 w)) [.label 0 [] (vals [] ++
        [.plain (.intConst .i32 ((8 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32))] ++
        expression (listBody.drop 14))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 14))
      (.memory (.loadIntVal (t := .i32) (a := .i32) (i := 0) (mem?_of hFm₁ hm₁) hldp)))
  have hld₂ : Memory.load B₁
      (effAddr ((8 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32).toNat ⟨0, 4⟩)
      (IntType.i32.width / 8) = some (BitVec.ofNat (8 * (IntType.i32.width / 8)) w.toNat) :=
    load_written' (a := 12) (by rw [hW₁.1]; decide) hW₁.2.2.2.2
  have st₁₂ : Step P NH ⟨s₁, {}, [.frame 0 (F.setLocal ⟨1⟩ (.i32 w)) [.label 0 [] (vals [] ++
        [.plain (.intConst .i32 ((8 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32))] ++
        expression (listBody.drop 14))]]⟩
      ⟨s₁, {}, [.frame 0 (F.setLocal ⟨1⟩ (.i32 w)) [.label 0 [] (vals [] ++
        [(Val.i32 w).toAdmin] ++ expression (listBody.drop 15))]]⟩ := by
    have hst := step_body (P := P) (host := NH) (s := s₁) (f := {}) (n := 0) (k := 0)
      (step_mid [] (expression (listBody.drop 15))
      (.memory (.loadIntVal (t := .i32) (a := .i32)
        (i := (8 : BitVec (8 * (IntType.i32.width / 8))).setWidth 32) (mem?_of hFm₁ hm₁) hld₂)))
    rw [hw] at hst
    exact hst
  have st₁₃ : Step P NH ⟨s₁, {}, [.frame 0 (F.setLocal ⟨1⟩ (.i32 w)) [.label 0 [] (vals [] ++
        [(Val.i32 w).toAdmin] ++ expression (listBody.drop 15))]]⟩
      ⟨s₁, {}, [.frame 0 ((F.setLocal ⟨1⟩ (.i32 w)).setLocal ⟨2⟩ (.i32 w)) [.label 0 [] (vals [] ++
        [] ++ expression (listBody.drop 16))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 16))
      (step_localSet (by simp [Frame.setLocal, hFl, Idx.toNat])))
  have hF₂f : ((F.setLocal ⟨1⟩ (.i32 w)).setLocal ⟨2⟩ (.i32 w)).module.funcs = [0, 1, 2, 3] :=
    hFf
  have hv₀ : ((F.setLocal ⟨1⟩ (.i32 w)).setLocal ⟨2⟩ (.i32 w)).local? ⟨0⟩ = some (some (.i32 h)) :=
    by simp [Frame.local?, Frame.setLocal, hFl, Idx.toNat]
  have hv₁ : ((F.setLocal ⟨1⟩ (.i32 w)).setLocal ⟨2⟩ (.i32 w)).local? ⟨1⟩ = some (some (.i32 w)) :=
    by simp [Frame.local?, Frame.setLocal, hFl, Idx.toNat]
  have hv₂ : ((F.setLocal ⟨1⟩ (.i32 w)).setLocal ⟨2⟩ (.i32 w)).local? ⟨2⟩ = some (some (.i32 w)) :=
    by simp [Frame.local?, Frame.setLocal, hFl, Idx.toNat]
  generalize (F.setLocal ⟨1⟩ (.i32 w)).setLocal ⟨2⟩ (.i32 w) = F₂ at st₁₃ hF₂f hv₀ hv₁ hv₂
  -- child(w, 0)
  have hs₁f := hfs s₁ hf₁
  have st₁₄ : Step P NH ⟨s₁, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [] ++
        expression (listBody.drop 16))]]⟩
      ⟨s₁, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [(Val.i32 w).toAdmin] ++
        expression (listBody.drop 17))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 17)) (step_localGet hv₁))
  have st₁₅ : Step P NH ⟨s₁, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [(Val.i32 w).toAdmin] ++
        expression (listBody.drop 17))]]⟩
      ⟨s₁, {}, (bodyCtx F₂ (expression (listBody.drop 19))).fill
        (vals [.i32 w, .i32 0] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 w, .i32 0] (expression (listBody.drop 19))
      (step_call (x := ⟨1⟩) (by rw [hF₂f]; rfl) hs₁f.2.1))
  have hd₂ : decompose? s₁ ((bodyCtx F₂ (expression (listBody.drop 19))).fill
      (vals [.i32 w, .i32 0] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F₂ (expression (listBody.drop 19)), 1, 1, [.i32 w, .i32 0]) :=
    decompose_fill _ trivial hs₁f.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have u := TSession.of_core_steps t₃ st₃.steps
  replace u := TSession.of_core_steps u st₄.steps
  replace u := TSession.of_core_steps u st₅.steps
  replace u := TSession.of_core_steps u st₆.steps
  replace u := TSession.of_core_steps u st₇.steps
  replace u := TSession.of_core_steps u st₈.steps
  replace u := TSession.of_core_steps u st₉.steps
  replace u := TSession.of_core_steps u st₁₀.steps
  replace u := TSession.of_core_steps u st₁₁.steps
  replace u := TSession.of_core_steps u st₁₂.steps
  replace u := TSession.of_core_steps u st₁₃.steps
  replace u := TSession.of_core_steps u st₁₄.steps
  replace u := TSession.of_core_steps u st₁₅.steps
  have t₄ := TSession.call u hd₂
  obtain ⟨B₂, hib₂, hW₂⟩ := written_of w hW₁.1
  let mi₂ : MemInst := { mi₁ with bytes := B₂ }
  let s₂ := s₁.setMem 0 mi₂
  have hs₂ : itemsStore w w s₁ = s₂ := by
    unfold itemsStore
    rw [hm₁, Option.bind_some, show mi₁.bytes = B₁ from rfl, hib₂]
    rfl
  obtain ⟨hm₂, hl₂, hf₂⟩ := setMem_mems (mi := mi₂) hl₁
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₂, .values []⟩) (q' := ())
    (by show _ = _; rw [← hs₂]; rfl)
  -- child(w, 0) again
  have hs₂f := hfs s₂ (hf₂.trans hf₁)
  have st₁₆ : Step P NH ⟨s₂, {}, (bodyCtx F₂ (expression (listBody.drop 19))).fill
      (Result.values []).toAdmin⟩
      ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [(Val.i32 w).toAdmin] ++
        expression (listBody.drop 20))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 20)) (step_localGet hv₂))
  have st₁₇ : Step P NH ⟨s₂, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [(Val.i32 w).toAdmin] ++
        expression (listBody.drop 20))]]⟩
      ⟨s₂, {}, (bodyCtx F₂ (expression (listBody.drop 22))).fill
        (vals [.i32 w, .i32 0] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 w, .i32 0] (expression (listBody.drop 22))
      (step_call (x := ⟨1⟩) (by rw [hF₂f]; rfl) hs₂f.2.1))
  have hd₃ : decompose? s₂ ((bodyCtx F₂ (expression (listBody.drop 22))).fill
      (vals [.i32 w, .i32 0] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F₂ (expression (listBody.drop 22)), 1, 1, [.i32 w, .i32 0]) :=
    decompose_fill _ trivial hs₂f.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₆ := TSession.call (TSession.of_core_steps t₅ (st₁₆.steps.trans st₁₇.steps)) hd₃
  obtain ⟨B₃, hib₃, hW₃⟩ := written_of w hW₂.1
  let mi₃ : MemInst := { mi₂ with bytes := B₃ }
  let s₃ := s₂.setMem 0 mi₃
  have hs₃ : itemsStore w w s₂ = s₃ := by
    unfold itemsStore
    rw [hm₂, Option.bind_some, show mi₂.bytes = B₂ from rfl, hib₃]
    rfl
  obtain ⟨-, -, hf₃⟩ := setMem_mems (mi := mi₃) hl₂
  have t₇ := TSession.answer t₆ hd₃ (a := ⟨s₃, .values []⟩) (q' := ())
    (by show _ = _; rw [← hs₃]; rfl)
  -- accept(h)
  have hs₃f := hfs s₃ ((hf₃.trans hf₂).trans hf₁)
  have st₁₈ : Step P NH ⟨s₃, {}, (bodyCtx F₂ (expression (listBody.drop 22))).fill
      (Result.values []).toAdmin⟩
      ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [(Val.i32 h).toAdmin] ++
        expression (listBody.drop 23))]]⟩ :=
    step_body (step_mid [] (expression (listBody.drop 23)) (step_localGet hv₀))
  have st₁₉ : Step P NH ⟨s₃, {}, [.frame 0 F₂ [.label 0 [] (vals [] ++ [(Val.i32 h).toAdmin] ++
        expression (listBody.drop 23))]]⟩
      ⟨s₃, {}, (bodyCtx F₂ []).fill (vals [.i32 h] ++ [.ref (.func 2), .callRefType f₂.type])⟩ :=
    step_body (step_mid [.i32 h] [] (step_call (x := ⟨2⟩) (by rw [hF₂f]; rfl) hs₃f.2.2.1))
  have hd₄ : decompose? s₃ ((bodyCtx F₂ []).fill
      (vals [.i32 h] ++ [.ref (.func 2), .callRefType f₂.type])) =
      some (bodyCtx F₂ [], 2, 2, [.i32 h]) :=
    decompose_fill _ trivial hs₃f.2.2.1 he₂ (by rw [hn₂]; rfl) hc₂
  have t₈ := TSession.call (TSession.of_core_steps t₇ (st₁₈.steps.trans st₁₉.steps)) hd₄
  -- the decoded events
  have hco₁ : calloutAt? (listMod ix) (some 0) ⟨c.store, {},
      (bodyCtx F (expression (listBody.drop 3))).fill
        (vals [.i32 h, .i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn ⟨ix.items.1, ix.items.2, .func ⟨0⟩⟩ (some 0) c.store [.i32 h, .i32 0]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? (listMod ix) (some 0) ⟨s₁, {},
      (bodyCtx F₂ (expression (listBody.drop 19))).fill
        (vals [.i32 w, .i32 0] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨ix.child.1, ix.child.2, .func ⟨0⟩⟩ (some 0) s₁ [.i32 w, .i32 0]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? (listMod ix) (some 0) ⟨s₂, {},
      (bodyCtx F₂ (expression (listBody.drop 22))).fill
        (vals [.i32 w, .i32 0] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨ix.child.1, ix.child.2, .func ⟨0⟩⟩ (some 0) s₂ [.i32 w, .i32 0]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hco₄ : calloutAt? (listMod ix) (some 0) ⟨s₃, {}, (bodyCtx F₂ []).fill
      (vals [.i32 h] ++ [.ref (.func 2), .callRefType f₂.type])⟩ =
      some (calloutIn ⟨ix.accept.1, ix.accept.2, .func ⟨1⟩⟩ (some 0) s₃ [.i32 h]) := by
    unfold calloutAt?; rw [hd₄]; rfl
  have hrd₁ : listRead ix ans (calloutIn ⟨ix.items.1, ix.items.2, .func ⟨0⟩⟩ (some 0) c.store
      [.i32 h, .i32 0]) ⟨.values [], memOf (some 0) s₁⟩ =
      some (.read (.items h) (.items [w, w])) := by
    have hm : memOf (some 0) s₁ = some B₁ := memOf_setMem hml
    simp [listRead, itemsRead, calloutIn, Val.i32, itemsAns, hm, written_itemsList hW₁,
      ListImports.toRead]
  have hrd₂ : listRead ix ans (calloutIn ⟨ix.child.1, ix.child.2, .func ⟨0⟩⟩ (some 0) s₁
      [.i32 w, .i32 0]) ⟨.values [], memOf (some 0) s₂⟩ = some (.read (.atom w) a) := by
    have hm : memOf (some 0) s₂ = some B₂ := memOf_setMem hl₁
    simp [listRead, childRead, calloutIn, Val.i32, hm, hne]
    exact hA B₂ hW₂
  have hrd₃ : listRead ix ans (calloutIn ⟨ix.child.1, ix.child.2, .func ⟨0⟩⟩ (some 0) s₂
      [.i32 w, .i32 0]) ⟨.values [], memOf (some 0) s₃⟩ = some (.read (.atom w) a) := by
    have hm : memOf (some 0) s₃ = some B₃ := memOf_setMem hl₂
    simp [listRead, childRead, calloutIn, Val.i32, hm, hne]
    exact hA B₃ hW₃
  have hna₁ : readAccept ix.toRead (calloutIn ⟨ix.items.1, ix.items.2, .func ⟨0⟩⟩ (some 0)
      c.store [.i32 h, .i32 0]) = none := by
    simp [readAccept, calloutIn, Callout.args1]
  have hna₂ : ∀ s : Store Nat, readAccept ix.toRead (calloutIn ⟨ix.child.1, ix.child.2,
      .func ⟨0⟩⟩ (some 0) s [.i32 w, .i32 0]) = none := by
    intro s
    simp [readAccept, calloutIn, Callout.args1]
  have hac : readAccept ix.toRead
      (calloutIn ⟨ix.accept.1, ix.accept.2, .func ⟨1⟩⟩ (some 0) s₃ [.i32 h]) =
      some (.accept h) := by
    simp [readAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32, ListImports.toRead]
  rw [hco₁, hco₂, hco₃, hco₄] at t₈
  refine ⟨_, ⟨mt, Is, c, hI, L, (), listEnv_reply w w _, .run, true, _,
    by rw [hmem0]; exact t₈⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, listRoles]
  rw [hna₁, hrd₁, hna₂, hrd₂, hna₂, hrd₃, hac]
  rfl

/-! ## Accepted lists -/

/-- The answers of a trace that are correct in `ρ`. -/
theorem atom_answers {ρ : Env (BitVec 32) SymStrBytesSExp} {c : BitVec 32} {x : MemAtom}
    (e : ρ c = some (.atom x)) :
    answers (sexpR MemAtom (BitVec 32)) .trap ρ (.atom c) =
      some {a | (sexpR MemAtom (BitVec 32)).ok ρ (.atom c) a} := by
  unfold answers
  split_ifs with hv
  · rfl
  · exact absurd ⟨x, e⟩ hv

/-- **`listMod ix` accepts the list of two copies of the atom `x`** read by its child reader,
when a fixed environment of `Rhos` names the list by `h` and `x` by `w`. -/
theorem listMod_live_of (P : Profile) (oa : OnInvalid) {ix : ListImports} (hok : listOk ix = true)
    (hlive : listLiveOk ix = true) {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)}
    {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)} {ρ : Env (BitVec 32) SymStrBytesSExp}
    (hρ : ρ ∈ Rhos) {h w : BitVec 32} {x : MemAtom}
    (hA : ∀ B, Written w B → ans ⟨.values [], some B⟩ 0 = .atom x)
    (e : ρ h = some (SExp.ofList [.atom x, .atom x])) (ew : ρ w = some (.atom x)) :
    SExp.ofList [.atom x, .atom x] ∈
      listReaderLang P (ReplyEnvs itemsReply) 0 (listMod ix) ix ans .trap oa Rhos := by
  have hans : answers (sexpR MemAtom (BitVec 32)) .trap ρ (.items h) =
      some {a | (sexpR MemAtom (BitVec 32)).ok ρ (.items h) a} := by
    unfold answers
    split_ifs with hv
    · rfl
    · exact absurd ⟨[.atom x, .atom x], e⟩ hv
  simp only [listReaderLang, readerLang, langOver, Host.lang]
  refine Set.mem_iUnion.2 ⟨⟨ρ, hρ⟩, Set.mem_biUnion (list_traces P hok hlive h w hA)
    ⟨_, _, .cons .enter
    (.cons (.read hans ⟨[.atom x, .atom x], e, .cons ew (.cons ew .nil)⟩)
    (.cons (.read (atom_answers ew) ew) (.cons (.read (atom_answers ew) ew)
    (.cons (.acceptOk (t := SExp.ofList [.atom x, .atom x]) e) (.nil _))))), by simp⟩⟩

/-- **`symListMod` accepts the list of two copies of the symbol of every two-byte UTF-8
text** `b₀ b₁`, when a fixed environment of `Rhos` names the list and (by `symWord b₀ b₁`) the
symbol. -/
theorem symListMod_live_of (P : Profile) (oa : OnInvalid)
    {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)} {ρ : Env (BitVec 32) SymStrBytesSExp}
    (hρ : ρ ∈ Rhos) {h : BitVec 32} {b₀ b₁ : UInt8} {str : String}
    (hu : utf8? [b₀, b₁] = some str)
    (e : ρ h = some (SExp.ofList [.atom (symOf str), .atom (symOf str)]))
    (ew : ρ (symWord b₀ b₁) = some (.atom (symOf str))) :
    SExp.ofList [.atom (symOf str), .atom (symOf str)] ∈
      listReaderLang P (ReplyEnvs itemsReply) 0 symListMod {} symTextAns .trap oa Rhos :=
  listMod_live_of P oa listOk_sym listLiveOk_sym hρ
    (fun B hW => by simp [symTextAns, written_bytesList hW, hu, symOf]) e ew

/-- **`blobListMod` accepts the list of two copies of every two-byte blob** `b₀ b₁`, when a
fixed environment of `Rhos` names the list and (by `symWord b₀ b₁`) the blob. -/
theorem blobListMod_live_of (P : Profile) (oa : OnInvalid)
    {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)} {ρ : Env (BitVec 32) SymStrBytesSExp}
    (hρ : ρ ∈ Rhos) {h : BitVec 32} {b₀ b₁ : UInt8}
    (e : ρ h = some (SExp.ofList [.atom ⟨.bytes, by decide, [b₀, b₁]⟩,
      .atom ⟨.bytes, by decide, [b₀, b₁]⟩]))
    (ew : ρ (symWord b₀ b₁) = some (.atom ⟨.bytes, by decide, [b₀, b₁]⟩)) :
    SExp.ofList [.atom ⟨.bytes, by decide, [b₀, b₁]⟩, .atom ⟨.bytes, by decide, [b₀, b₁]⟩] ∈
      listReaderLang P (ReplyEnvs itemsReply) 0 blobListMod blobImports blobAns .trap oa Rhos :=
  listMod_live_of P oa listOk_blob listLiveOk_blob hρ
    (fun B hW => by simp [blobAns, written_bytesList hW]) e ew

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck
