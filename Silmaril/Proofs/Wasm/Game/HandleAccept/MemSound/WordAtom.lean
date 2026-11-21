module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.AtomsLive

/-!
# Proofs: word atoms through linear memory

* `X.i64Const`, `X.store64`, `step_store64`: the every-run and step rules of `i64.const` and of a
  full-width `i64` store to memory `0`;
* `word_sat`: `wordMod` meets the closed-writes contract `rolesClosed (wordRoles {}) {42}
  hiReply`: its call `word(0)` sees the eight bytes of `42` at `[0, 8)` (`seg_42`, `word_of`);
* `word_traces`: the traced session against the counting host: `[enter, write 42 q, accept q]`;
* `word_sound`, `word_live`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WordAtom

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms
  Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-! ## Rules for the `i64` store -/

section Rules

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {F : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

theorem X.i64Const {c : BitVec 64}
    (h : HWP P host s F (vals (us ++ [.i64 c]) ++ expression is) Q) :
    HWP P host s F (vals us ++ expression (.intConst .i64 c :: is)) Q := by
  simpa [vals, expression, Val.i64, Val.toAdmin] using h

/-- A full-width `i64` store to memory `0` of a store with one memory. -/
theorem X.store64 {addr : BitVec 32} {v : BitVec 64} (hF : F.module.mems = [0])
    (hl : s.mems.length = 1) (htrap : Q s F .trap)
    (h : ∀ mi b, s.mems[0]? = some mi →
      Memory.store mi.bytes (effAddr addr.toNat ⟨0, 0⟩) (count := IntType.i64.width / 8)
        (v.setWidth _) = some b →
      HWP P host (s.setMem 0 { mi with bytes := b }) F (vals us ++ expression is) Q) :
    HWP P host s F (vals (us ++ [.i32 addr, .i64 v]) ++
      expression (.intStore .i64 none ⟨0⟩ ⟨0, 0⟩ :: is)) Q := by
  obtain ⟨mi, hmi⟩ : ∃ mi, s.mems[0]? = some mi :=
    ⟨s.mems[0]'(by omega), List.getElem?_eq_getElem _⟩
  have hm := mem?_of hF hmi
  rcases hst : Memory.store mi.bytes (effAddr addr.toNat ⟨0, 0⟩)
    (count := IntType.i64.width / 8) (v.setWidth _) with _ | b
  · exact Wp.intStore_oob (m := .part) (a := .i32) (i := addr) (t := .i64) (c := v)
      hm (store_none_lt hst) htrap
  · exact Wp.intStore (m := .part) (a := .i32) (i := addr) (t := .i64) (c := v) hm hst
      (h mi b hmi hst)

/-- A full-width `i64` store to memory `0`. -/
theorem step_store64 {a : BitVec 32} {v : BitVec 64} {mi : MemInst} {b : ByteArray}
    (hF : F.module.mems = [0]) (hmi : s.mems[0]? = some mi)
    (hst : Memory.store mi.bytes (effAddr a.toNat ⟨0, 0⟩) (count := IntType.i64.width / 8)
      (v.setWidth _) = some b) :
    Step P host ⟨s, F, [.plain (.intConst .i32 a), .plain (.intConst .i64 v),
      .plain (.intStore .i64 none ⟨0⟩ ⟨0, 0⟩)]⟩ ⟨s.setMem 0 { mi with bytes := b }, F, []⟩ :=
  .memory (.storeIntVal (a := .i32) (i := a) (t := .i64) (c := v) (mem?_of hF hmi) hst)

end Rules

/-! ## Decoding -/

/-- The callout of `word(0)` over the bytes of `42` decodes to `42`. -/
theorem word_of {o : Callout} (ha : o.args = [.i32 0])
    (hs : o.segment 0 8 = some (Memory.encodeLE 8 42).data.toList) :
    Callout.word64 o = some 42 := by
  unfold Callout.word64
  rw [ha]
  simp only [Callout.args1, Callout.i32?, Val.i32, Option.bind_eq_bind, Option.bind_some]
  rw [show (0 : BitVec 32).toNat = 0 from rfl, hs]
  decide

theorem wordWrite_word {o : Callout} {w : HostReply} {op : SxOp (BitVec 64)}
    {args : List (BitVec 32)} {r : BitVec 32} (hi : o.imp = ("sexp", "word"))
    (hh : Callout.word64 o = some 42) (h : wordWrite {} o w = some (.write op args r)) :
    op = .atom 42 ∧ args = [] := by
  unfold wordWrite at h
  rcases hr : replyI32 w with _ | r'
  · simp [hr] at h
  · simp only [hr, hi, hh, Option.bind_eq_bind, Option.bind_some] at h
    simp at h
    exact ⟨h.1.symm, h.2.1⟩

theorem wordWrite_accept {o : Callout} {w : HostReply} (hi : o.imp = ("sexp", "accept")) :
    wordWrite {} o w = none := by
  unfold wordWrite
  rcases replyI32 w with _ | r <;> simp [hi]

theorem wordAccept_not_write (o : Callout) (op : SxOp (BitVec 64)) (args : List (BitVec 32))
    (r : BitVec 32) : wordAccept {} o ≠ some (.write op args r) := by
  unfold wordAccept
  split
  · cases Callout.args1 Callout.i32? o.args <;> simp
  · simp

/-- What a callout sees at `[0, 8)` right after the store of `42`. -/
theorem seg_42 {s : Store Nat} {mi : MemInst} {b : ByteArray} (hl : s.mems.length = 1)
    (hst : Memory.store mi.bytes (effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
      (count := IntType.i64.width / 8) ((42 : BitVec 64).setWidth _) = some b)
    (i : Import) (args : List Val) :
    (calloutIn i (some 0) (s.setMem 0 { mi with bytes := b }) args).segment 0 8 =
      some (Memory.encodeLE 8 42).data.toList :=
  segment_of_store hst
    (calloutIn i (some 0) (s.setMem 0 { mi with bytes := b }) args) (memOf_setMem hl)

/-! ## The instantiated module -/

def wordOk : Bool :=
  match prep wordMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 1 f₀ && stubOk 1 1 f₁ &&
          fnOk [] wordBody 0 0 [0, 1, 2] [0] [] f₂
       | _ => false)
  | none => false

theorem wordOk_true : wordOk = true := by decide +kernel

theorem word_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep wordMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧ stubOk 0 1 f₀ = true ∧
      stubOk 1 1 f₁ = true ∧ fnOk [] wordBody 0 0 [0, 1, 2] [0] [] f₂ = true := by
  have h := wordOk_true
  unfold wordOk at h
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

/-- The store invariant: the instantiated functions and one memory. -/
def wordInv (s : Store Nat) : Prop :=
  ∃ c st, prep wordMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The contract: every decoded write is closed in `{42}`. -/
abbrev hK : MemContract WordWEv := rolesClosed (wordRoles {}) {.atom (42 : BitVec 64)} hiReply

/-! ## Every-run proof -/

theorem word_body {P : Profile} {c : Config Nat} {st : Option FuncIdx}
    (hp : prep wordMod = some (c, st)) {f₀ f₁ f₂ : FuncInst Nat}
    (hf : c.store.funcs = [f₀, f₁, f₂]) (h0 : stubOk 0 1 f₀ = true) (h1 : stubOk 1 1 f₁ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2]) (hFm : F.module.mems = [0]) {s : Store Nat}
    (hs : wordInv s) {Q : Post Nat} (hQ : BodyExits wordInv Q) :
    HWP P (memHost wordMod (some 0) (wordRoles {}) hK) s F
      (vals [] ++ expression wordBody) Q := by
  obtain ⟨c', st', hp', hsf, hml⟩ := hs
  have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
  rw [hcc, hf] at hsf
  have hs : wordInv s := ⟨c, st, hp, by rw [hsf, hf], hml⟩
  have hinv : ∀ s', s'.funcs = s.funcs → s'.mems.length = s.mems.length → wordInv s' :=
    fun s' h1 h2 => ⟨c, st, hp, by rw [h1, hsf, hf], by rw [h2, hml]⟩
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  unfold wordBody
  refine X.i32Const (us := []) ?_
  refine X.i64Const (us := [] ++ [.i32 0]) ?_
  refine X.store64 (us := []) hFm hml ((hQ s hs F).2.2.1) fun mi b hmi hst => ?_
  obtain ⟨-, hl₁, hf₁⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  refine X.i32Const (us := []) ?_
  refine hwp_call (us := []) (args := [.i32 0]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := ⟨"sexp", "word", .func ⟨0⟩⟩) (by rw [hFf]; rfl) (by rw [hf₁, hsf]; rfl)
    hc₀ he₀ (by simp [hn₀]) rfl (fun w op args r hw =>
      let ⟨h1, h2⟩ := wordWrite_word rfl (word_of rfl (seg_42 hml hst _ _)) hw
      closed_atom h1 h2) ?_
  rintro s' r ⟨⟨hfs', hml'⟩, hshape⟩ -
  have hs' : wordInv s' := hinv s' (by rw [hfs', hf₁]) (by rw [hml', hl₁, hml])
  refine ⟨fun res hr => ?_, fun _ => (hQ s' hs' F).2.2.1, fun a _ => (hQ s' hs' F).2.2.2 a⟩
  obtain ⟨v, rfl⟩ := (hshape res hr).1 rfl
  refine hwp_call (us := []) (args := [.i32 v]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := ⟨"sexp", "accept", .func ⟨1⟩⟩) (by rw [hFf]; rfl) (by rw [hfs', hf₁, hsf]; rfl) hc₁
    he₁ (by simp [hn₁]) rfl (fun w op args r hw => by
      change wordWrite {} _ w = _ at hw; rw [wordWrite_accept rfl] at hw; cases hw) ?_
  rintro s'' r' ⟨⟨hfs'', hml''⟩, hshape'⟩ -
  have hs'' : wordInv s'' := hinv s'' (by rw [hfs'', hfs', hf₁])
    (by rw [hml'', hml', hl₁, hml])
  refine ⟨fun res hr => ?_, fun _ => (hQ s'' hs'' F).2.2.1, fun a _ => (hQ s'' hs'' F).2.2.2 a⟩
  obtain rfl := (hshape' res hr).2 rfl
  exact X.done (hQ s'' hs'' F).1

/-- **`wordMod` meets the closed-writes contract**, for every profile. -/
theorem word_sat (P : Profile) : MemSat P wordMod 0 (wordRoles {}) hK wordInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := word_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 2 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, -, hrs, hfuncs, hmems2, -⟩ := fnOk_spec h2
  refine export_valid (fi := f₂) (fun s hs => ?_) hcode2 he hrs ?_
  · obtain ⟨c', st', hp', hfs, _⟩ := hs
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc, hf]
    rfl
  · intro s args hs _ Q hQ
    rw [hbody]
    exact word_body hp hf h0 h1 (by simp [Frame.forCall, hfuncs])
      (by simp [Frame.forCall, hmems2]) hs hQ

/-- `wordMod` accepts only the word `42`. -/
theorem word_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    wordWriterLang P (ReplyEnvs hiReply) 0 wordMod {} pol ⊆ {.atom (42 : BitVec 64)} :=
  rolesLang_subset_of_closed (R := wordRoles {}) wordAccept_not_write (word_sat P)
    (fun _ _ h => h) ha hw

/-! ## The traced session -/

theorem spec_word : (Silmaril.Wasm.Verify.specInstance? wordMod).isSome = true := by
  decide +kernel
theorem mem_word : memSizes wordMod = [65536] := by decide +kernel

/-- **The traced session of `wordMod`** against the counting host started at `q`. -/
theorem word_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write (.atom (42 : BitVec 64)) [] q, .accept q] ∈
      inputsOf (some .enter) '' tagTraces P (ReplyEnvs hiReply) 0 wordMod (wordRoles {}) := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists spec_word
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := word_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page mem_word hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, -⟩ := fnOk_spec h2
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hf0 : c.store.funcs[0]? = some f₀ := by rw [hf]; rfl
  have hf1 : c.store.funcs[1]? = some f₁ := by rw [hf]; rfl
  have hf2 : c.store.funcs[2]? = some f₂ := by rw [hf]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  let F : Frame := Frame.forCall f₂.module [] []
  have hFf : F.module.funcs = [0, 1, 2] := by simp [F, Frame.forCall, hfuncs]
  have hFm : F.module.mems = [0] := by simp [F, Frame.forCall, hmems2]
  let L := countEnv hiOut
  have t₀ : TSession P L wordMod (some 0) (wordRoles {}) c q Is.addrs .inst false (c, q) [] :=
    .start
  have hok' : InvokeOk c.store 2 [] := ⟨f₂, ps, rs, hf2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 2 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok'
  have st₀ : Step P NH (invoke c.store 2 [])
      ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression wordBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[2]?.map FuncInst.type).getD default)) (vs := [])
      (a := 2) (fi := f₂) (code := code) trivial hf2 he (by rw [hps]; rfl) hcode2
    rw [hrs, hloc, hbody] at h
    exact h
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := IntType.i64.width / 8) ((42 : BitVec 64).setWidth _) (by rw [hsize]; decide)
  let s₁ := c.store.setMem 0 { mi with bytes := b }
  obtain ⟨-, hl₁, hfs₁⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  have hf0' : s₁.funcs[0]? = some f₀ := by rw [hfs₁]; exact hf0
  have hf1' : s₁.funcs[1]? = some f₁ := by rw [hfs₁]; exact hf1
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression wordBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression [.intConst .i32 0, .call ⟨0⟩,
        .call ⟨1⟩])]]⟩ :=
    step_body (step_mid [] _ (step_store64 hFm hmi hst))
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression [.intConst .i32 0,
      .call ⟨0⟩, .call ⟨1⟩])]]⟩
      ⟨s₁, {}, (bodyCtx F [.plain (.call ⟨1⟩)]).fill
        (vals [.i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0] [.plain (.call ⟨1⟩)]
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hf0'))
  have hd₁ : decompose? s₁ ((bodyCtx F [.plain (.call ⟨1⟩)]).fill
      (vals [.i32 0] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F [.plain (.call ⟨1⟩)], 0, 0, [.i32 0]) :=
    decompose_fill _ trivial hf0' he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F [.plain (.call ⟨1⟩)]).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, (bodyCtx F []).fill (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 q] [] (step_call (x := ⟨1⟩) (by rw [hFf]; rfl) hf1'))
  have hd₂ : decompose? s₁ ((bodyCtx F []).fill
      (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (bodyCtx F [], 1, 1, [.i32 q]) :=
    decompose_fill _ trivial hf1' he₁ (by rw [hn₁]; rfl) hc₁
  have t₄ := TSession.call (TSession.of_core_steps t₃ st₃.steps) hd₂
  have hco₁ : calloutAt? wordMod (some 0) ⟨s₁, {}, (bodyCtx F [.plain (.call ⟨1⟩)]).fill
      (vals [.i32 0] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn ⟨"sexp", "word", .func ⟨0⟩⟩ (some 0) s₁
        [.i32 0]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? wordMod (some 0) ⟨s₁, {}, (bodyCtx F []).fill
      (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨"sexp", "accept", .func ⟨1⟩⟩ (some 0) s₁ [.i32 q]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hh := word_of (o := calloutIn ⟨"sexp", "word", .func ⟨0⟩⟩ (some 0) s₁
    [.i32 0]) rfl (seg_42 hml hst _ _)
  rw [hco₁, hco₂] at t₄
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply hiOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₄⟩, ?_⟩
  have hr : replyI32 ⟨.values [.i32 q], memOf (some 0) s₁⟩ = some q := rfl
  have hw : (wordRoles {}).answerIn (calloutIn ⟨"sexp", "word", .func ⟨0⟩⟩ (some 0) s₁
      [.i32 0]) ⟨.values [.i32 q], memOf (some 0) s₁⟩ =
      some (.write (.atom (42 : BitVec 64)) [] q) := by
    simp only [wordRoles, wordWrite, hr, hh]
    rfl
  have hn : (wordRoles {}).callIn (calloutIn ⟨"sexp", "word", .func ⟨0⟩⟩ (some 0) s₁
      [.i32 0]) = none := by
    simp [wordRoles, wordAccept, calloutIn]
  have hacc : (wordRoles {}).callIn (calloutIn ⟨"sexp", "accept", .func ⟨1⟩⟩ (some 0) s₁
      [.i32 q]) = some (.accept q) := by
    simp [wordRoles, wordAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  simp only [Option.elim, Roles.callTags, Roles.answerTags]
  rw [show ∀ o, (wordRoles {}).callOut o = none from fun _ => rfl,
    show ∀ o, (wordRoles {}).callOut o = none from fun _ => rfl, hn, hw, hacc]
  rfl

/-- `wordMod` accepts the word `42`, for every policy. -/
theorem word_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom (42 : BitVec 64) ∈ wordWriterLang P (ReplyEnvs hiReply) 0 wordMod {} pol :=
  atom_accepts pol (42 : BitVec 64) (word_traces P (base pol))

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WordAtom
