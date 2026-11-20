module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.AtomsLive

/-!
# Proofs: hinted atoms through linear memory

* `hinted_sat`: `hintedMod` meets the closed-writes contract `rolesClosed (hintedRoles {})
  {[hi]hi} hiReply`: the Hoare-logic proof of `hiMod` with the call `hinted(0, 2, 0, 2)`, whose
  callout sees `68 69` at `[0, 2)` both as the hint and as the octets (`hinted_of`).
* `hinted_traces`: the traced session against the counting host: `[enter, write [hi]hi q,
  accept q]`.
* `hinted_sound`, `hinted_live`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hinted

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-! ## Decoding -/

/-- The callout of `hinted(0, 2, 0, 2)` over `68 69` decodes to `[hi]hi`. -/
theorem hinted_of {o : Callout} (ha : o.args = [.i32 0, .i32 2, .i32 0, .i32 2])
    (hs : o.segment 0 2 = some [0x68, 0x69]) : Callout.hinted o = some hiHinted := by
  unfold Callout.hinted
  rw [ha]
  simp [Val.i32, hs, hiHinted]

theorem hintedWrite_hinted {o : Callout} {w : HostReply} {op : SxOp Hinted}
    {args : List (BitVec 32)} {r : BitVec 32} (hi : o.imp = ("sexp", "hinted"))
    (hh : Callout.hinted o = some hiHinted) (h : hintedWrite {} o w = some (.write op args r)) :
    op = .atom hiHinted ∧ args = [] := by
  unfold hintedWrite at h
  rcases hr : replyI32 w with _ | r'
  · simp [hr] at h
  · simp only [hr, hi, hh, Option.bind_eq_bind, Option.bind_some] at h
    simp at h
    exact ⟨h.1.symm, h.2.1⟩

theorem hintedWrite_accept {o : Callout} {w : HostReply} (hi : o.imp = ("sexp", "accept")) :
    hintedWrite {} o w = none := by
  unfold hintedWrite
  rcases replyI32 w with _ | r <;> simp [hi]

theorem hintedAccept_not_write (o : Callout) (op : SxOp Hinted) (args : List (BitVec 32))
    (r : BitVec 32) : hintedAccept {} o ≠ some (.write op args r) := by
  unfold hintedAccept
  split
  · cases Callout.args1 Callout.i32? o.args <;> simp
  · simp

/-- What a callout sees at `[0, 2)` right after the store of `68 69`. -/
theorem seg_hi {s : Store Nat} {mi : MemInst} {b : ByteArray} (hl : s.mems.length = 1)
    (hst : Memory.store mi.bytes (effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
      (count := PackSize.i16.width / 8) ((0x6968 : BitVec 32).setWidth _) = some b)
    (i : Import) (args : List Val) :
    (calloutIn i (some 0) (s.setMem 0 { mi with bytes := b }) args).segment 0 2 =
      some [0x68, 0x69] := by
  have hseg := segment_of_store hst
    (calloutIn i (some 0) (s.setMem 0 { mi with bytes := b }) args) (memOf_setMem hl)
  exact hseg.trans (by decide)

/-! ## The instantiated module -/

def hintedOk : Bool :=
  match prep hintedMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 4 f₀ && stubOk 1 1 f₁ &&
          fnOk [] hintedBody 0 0 [0, 1, 2] [0] [] f₂
       | _ => false)
  | none => false

theorem hintedOk_true : hintedOk = true := by decide +kernel

theorem hinted_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep hintedMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧ stubOk 0 4 f₀ = true ∧
      stubOk 1 1 f₁ = true ∧ fnOk [] hintedBody 0 0 [0, 1, 2] [0] [] f₂ = true := by
  have h := hintedOk_true
  unfold hintedOk at h
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
def hintedInv (s : Store Nat) : Prop :=
  ∃ c st, prep hintedMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The contract: every decoded write is closed in `{[hi]hi}`. -/
abbrev hK : MemContract HintedWEv := rolesClosed (hintedRoles {}) {.atom hiHinted} hiReply

/-! ## Every-run proof -/

theorem hinted_body {P : Profile} {c : Config Nat} {st : Option FuncIdx}
    (hp : prep hintedMod = some (c, st)) {f₀ f₁ f₂ : FuncInst Nat}
    (hf : c.store.funcs = [f₀, f₁, f₂]) (h0 : stubOk 0 4 f₀ = true) (h1 : stubOk 1 1 f₁ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2]) (hFm : F.module.mems = [0]) {s : Store Nat}
    (hs : hintedInv s) {Q : Post Nat} (hQ : BodyExits hintedInv Q) :
    HWP P (memHost hintedMod (some 0) (hintedRoles {}) hK) s F
      (vals [] ++ expression hintedBody) Q := by
  obtain ⟨c', st', hp', hsf, hml⟩ := hs
  have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
  rw [hcc, hf] at hsf
  have hs : hintedInv s := ⟨c, st, hp, by rw [hsf, hf], hml⟩
  have hinv : ∀ s', s'.funcs = s.funcs → s'.mems.length = s.mems.length → hintedInv s' :=
    fun s' h1 h2 => ⟨c, st, hp, by rw [h1, hsf, hf], by rw [h2, hml]⟩
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  unfold hintedBody
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.storePack (us := []) hFm hml ((hQ s hs F).2.2.1) fun mi b hmi hst => ?_
  obtain ⟨-, hl₁, hf₁⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 2]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 2] ++ [.i32 0]) ?_
  refine hwp_call (us := []) (args := [.i32 0, .i32 2, .i32 0, .i32 2]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := ⟨"sexp", "hinted", .func ⟨0⟩⟩) (by rw [hFf]; rfl) (by rw [hf₁, hsf]; rfl)
    hc₀ he₀ (by simp [hn₀]) rfl (fun w op args r hw =>
      let ⟨h1, h2⟩ := hintedWrite_hinted rfl (hinted_of rfl (seg_hi hml hst _ _)) hw
      closed_atom h1 h2) ?_
  rintro s' r ⟨⟨hfs', hml'⟩, hshape⟩ -
  have hs' : hintedInv s' := hinv s' (by rw [hfs', hf₁]) (by rw [hml', hl₁, hml])
  refine ⟨fun res hr => ?_, fun _ => (hQ s' hs' F).2.2.1, fun a _ => (hQ s' hs' F).2.2.2 a⟩
  obtain ⟨v, rfl⟩ := (hshape res hr).1 rfl
  refine hwp_call (us := []) (args := [.i32 v]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := ⟨"sexp", "accept", .func ⟨1⟩⟩) (by rw [hFf]; rfl) (by rw [hfs', hf₁, hsf]; rfl) hc₁
    he₁ (by simp [hn₁]) rfl (fun w op args r hw => by
      change hintedWrite {} _ w = _ at hw; rw [hintedWrite_accept rfl] at hw; cases hw) ?_
  rintro s'' r' ⟨⟨hfs'', hml''⟩, hshape'⟩ -
  have hs'' : hintedInv s'' := hinv s'' (by rw [hfs'', hfs', hf₁])
    (by rw [hml'', hml', hl₁, hml])
  refine ⟨fun res hr => ?_, fun _ => (hQ s'' hs'' F).2.2.1, fun a _ => (hQ s'' hs'' F).2.2.2 a⟩
  obtain rfl := (hshape' res hr).2 rfl
  exact X.done (hQ s'' hs'' F).1

/-- **`hintedMod` meets the closed-writes contract**, for every profile. -/
theorem hinted_sat (P : Profile) : MemSat P hintedMod 0 (hintedRoles {}) hK hintedInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := hinted_facts hp
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
    exact hinted_body hp hf h0 h1 (by simp [Frame.forCall, hfuncs])
      (by simp [Frame.forCall, hmems2]) hs hQ

/-- `hintedMod` accepts only `[hi]hi`. -/
theorem hinted_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    hintedWriterLang P (ReplyEnvs hiReply) 0 hintedMod {} pol ⊆ {.atom hiHinted} :=
  rolesLang_subset_of_closed (R := hintedRoles {}) hintedAccept_not_write (hinted_sat P)
    (fun _ _ h => h) ha hw

/-! ## The traced session -/

theorem spec_hinted : (Silmaril.Wasm.Verify.specInstance? hintedMod).isSome = true := by
  decide +kernel
theorem mem_hinted : memSizes hintedMod = [65536] := by decide +kernel

/-- **The traced session of `hintedMod`** against the counting host started at `q`. -/
theorem hinted_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write (.atom hiHinted) [] q, .accept q] ∈
      inputsOf (some .enter) '' tagTraces P (ReplyEnvs hiReply) 0 hintedMod (hintedRoles {}) := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists spec_hinted
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := hinted_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page mem_hinted hp
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
  have t₀ : TSession P L hintedMod (some 0) (hintedRoles {}) c q Is.addrs .inst false (c, q) [] :=
    .start
  have hok' : InvokeOk c.store 2 [] := ⟨f₂, ps, rs, hf2, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 2 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok'
  have st₀ : Step P NH (invoke c.store 2 [])
      ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression hintedBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[2]?.map FuncInst.type).getD default)) (vs := [])
      (a := 2) (fi := f₂) (code := code) trivial hf2 he (by rw [hps]; rfl) hcode2
    rw [hrs, hloc, hbody] at h
    exact h
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i16.width / 8) ((0x6968 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  let s₁ := c.store.setMem 0 { mi with bytes := b }
  obtain ⟨-, hl₁, hfs₁⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  have hf0' : s₁.funcs[0]? = some f₀ := by rw [hfs₁]; exact hf0
  have hf1' : s₁.funcs[1]? = some f₁ := by rw [hfs₁]; exact hf1
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression hintedBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression [.intConst .i32 0, .intConst .i32 2,
        .intConst .i32 0, .intConst .i32 2, .call ⟨0⟩, .call ⟨1⟩])]]⟩ :=
    step_body (step_mid [] _ (step_storePack hFm hmi hst))
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression [.intConst .i32 0,
      .intConst .i32 2, .intConst .i32 0, .intConst .i32 2, .call ⟨0⟩, .call ⟨1⟩])]]⟩
      ⟨s₁, {}, (bodyCtx F [.plain (.call ⟨1⟩)]).fill
        (vals [.i32 0, .i32 2, .i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 2, .i32 0, .i32 2] [.plain (.call ⟨1⟩)]
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hf0'))
  have hd₁ : decompose? s₁ ((bodyCtx F [.plain (.call ⟨1⟩)]).fill
      (vals [.i32 0, .i32 2, .i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F [.plain (.call ⟨1⟩)], 0, 0, [.i32 0, .i32 2, .i32 0, .i32 2]) :=
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
  have hco₁ : calloutAt? hintedMod (some 0) ⟨s₁, {}, (bodyCtx F [.plain (.call ⟨1⟩)]).fill
      (vals [.i32 0, .i32 2, .i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (calloutIn ⟨"sexp", "hinted", .func ⟨0⟩⟩ (some 0) s₁
        [.i32 0, .i32 2, .i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? hintedMod (some 0) ⟨s₁, {}, (bodyCtx F []).fill
      (vals [.i32 q] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (calloutIn ⟨"sexp", "accept", .func ⟨1⟩⟩ (some 0) s₁ [.i32 q]) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hh := hinted_of (o := calloutIn ⟨"sexp", "hinted", .func ⟨0⟩⟩ (some 0) s₁
    [.i32 0, .i32 2, .i32 0, .i32 2]) rfl (seg_hi hml hst _ _)
  rw [hco₁, hco₂] at t₄
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply hiOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₄⟩, ?_⟩
  have hr : replyI32 ⟨.values [.i32 q], memOf (some 0) s₁⟩ = some q := rfl
  have hw : (hintedRoles {}).answerIn (calloutIn ⟨"sexp", "hinted", .func ⟨0⟩⟩ (some 0) s₁
      [.i32 0, .i32 2, .i32 0, .i32 2]) ⟨.values [.i32 q], memOf (some 0) s₁⟩ =
      some (.write (.atom hiHinted) [] q) := by
    simp only [hintedRoles, hintedWrite, hr, hh]
    rfl
  have hn : (hintedRoles {}).callIn (calloutIn ⟨"sexp", "hinted", .func ⟨0⟩⟩ (some 0) s₁
      [.i32 0, .i32 2, .i32 0, .i32 2]) = none := by
    simp [hintedRoles, hintedAccept, calloutIn]
  have hacc : (hintedRoles {}).callIn (calloutIn ⟨"sexp", "accept", .func ⟨1⟩⟩ (some 0) s₁
      [.i32 q]) = some (.accept q) := by
    simp [hintedRoles, hintedAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32]
  simp only [Option.elim, Roles.callTags, Roles.answerTags]
  rw [show ∀ o, (hintedRoles {}).callOut o = none from fun _ => rfl,
    show ∀ o, (hintedRoles {}).callOut o = none from fun _ => rfl, hn, hw, hacc]
  rfl

/-- `hintedMod` accepts `[hi]hi`, for every policy. -/
theorem hinted_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom hiHinted ∈ hintedWriterLang P (ReplyEnvs hiReply) 0 hintedMod {} pol :=
  atom_accepts pol hiHinted (hinted_traces P (base pol))

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hinted
