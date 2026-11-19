module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn

/-!
# Proofs: `ownMod` meets the writer contract of its stateless reading

* `readVals_handle`: the payload `u32` `1` stored at `[16, 20)` is read back as the raw handle
  `1`;
* `built_res`, `built_res_none`: the stateless reading `viaRT (astW ownSig.toAstSig) rt₀` of the
  raw write `res 1` builds `res(rep)` when `1` is a live `own<0>` handle of `rt₀` with
  representation `rep`, and nothing otherwise;
* `own_sat`: in every fixed environment `ρ`, `ownMod` meets
  `roleWriterContract (witRoles (rawSig ownSig) ownRawTagOf {}) (viaRT … rt₀) none ρ (ownL rt₀)
  hiReply`: the store writes the handle `1` at `[16, 20)`, `node(0, 16, 0, 0)` reads it as the
  raw payload, the answer `r` denotes `res(rep)` (the contract of the stateless reading), and
  `accept(r)` names it.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnMod

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.IO Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Cons
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WordAtom
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region)

/-! ## Decoding and building -/

theorem readVals_handle (seg : Nat → Nat → Option (List UInt8)) :
    readVals seg [.u32] (Memory.encodeLE (IntType.i32.width / 8)
      (BitVec.setWidth (8 * (IntType.i32.width / 8)) (1 : BitVec 32)).toNat).data.toList =
      some ((1 : UInt32), ()) := by
  rfl

theorem resolveVals_res (rt₀ : RT) :
    resolveVals rt₀ [.own 0] ((1 : UInt32), ()) = (rt₀.lookup 0 1).map fun rep => (rep, ()) := by
  show (rt₀.lookup 0 (UInt32.toBitVec 1)).bind _ = _
  rw [show UInt32.toBitVec 1 = 1 from rfl]
  cases rt₀.lookup 0 1 <;> rfl

theorem movedOp_res : movedOp ownSig (rawRes 1) = [1] := rfl

/-- The raw write `res 1` resolved in `rt₀`. -/
theorem resolve_res {rt₀ : RT} {rep : Nat} (h : rt₀.lookup 0 1 = some rep) :
    resolveOp ownSig rt₀ (rawRes 1) = some (⟨OwnTag.res, (rep, ())⟩, rt₀.killAll [1]) := by
  unfold resolveOp
  simp only [movedOp_res, List.nodup_singleton, ↓reduceIte]
  show Option.map _ (resolveVals rt₀ [.own 0] ((1 : UInt32), ())) = _
  rw [resolveVals_res, h]
  rfl

theorem resolve_res_none {rt₀ : RT} (h : rt₀.lookup 0 1 = none) :
    resolveOp ownSig rt₀ (rawRes 1) = none := by
  unfold resolveOp
  simp only [movedOp_res, List.nodup_singleton, ↓reduceIte]
  show Option.map _ (resolveVals rt₀ [.own 0] ((1 : UInt32), ())) = _
  rw [resolveVals_res, h]
  rfl

theorem built_res {rt₀ : RT} {rep : Nat} (h : rt₀.lookup 0 1 = some rep)
    (ρ : Env (BitVec 32) (AST ownSig.toAstSig)) :
    (viaRT (astW ownSig.toAstSig) rt₀).built ρ (rawRes 1) [] = some (resTree rep) :=
  (Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.built_via
    (W := astW ownSig.toAstSig) (resolve_res h) ρ []).trans rfl

theorem built_res_none {rt₀ : RT} (h : rt₀.lookup 0 1 = none)
    (ρ : Env (BitVec 32) (AST ownSig.toAstSig)) :
    (viaRT (astW ownSig.toAstSig) rt₀).built ρ (rawRes 1) [] = none :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwn.built_via_none (resolve_res_none h) ρ []

/-! ## The instantiated module -/

/-- The shape of the instantiated module. -/
def ownOk : Bool :=
  match prep ownMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 4 f₀ && stubOk 1 1 f₁ &&
          fnOk [.i32, .i32] ownBody 0 0 [0, 1, 2] [0] calcD f₂
       | _ => false)
  | none => false

theorem ownOk_true : ownOk = true := by decide +kernel

theorem own_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep ownMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧
      stubOk 0 4 f₀ = true ∧ stubOk 1 1 f₁ = true ∧
      fnOk [.i32, .i32] ownBody 0 0 [0, 1, 2] [0] calcD f₂ = true := by
  have h := ownOk_true
  unfold ownOk at h
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
def ownInv (s : Store Nat) : Prop :=
  ∃ c st, prep ownMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The roles of the example: the raw signature. -/
abbrev ownRoles : Roles Unit (WitWEv (rawSig ownSig)) Unit Unit := witRoles (rawSig ownSig) ownRawTagOf {}

/-- The writer contract of the stateless reading in `rt₀`, in the fixed environment `ρ`. -/
abbrev ownK (rt₀ : RT) (ρ : Env (BitVec 32) (AST ownSig.toAstSig)) :
    MemContract (WitWEv (rawSig ownSig)) :=
  roleWriterContract ownRoles (viaRT (astW ownSig.toAstSig) rt₀) none ρ (ownL rt₀) hiReply

theorem pre_other {rt₀ : RT} {ρ : Env (BitVec 32) (AST ownSig.toAstSig)} {i : Import}
    {s : Store Nat} {args : List Val} (hi : (i.moduleName, i.name) ≠ ("wit", "accept")) :
    (ownK rt₀ ρ).pre (calloutIn i (some 0) s args) := by
  intro h hd
  change witAccept (rawSig ownSig) {} _ = _ at hd
  rw [witAccept_eq_none hi] at hd
  cases hd

/-! ## Every-run proof -/

/-- **The body of `run`**, in the fixed environment `ρ`. -/
theorem own_body {P : Profile} {rt₀ : RT} {ρ : Env (BitVec 32) (AST ownSig.toAstSig)}
    {f₀ f₁ : FuncInst Nat} (h0 : stubOk 0 4 f₀ = true) (h1 : stubOk 1 1 f₁ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2]) (hFm : F.module.mems = [0])
    {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁] ++ fs.drop 2) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → ownInv s') {Q : Post Nat}
    (hQ : BodyExits ownInv Q) :
    HWP P (memHost ownMod (some 0) ownRoles (ownK rt₀ ρ)) s F
      (vals [] ++ expression ownBody) Q := by
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  have hf0 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[0]? = some f₀ := fun s' h => by
    rw [h, hfs]; rfl
  have hf1 : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[1]? = some f₁ := fun s' h => by
    rw [h, hfs]; rfl
  have htrap : ∀ s' (F' : Frame), s'.funcs = fs → s'.mems.length = 1 → Q s' F' .trap :=
    fun s' F' h h' => (hQ s' (hinv s' h h') F').2.2.1
  have hthrow : ∀ s' (F' : Frame) a, s'.funcs = fs → s'.mems.length = 1 → Q s' F' (.throw a) :=
    fun s' F' a h h' => (hQ s' (hinv s' h h') F').2.2.2 a
  unfold ownBody
  -- the handle `1` at 16
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 16]) ?_
  refine X.store32 (us := []) hFm hml (htrap s F hsf hml) fun mi₀ b₀ hmi₀ hst₀ => ?_
  obtain ⟨-, hl₁, hf₁⟩ := setMem_mems (mi := { mi₀ with bytes := b₀ }) hml
  -- node(0, 16, 0, 0)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16] ++ [.i32 0]) ?_
  have hd₁ : Callout.witNode (rawSig ownSig) ownRawTagOf (calloutIn impNode (some 0)
      (s.setMem 0 { mi₀ with bytes := b₀ }) [.i32 0, .i32 16, .i32 0, .i32 0]) =
      some (rawRes 1, []) :=
    witNode_eq rfl rfl (segment_of_store hst₀ _ (memOf_setMem hml)) (readVals_handle _)
      (segment_nil (memOf_setMem hml) 0 (Nat.zero_le _)) rfl rfl
  refine hwp_call (us := []) (args := [.i32 0, .i32 16, .i32 0, .i32 0]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := impNode) (by rw [hFf]; rfl) (hf0 _ (hf₁.trans hsf)) hc₀ he₀ (by simp [hn₀])
    rfl (pre_other (by decide)) ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ hans
  have hfs₂' : s₂.funcs = fs := hfs₂.trans (hf₁.trans hsf)
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hl₁
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F hfs₂' hml₂',
    fun a _ => hthrow s₂ F a hfs₂' hml₂'⟩
  obtain ⟨r₁, rfl⟩ := (hshape res hr).1 rfl
  subst hr
  have hρ₁ : ∀ t, ρ r₁ = some t → t ∈ ownL rt₀ := by
    intro t hρ
    rcases hans _ (witWrite_eq rfl hd₁ rfl) _ _ _ rfl with h | ⟨t', ht, hρ'⟩
    · cases h
    · rw [hρ] at hρ'
      cases hρ'
      rcases hl : rt₀.lookup 0 1 with _ | rep
      · cases (built_res_none hl ρ).symm.trans ht
      · cases (built_res hl ρ).symm.trans ht
        exact ⟨rep, hl, rfl⟩
  -- accept(r₁)
  refine hwp_call (us := []) (args := [.i32 r₁]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := WitAst.impAcc) (by rw [hFf]; rfl) (hf1 _ hfs₂') hc₁ he₁ (by simp [hn₁]) rfl ?_ ?_
  · intro h hd t ht
    simp [ownRoles, witRoles, witAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32] at hd
    subst hd
    exact hρ₁ t ht
  rintro s₈ r ⟨⟨hfs₈, hml₈⟩, hshape⟩ -
  have hfs₈' : s₈.funcs = fs := hfs₈.trans hfs₂'
  have hml₈' : s₈.mems.length = 1 := hml₈.trans hml₂'
  refine ⟨fun res hr => ?_, fun _ => htrap s₈ _ hfs₈' hml₈',
    fun a _ => hthrow s₈ _ a hfs₈' hml₈'⟩
  obtain rfl := (hshape res hr).2 rfl
  exact X.done (hQ s₈ (hinv s₈ hfs₈' hml₈') _).1

/-- **`ownMod` meets the writer contract of its stateless reading** in every table and fixed
environment, for every profile. -/
theorem own_sat (P : Profile) (rt₀ : RT) (ρ : Env (BitVec 32) (AST ownSig.toAstSig)) :
    MemSat P ownMod 0 ownRoles (ownK rt₀ ρ) ownInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := own_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 2 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, -⟩ := fnOk_spec h2
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → ownInv s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, ownInv s → s.funcs = c.store.funcs := by
    rintro s ⟨c', st', hp', hfs, _⟩
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc]
  refine export_valid (fi := f₂) (fun s hs => by rw [hfi s hs, hf]; rfl) hcode2 he hrs ?_
  intro s args hs hok Q hQ
  have hargs : args = [] := by
    have := args_length (by rw [hfi s hs, hf]; rfl) he hok
    rw [hps] at this
    exact List.eq_nil_of_length_eq_zero this
  subst hargs
  rw [hbody, hloc]
  have hml' : s.mems.length = 1 := by obtain ⟨_, _, _, _, h⟩ := hs; exact h
  exact own_body h0 h1 (by simp [Frame.forCall, hfuncs]) (by simp [Frame.forCall, hmems2])
    (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs) hml' hinv hQ

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnMod
