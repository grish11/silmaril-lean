module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WordAtom
import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# Proofs: typed payloads and fixed arities through linear memory

* Decoding: `witAccept_isAccept`, `witWrite_isWrite` (so the generic bridges apply),
  `witWrite_admits` (**a decoded write always has an admitted number of children**),
  `witWrite_none` (a call the decoder rejects has no write event),
  `witNode_eq`, `witWrite_eq`; the payloads `readVals_one`, `readVals_two` of the example and the
  two child handles `children_pair`.
* `calc_sat`: in a fixed environment `ρ` (no sentinel), `calcMod` meets the writer contract
  `roleWriterContract (witRoles calcSig calcTagOf {}) (astW calcSig.toAstSig) none ρ {addTree}
  hiReply`: the first `node(0, 16, 0, 0)` reads the `s64` `1` stored at `[16, 24)` right before
  it (handle `r₁` denotes `num 1`), the second reads `2` (handle `r₂`, `num 2`); the module
  stores `r₁`, `r₂` at `[0, 8)` and `node(1, 0, 0, 2)` reads no payload and the two child
  handles, so its handle denotes `add(num 1, num 2)`, which `accept` names.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.IO Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Cons
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ast
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WordAtom Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt Region)

/-! ## The decoder -/

section Decoder

variable {S : WitSig} {tagOf : BitVec 32 → Option S.Tag}

theorem witAccept_isAccept {ix : WitImports} {o : Callout} {e : WitWEv S}
    (h : witAccept S ix o = some e) : ∃ h, e = .accept h := by
  unfold witAccept at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨h, -, rfl⟩ := h
    exact ⟨h, rfl⟩
  · cases h

theorem witWrite_isWrite {ix : WitImports} {o : Callout} {w : HostReply} {e : WitWEv S}
    (h : witWrite S tagOf ix o w = some e) : ∃ op args r, e = .write op args r := by
  unfold witWrite at h
  rcases hr : replyI32 w with _ | r
  · simp [hr] at h
  · simp only [hr] at h
    split_ifs at h
    · rcases ht : Callout.witNode S tagOf o with _ | ⟨op, hs⟩
      · simp [ht] at h
      · simp only [ht, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq] at h
        exact ⟨_, _, _, h.symm⟩
    · simp at h

/-- **The decoder admits only the declared arities.** -/
theorem witNode_admits {o : Callout} {op : Σ t, S.toAstSig.Arg t} {hs : List (BitVec 32)}
    (h : Callout.witNode S tagOf o = some (op, hs)) : (S.arity op.1).Admits hs.length = true := by
  unfold Callout.witNode at h
  split at h
  · obtain ⟨t, -, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨bs, -, a, -, cs, -, hs', -, h⟩ := h
      split at h
      · rename_i hadm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hadm
      · cases h
    · cases h
  · cases h

/-- **A decoded write has an admitted number of children.** -/
theorem witWrite_admits {ix : WitImports} {o : Callout} {w : HostReply}
    {op : Σ t, S.toAstSig.Arg t} {hs : List (BitVec 32)} {r : BitVec 32}
    (h : witWrite S tagOf ix o w = some (.write op hs r)) :
    (S.arity op.1).Admits hs.length = true := by
  unfold witWrite at h
  rcases hr : replyI32 w with _ | r'
  · simp [hr] at h
  · simp only [hr] at h
    split_ifs at h
    · rcases ht : Callout.witNode S tagOf o with _ | ⟨op', hs'⟩
      · simp [ht] at h
      · simp only [ht, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq, WEv.write.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact witNode_admits ht
    · simp at h

/-- **A call the decoder rejects has no write event**, whatever its answer. -/
theorem witWrite_none {ix : WitImports} {o : Callout} {w : HostReply}
    (h : Callout.witNode S tagOf o = none) : witWrite S tagOf ix o w = none := by
  unfold witWrite
  rcases replyI32 w with _ | r <;> simp [h]

theorem witAccept_eq_none {o : Callout} (h : o.imp ≠ ("wit", "accept")) :
    witAccept S {} o = none := by
  simp [witAccept, h]

theorem witNode_eq {o : Callout} {tg pp cp n : BitVec 32} {t : S.Tag} {bs cs : List UInt8}
    {a : S.toAstSig.Arg t} {hs : List (BitVec 32)}
    (ha : o.args = [.i32 tg, .i32 pp, .i32 cp, .i32 n]) (ht : tagOf tg = some t)
    (h1 : o.segment pp.toNat (valsWidth (S.params t)) = some bs)
    (h2 : readVals o.segment (S.params t) bs = some a) (h3 : o.segment cp.toNat (4 * n.toNat) = some cs)
    (h4 : le32s cs = some hs) (h5 : (S.arity t).Admits hs.length = true)
    (hal : pp.toNat % valsAlign (S.params t) = 0 ∧ cp.toNat % 4 = 0 := by decide)
    (hshape : checkPTys .memoryOnly (S.params t) = .ok () := by rfl) :
    Callout.witNode S tagOf o = some (⟨t, a⟩, hs) := by
  unfold Callout.witNode
  rw [ha]
  simp only [Val.i32]
  refine Option.bind_eq_some_iff.2 ⟨t, ht, ?_⟩
  split
  swap
  · rename_i rejected
    exact (rejected ⟨hal.1, hal.2, by rw [hshape]; rfl⟩).elim
  refine Option.bind_eq_some_iff.2 ⟨bs, h1, ?_⟩
  refine Option.bind_eq_some_iff.2 ⟨a, h2, ?_⟩
  refine Option.bind_eq_some_iff.2 ⟨cs, h3, ?_⟩
  refine Option.bind_eq_some_iff.2 ⟨hs, h4, ?_⟩
  simp only [h5, ↓reduceIte]

theorem witWrite_eq {o : Callout} {w : HostReply} {op : Σ t, S.toAstSig.Arg t}
    {hs : List (BitVec 32)} {r : BitVec 32} (hi : o.imp = ("wit", "node"))
    (ht : Callout.witNode S tagOf o = some (op, hs)) (hr : replyI32 w = some r) :
    witWrite S tagOf {} o w = some (.write op hs r) := by
  simp [witWrite, hr, hi, ht]

end Decoder

/-! ## Memory facts of the example -/

theorem readVals_one (seg : Nat → Nat → Option (List UInt8)) :
    readVals seg [.s64] (Memory.encodeLE (IntType.i64.width / 8)
      (BitVec.setWidth (8 * (IntType.i64.width / 8)) (1 : BitVec 64)).toNat).data.toList =
      some ((1 : Int64), ()) := by
  kernel_rfl

theorem readVals_two (seg : Nat → Nat → Option (List UInt8)) :
    readVals seg [.s64] (Memory.encodeLE (IntType.i64.width / 8)
      (BitVec.setWidth (8 * (IntType.i64.width / 8)) (2 : BitVec 64)).toNat).data.toList =
      some ((2 : Int64), ()) := by
  kernel_rfl

/-- What `node(_, _, 0, 2)` observes when the memory holds two handles at `0` and `4`. -/
theorem children_pair {o : Callout} {b : ByteArray} {r₁ r₂ : BitVec 32} (hmem : o.mem = some b)
    (h8 : 8 ≤ b.size) (h₀ : bytesAt b ⟨0, 4⟩ = (Memory.encodeLE 4 r₁.toNat).data.toList)
    (h₄ : bytesAt b ⟨4, 4⟩ = (Memory.encodeLE 4 r₂.toNat).data.toList) :
    ∃ cs, o.segment (0 : BitVec 32).toNat (4 * (2 : BitVec 32).toNat) = some cs ∧
      le32s cs = some [r₁, r₂] := by
  refine ⟨_, segment_of_bytesAt hmem (a := 0) (n := 4 + 4) h8
    (by rw [bytesAt_append, h₀, h₄]), ?_⟩
  rw [le32s_encode, ← List.append_nil (Memory.encodeLE 4 r₂.toNat).data.toList, le32s_encode]
  rfl

/-! ## The instantiated module -/

/-- The default values of the locals. -/
def calcD : List (Option Val) := [some (.i32 0), some (.i32 0)]

/-- The shape of the instantiated module. -/
def calcOk : Bool :=
  match prep calcMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 4 f₀ && stubOk 1 1 f₁ &&
          fnOk [.i32, .i32] calcBody 0 0 [0, 1, 2] [0] calcD f₂
       | _ => false)
  | none => false

theorem calcOk_true : calcOk = true := by decide +kernel

theorem calc_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep calcMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧
      stubOk 0 4 f₀ = true ∧ stubOk 1 1 f₁ = true ∧
      fnOk [.i32, .i32] calcBody 0 0 [0, 1, 2] [0] calcD f₂ = true := by
  have h := calcOk_true
  unfold calcOk at h
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
def calcInv (s : Store Nat) : Prop :=
  ∃ c st, prep calcMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The roles of the example. -/
abbrev calcRoles : Roles Unit (WitWEv calcSig) Unit Unit := witRoles calcSig calcTagOf {}

/-- The writer contract in the fixed environment `ρ`. -/
abbrev calcK (ρ : Env (BitVec 32) (AST calcSig.toAstSig)) : MemContract (WitWEv calcSig) :=
  roleWriterContract calcRoles (astW calcSig.toAstSig) none ρ {addTree} hiReply

/-- The import `node`. -/
abbrev impNode : Import := ⟨"wit", "node", .func ⟨0⟩⟩
/-- The import `accept`. -/
abbrev impAcc : Import := ⟨"wit", "accept", .func ⟨1⟩⟩

/-- Calls of other imports than `accept` are always allowed. -/
theorem pre_other {ρ : Env (BitVec 32) (AST calcSig.toAstSig)} {i : Import} {s : Store Nat}
    {args : List Val} (hi : (i.moduleName, i.name) ≠ ("wit", "accept")) :
    (calcK ρ).pre (calloutIn i (some 0) s args) := by
  intro h hd
  change witAccept calcSig {} _ = _ at hd
  rw [witAccept_eq_none hi] at hd
  cases hd

/-- `num k` from its payload. -/
theorem built_num (ρ : Env (BitVec 32) (AST calcSig.toAstSig)) (k : Int64) :
    (astW calcSig.toAstSig).built ρ ⟨CalcTag.num, (k, ())⟩ [] = some (numTree k) := rfl

/-- `add(x, y)` from the handles of `x` and `y`. -/
theorem built_add {ρ : Env (BitVec 32) (AST calcSig.toAstSig)} {r₁ r₂ : BitVec 32}
    {x y : AST calcSig.toAstSig} (h₁ : ρ r₁ = some x) (h₂ : ρ r₂ = some y) :
    (astW calcSig.toAstSig).built ρ ⟨CalcTag.add, ()⟩ [r₁, r₂] =
      some (AST.node (S := calcSig.toAstSig) CalcTag.add () [x, y]) := by
  unfold Writer.built Env.lookupAll
  rw [List.mapM_cons, List.mapM_cons, List.mapM_nil, h₁, h₂]
  rfl

/-! ## Every-run proof -/

/-- **The body of `run`**, in the fixed environment `ρ`. -/
theorem calc_body {P : Profile} {ρ : Env (BitVec 32) (AST calcSig.toAstSig)}
    {f₀ f₁ : FuncInst Nat} (h0 : stubOk 0 4 f₀ = true) (h1 : stubOk 1 1 f₁ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2]) (hFm : F.module.mems = [0])
    (hFl : F.locals = calcD) {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁] ++ fs.drop 2) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → calcInv s') {Q : Post Nat}
    (hQ : BodyExits calcInv Q) :
    HWP P (memHost calcMod (some 0) calcRoles (calcK ρ)) s F
      (vals [] ++ expression calcBody) Q := by
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
  unfold calcBody
  -- the payload `1` at 16
  refine X.i32Const (us := []) ?_
  refine X.i64Const (us := [] ++ [.i32 16]) ?_
  refine X.store64 (us := []) hFm hml (htrap s F hsf hml) fun mi₀ b₀ hmi₀ hst₀ => ?_
  obtain ⟨-, hl₁, hf₁⟩ := setMem_mems (mi := { mi₀ with bytes := b₀ }) hml
  -- node(0, 16, 0, 0)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16] ++ [.i32 0]) ?_
  have hd₁ : Callout.witNode calcSig calcTagOf (calloutIn impNode (some 0)
      (s.setMem 0 { mi₀ with bytes := b₀ }) [.i32 0, .i32 16, .i32 0, .i32 0]) =
      some (⟨CalcTag.num, ((1 : Int64), ())⟩, []) :=
    witNode_eq rfl rfl (segment_of_store hst₀ _ (memOf_setMem hml)) (readVals_one _)
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
  have hρ₁ : ρ r₁ = some (numTree 1) := by
    rcases hans _ (witWrite_eq rfl hd₁ rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · rw [built_num] at ht
      rw [hρ]
      exact ht.symm
  refine X.localSet (us := []) (x := ⟨0⟩) (by simp [hFl, calcD, Idx.toNat]) ?_
  let F₁ := F.setLocal ⟨0⟩ (.i32 r₁)
  have hF₁f : F₁.module.funcs = [0, 1, 2] := hFf
  have hF₁m : F₁.module.mems = [0] := hFm
  -- the payload `2` at 16
  refine X.i32Const (us := []) ?_
  refine X.i64Const (us := [] ++ [.i32 16]) ?_
  refine X.store64 (us := []) hF₁m hml₂' (htrap s₂ _ hfs₂' hml₂') fun mi₂ b₂ hmi₂ hst₂ => ?_
  obtain ⟨-, hl₃, hf₃⟩ := setMem_mems (mi := { mi₂ with bytes := b₂ }) hml₂'
  -- node(0, 16, 0, 0)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16]) ?_
  refine X.i32Const (us := [] ++ [.i32 0] ++ [.i32 16] ++ [.i32 0]) ?_
  have hd₂ : Callout.witNode calcSig calcTagOf (calloutIn impNode (some 0)
      (s₂.setMem 0 { mi₂ with bytes := b₂ }) [.i32 0, .i32 16, .i32 0, .i32 0]) =
      some (⟨CalcTag.num, ((2 : Int64), ())⟩, []) :=
    witNode_eq rfl rfl (segment_of_store hst₂ _ (memOf_setMem hml₂')) (readVals_two _)
      (segment_nil (memOf_setMem hml₂') 0 (Nat.zero_le _)) rfl rfl
  refine hwp_call (us := []) (args := [.i32 0, .i32 16, .i32 0, .i32 0]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := impNode) (by rw [hF₁f]; rfl) (hf0 _ (hf₃.trans hfs₂')) hc₀ he₀
    (by simp [hn₀]) rfl (pre_other (by decide)) ?_
  rintro s₄ r ⟨⟨hfs₄, hml₄⟩, hshape⟩ hans
  have hfs₄' : s₄.funcs = fs := hfs₄.trans (hf₃.trans hfs₂')
  have hml₄' : s₄.mems.length = 1 := hml₄.trans hl₃
  refine ⟨fun res hr => ?_, fun _ => htrap s₄ _ hfs₄' hml₄',
    fun a _ => hthrow s₄ _ a hfs₄' hml₄'⟩
  obtain ⟨r₂, rfl⟩ := (hshape res hr).1 rfl
  subst hr
  have hρ₂ : ρ r₂ = some (numTree 2) := by
    rcases hans _ (witWrite_eq rfl hd₂ rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · rw [built_num] at ht
      rw [hρ]
      exact ht.symm
  refine X.localSet (us := []) (x := ⟨1⟩) (by simp [Frame.setLocal, hFl, calcD, Idx.toNat])
    ?_
  let F₂ := F₁.setLocal ⟨1⟩ (.i32 r₂)
  have hF₂f : F₂.module.funcs = [0, 1, 2] := hFf
  have hF₂m : F₂.module.mems = [0] := hFm
  -- the handles at 0 and 4
  refine X.i32Const (us := []) ?_
  refine X.localGet (us := [] ++ [.i32 0]) (v := .i32 r₁) ?_ ?_
  · simp [Frame.local?, Frame.setLocal, hFl, calcD, Idx.toNat]
  refine X.store32 (us := []) hF₂m hml₄' (htrap s₄ _ hfs₄' hml₄') fun mi₄ b₄ hmi₄ hst₄ => ?_
  obtain ⟨hm₅, hl₅, hf₅⟩ := setMem_mems (mi := { mi₄ with bytes := b₄ }) hml₄'
  refine X.i32Const (us := []) ?_
  refine X.localGet (us := [] ++ [.i32 4]) (v := .i32 r₂) ?_ ?_
  · simp [Frame.local?, Frame.setLocal, hFl, calcD, Idx.toNat]
  refine X.store32 (us := []) hF₂m hl₅ (htrap _ _ (hf₅.trans hfs₄') hl₅)
    fun mi₅ b₅ hmi₅ hst₅ => ?_
  obtain rfl : mi₅ = { mi₄ with bytes := b₄ } := Option.some.inj (hmi₅.symm.trans hm₅)
  obtain ⟨-, hl₆, hf₆⟩ := setMem_mems (mi := { mi₄ with bytes := b₅ }) hl₅
  have hfs₆ : ((s₄.setMem 0 { mi₄ with bytes := b₄ }).setMem 0 { mi₄ with bytes := b₅ }).funcs
      = fs := hf₆.trans (hf₅.trans hfs₄')
  -- node(1, 0, 0, 2)
  have h₀ : bytesAt b₅ ⟨0, 4⟩ = (Memory.encodeLE 4 r₁.toNat).data.toList := by
    rw [Silmaril.Wasm.Logic.Core.bytesAt_store_disjoint hst₅ (.inr (by decide))]
    exact bytes_of_store32 hst₄
  have h₄ : bytesAt b₅ ⟨4, 4⟩ = (Memory.encodeLE 4 r₂.toNat).data.toList :=
    bytes_of_store32 hst₅
  have h8 : 8 ≤ b₅.size := by
    have := store_inBounds hst₅; simp [effAddr, IntType.width] at this ⊢; omega
  obtain ⟨cs, hcs, hle⟩ := children_pair (o := calloutIn impNode (some 0)
      ((s₄.setMem 0 { mi₄ with bytes := b₄ }).setMem 0 { mi₄ with bytes := b₅ })
      [.i32 1, .i32 0, .i32 0, .i32 2]) (memOf_setMem hl₅) h8 h₀ h₄
  have hd₃ : Callout.witNode calcSig calcTagOf (calloutIn impNode (some 0)
      ((s₄.setMem 0 { mi₄ with bytes := b₄ }).setMem 0 { mi₄ with bytes := b₅ })
      [.i32 1, .i32 0, .i32 0, .i32 2]) = some (⟨CalcTag.add, ()⟩, [r₁, r₂]) :=
    witNode_eq rfl rfl (segment_nil (memOf_setMem hl₅) 0 (Nat.zero_le _)) rfl hcs hle rfl
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 1]) ?_
  refine X.i32Const (us := [] ++ [.i32 1] ++ [.i32 0]) ?_
  refine X.i32Const (us := [] ++ [.i32 1] ++ [.i32 0] ++ [.i32 0]) ?_
  refine hwp_call (us := []) (args := [.i32 1, .i32 0, .i32 0, .i32 2]) (x := ⟨0⟩) (k := 0)
    (fk := f₀) (i := impNode) (by show F₂.module.funcs[_]? = _; rw [hF₂f]; rfl) (hf0 _ hfs₆)
    hc₀ he₀ (by simp [hn₀]) rfl (pre_other (by decide)) ?_
  rintro s₇ r ⟨⟨hfs₇, hml₇⟩, hshape⟩ hans
  have hfs₇' : s₇.funcs = fs := hfs₇.trans hfs₆
  have hml₇' : s₇.mems.length = 1 := hml₇.trans hl₆
  refine ⟨fun res hr => ?_, fun _ => htrap s₇ _ hfs₇' hml₇',
    fun a _ => hthrow s₇ _ a hfs₇' hml₇'⟩
  obtain ⟨r₃, rfl⟩ := (hshape res hr).1 rfl
  subst hr
  have hρ₃ : ρ r₃ = some addTree := by
    rcases hans _ (witWrite_eq rfl hd₃ rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · rw [built_add hρ₁ hρ₂] at ht
      rw [hρ]
      exact ht.symm
  -- accept(r₃)
  refine hwp_call (us := []) (args := [.i32 r₃]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := impAcc) (by show F₂.module.funcs[_]? = _; rw [hF₂f]; rfl) (hf1 _ hfs₇') hc₁ he₁
    (by simp [hn₁]) rfl ?_ ?_
  · intro h hd t ht
    simp [calcRoles, witRoles, witAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32] at hd
    subst hd
    rw [hρ₃] at ht
    cases ht
    rfl
  rintro s₈ r ⟨⟨hfs₈, hml₈⟩, hshape⟩ -
  have hfs₈' : s₈.funcs = fs := hfs₈.trans hfs₇'
  have hml₈' : s₈.mems.length = 1 := hml₈.trans hml₇'
  refine ⟨fun res hr => ?_, fun _ => htrap s₈ _ hfs₈' hml₈',
    fun a _ => hthrow s₈ _ a hfs₈' hml₈'⟩
  obtain rfl := (hshape res hr).2 rfl
  exact X.done (hQ s₈ (hinv s₈ hfs₈' hml₈') _).1

/-- **`calcMod` meets the writer contract** in every fixed environment, for every profile. -/
theorem calc_sat (P : Profile) (ρ : Env (BitVec 32) (AST calcSig.toAstSig)) :
    MemSat P calcMod 0 calcRoles (calcK ρ) calcInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := calc_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 2 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, hps, hrs, hfuncs, hmems2, hD⟩ := fnOk_spec h2
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → calcInv s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, calcInv s → s.funcs = c.store.funcs := by
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
  exact calc_body h0 h1 (by simp [Frame.forCall, hfuncs]) (by simp [Frame.forCall, hmems2])
    (by simp [Frame.forCall, hD]) (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs)
    hml' hinv hQ

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst
