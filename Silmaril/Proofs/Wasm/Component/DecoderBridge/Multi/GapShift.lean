module

public import Silmaril.Proofs.Wasm.Component.Reference.CoreShift
public import Silmaril.Proofs.Wasm.Component.Lime1RT.Inst.Store

/-!
# Relocating a Core 3.0 instantiation into a shared store, imports kept in place

`Reference.CoreShift` relates a module instantiated alone in `t` to the same module instantiated
after a store `s₀`, every address of `t` shifted past `s₀`. There the imports of the module are
shifted too. For the later core instances of a component (`DecoderBridge.Multi`) the imports are
the trampolines at the **start** of the shared store, while the module's own objects are
allocated at its end: the IR instantiates the module alone, its imports the first `b` functions
of its store, and the reference machine in the shared store `pre`, its imports the first `b`
functions of `pre`.

* `GShift`: offsets of every address space but functions, and a map of function addresses;
  references, values, instances, frames and stores are mapped along it (as `Reference.Shift`);
* `Gap H`: the shared store `pre` and the number `b` of imported functions; `Gap.fnMap`
  keeps the addresses below `b` and moves the others past `pre`, `Gap.sh` is the `GShift`;
  `Gap.rel t`: `pre` followed by the store `t` without its first `b` functions, mapped;
* `Gap.PreOk g fs`: the first `b` functions of `pre` are those of `fs`, mapped (so the
  function at `fnMap a` of `g.rel t` is the one at `a` of `t`, mapped: `funcs_gap`);
* `prepare?_gap`: preparing a module in `g.rel t` against the mapped external addresses is
  preparing it in `t` and mapping the store and frame.

The proofs follow `Reference.CoreShift` (copied and adapted).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.Component.Reference (Store.app)

/-- Offsets of every address space of a Core store but functions, and a map of function
addresses. -/
structure GShift where
  tg : Nat
  gl : Nat
  me : Nat
  ta : Nat
  fn : Nat → Nat
  da : Nat
  el : Nat
  st : Nat
  ar : Nat
  ex : Nat

namespace GShift

variable {H : Type} (δ : GShift)

/-- Shift a reference. -/
def ref : Ref → Ref
  | .struct a => .struct (δ.st + a)
  | .array a => .array (δ.ar + a)
  | .func a => .func (δ.fn a)
  | .exn a => .exn (δ.ex + a)
  | .extern r => .extern (ref r)
  | r => r

/-- Shift a value. -/
def val : Val → Val
  | .ref r => .ref (δ.ref r)
  | v => v

/-- Shift a field value. -/
def fval : FieldVal → FieldVal
  | .val v => .val (δ.val v)
  | p => p

/-- Shift an external address. -/
def xa : ExternAddr → ExternAddr
  | .tag a => .tag (δ.tg + a)
  | .global a => .global (δ.gl + a)
  | .mem a => .mem (δ.me + a)
  | .table a => .table (δ.ta + a)
  | .func a => .func (δ.fn a)

/-- Shift an export instance. -/
def xinst (x : ExportInst) : ExportInst := { x with addr := δ.xa x.addr }

/-- Shift a module instance. -/
def minst (mi : ModuleInst) : ModuleInst :=
  { types := mi.types, tags := mi.tags.map (δ.tg + ·), globals := mi.globals.map (δ.gl + ·),
    mems := mi.mems.map (δ.me + ·), tables := mi.tables.map (δ.ta + ·),
    funcs := mi.funcs.map δ.fn, datas := mi.datas.map (δ.da + ·),
    elems := mi.elems.map (δ.el + ·), exports := mi.exports.map δ.xinst }

/-- Shift a function instance (its module instance). -/
def finst (fi : FuncInst H) : FuncInst H := { fi with module := δ.minst fi.module }

def ginst (g : GlobalInst) : GlobalInst := { g with value := δ.val g.value }
def tinst (t : TableInst) : TableInst := { t with refs := t.refs.map δ.ref }
def einst (e : ElemInst) : ElemInst := { e with refs := e.refs.map δ.ref }
def sinst (si : StructInst) : StructInst := { si with fields := si.fields.map δ.fval }
def ainst (ai : ArrayInst) : ArrayInst := { ai with fields := ai.fields.map δ.fval }
def xninst (e : ExnInst) : ExnInst := ⟨δ.tg + e.tag, e.fields.map δ.val⟩

/-- Shift a frame. -/
def frame (f : Frame) : Frame := ⟨f.locals.map (Option.map δ.val), δ.minst f.module⟩

/-- Shift every object of a store. -/
def store (t : Store H) : Store H :=
  { tags := t.tags, globals := t.globals.map δ.ginst, mems := t.mems,
    tables := t.tables.map δ.tinst, funcs := t.funcs.map δ.finst, datas := t.datas,
    elems := t.elems.map δ.einst, structs := t.structs.map δ.sinst,
    arrays := t.arrays.map δ.ainst, exns := t.exns.map δ.xninst }

@[simp] theorem val_num (v : NumVal) : δ.val (.num v) = .num v := rfl
@[simp] theorem val_vec (b : BitVec 128) : δ.val (.vec b) = .vec b := rfl
@[simp] theorem val_ref (r : Ref) : δ.val (.ref r) = .ref (δ.ref r) := rfl
@[simp] theorem ref_null : δ.ref .null = .null := rfl
@[simp] theorem ref_i31 (b : BitVec 31) : δ.ref (.i31 b) = .i31 b := rfl
@[simp] theorem ref_func (a : Nat) : δ.ref (.func a) = .func (δ.fn a) := rfl
@[simp] theorem ref_struct (a : Nat) : δ.ref (.struct a) = .struct (δ.st + a) := rfl
@[simp] theorem ref_array (a : Nat) : δ.ref (.array a) = .array (δ.ar + a) := rfl
@[simp] theorem ref_extern (r : Ref) : δ.ref (.extern r) = .extern (δ.ref r) := rfl

theorem ref_eq_null_iff {r : Ref} : δ.ref r = .null ↔ r = .null := by
  cases r <;> simp [ref]

@[simp] theorem minst_types (mi : ModuleInst) : (δ.minst mi).types = mi.types := rfl
@[simp] theorem minst_funcs (mi : ModuleInst) : (δ.minst mi).funcs = mi.funcs.map δ.fn :=
  rfl
@[simp] theorem minst_globals (mi : ModuleInst) :
    (δ.minst mi).globals = mi.globals.map (δ.gl + ·) := rfl
@[simp] theorem frame_module (f : Frame) : (δ.frame f).module = δ.minst f.module := rfl

theorem minst_empty : δ.minst ({} : ModuleInst) = {} := rfl

theorem fval_packField (st : CStorageType) (v : Val) :
    δ.fval (packField st v) = packField st (δ.val v) := by
  rcases st with _ | _
  · rfl
  · rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

theorem packable_val (st : CStorageType) (v : Val) : packable st (δ.val v) = packable st v := by
  rcases st with _ | _
  · rfl
  · rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

theorem int?_val (t : IntType) (v : Val) : (δ.val v).int? t = v.int? t := by
  rcases v with _ | _ | _ <;> rfl

theorem val_defaultVal {t : CValType} {v : Val} (h : defaultVal? t = some v) : δ.val v = v := by
  unfold defaultVal? at h
  split at h <;> first | (cases h; rfl) | cases h

theorem map_val_mapM_default {α : Type} (g : α → CValType) :
    ∀ {l : List α} {dvs : List Val}, l.mapM (fun x => defaultVal? (g x)) = some dvs →
      dvs.map δ.val = dvs
  | [], dvs, h => by cases h; rfl
  | x :: l, dvs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs, hvs, rfl⟩ := h
    simp only [List.map_cons, val_defaultVal δ hv, map_val_mapM_default g hvs]

end GShift

variable {H : Type}

/-- **The shared store and the imported functions**: the store `pre` before the instantiation,
and the number `b` of functions the module imports (the first `b` functions of `pre`). -/
structure Gap (H : Type) where
  pre : Store H
  b : Nat

namespace Gap

variable (g : Gap H)

/-- The map of function addresses: imports stay, the module's own functions move past `pre`. -/
def fnMap (a : Nat) : Nat := if a < g.b then a else g.pre.funcs.length + (a - g.b)

/-- The map of every address space. -/
def sh : GShift :=
  ⟨g.pre.tags.length, g.pre.globals.length, g.pre.mems.length, g.pre.tables.length, g.fnMap,
    g.pre.datas.length, g.pre.elems.length, g.pre.structs.length, g.pre.arrays.length,
    g.pre.exns.length⟩

/-- **The store `t` in the shared store**: `pre`, followed by `t` without its first `b`
functions (its imports), mapped. -/
def rel (t : Store H) : Store H := Store.app g.pre (g.sh.store { t with funcs := t.funcs.drop g.b })

/-- The first `b` functions of `pre` are the first `b` of `fs`, mapped. -/
def PreOk (fs : List (FuncInst H)) : Prop :=
  g.b ≤ fs.length ∧ ∀ a, a < g.b → g.pre.funcs[a]? = (fs[a]?).map g.sh.finst

end Gap

section Basic

variable (g : Gap H)

@[simp] theorem rel_globals (t : Store H) :
    (g.rel t).globals = g.pre.globals ++ t.globals.map g.sh.ginst := rfl
@[simp] theorem rel_funcs (t : Store H) :
    (g.rel t).funcs = g.pre.funcs ++ (t.funcs.drop g.b).map g.sh.finst := rfl
@[simp] theorem rel_structs (t : Store H) :
    (g.rel t).structs = g.pre.structs ++ t.structs.map g.sh.sinst := rfl
@[simp] theorem rel_arrays (t : Store H) :
    (g.rel t).arrays = g.pre.arrays ++ t.arrays.map g.sh.ainst := rfl
@[simp] theorem rel_exns (t : Store H) :
    (g.rel t).exns = g.pre.exns ++ t.exns.map g.sh.xninst := rfl

@[simp] theorem sh_fn : g.sh.fn = g.fnMap := rfl
@[simp] theorem sh_gl : g.sh.gl = g.pre.globals.length := rfl
@[simp] theorem sh_st : g.sh.st = g.pre.structs.length := rfl
@[simp] theorem sh_ar : g.sh.ar = g.pre.arrays.length := rfl
@[simp] theorem sh_ex : g.sh.ex = g.pre.exns.length := rfl
@[simp] theorem sh_tg : g.sh.tg = g.pre.tags.length := rfl
@[simp] theorem sh_me : g.sh.me = g.pre.mems.length := rfl
@[simp] theorem sh_ta : g.sh.ta = g.pre.tables.length := rfl

theorem fnMap_lt {a : Nat} (h : a < g.b) : g.fnMap a = a := by simp [Gap.fnMap, h]

theorem fnMap_ge {a : Nat} (h : g.b ≤ a) : g.fnMap a = g.pre.funcs.length + (a - g.b) := by
  simp [Gap.fnMap, Nat.not_lt.mpr h]

/-- **The function at `fnMap a` of `g.rel t` is the one at `a` of `t`, mapped.** -/
theorem funcs_gap {t : Store H} (hP : g.PreOk t.funcs) (a : Nat) :
    (g.rel t).funcs[g.sh.fn a]? = (t.funcs[a]?).map g.sh.finst := by
  rw [sh_fn, rel_funcs]
  by_cases ha : a < g.b
  · rw [fnMap_lt g ha, ← hP.2 a ha]
    have hl : a < t.funcs.length := Nat.lt_of_lt_of_le ha hP.1
    obtain ⟨fi, hfi⟩ : ∃ fi, t.funcs[a]? = some fi := ⟨_, List.getElem?_eq_getElem hl⟩
    have hpa : a < g.pre.funcs.length := by
      have := hP.2 a ha
      rw [hfi] at this
      exact (List.getElem?_eq_some_iff.mp this).1
    rw [List.getElem?_append_left hpa]
  · have hb : g.b ≤ a := Nat.not_lt.mp ha
    rw [fnMap_ge g hb, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_map, List.getElem?_drop, Nat.add_sub_cancel' hb]

/-- The map of function addresses is injective once `pre` has at least `b` functions. -/
theorem fnMap_injective (hb : g.b ≤ g.pre.funcs.length) : Function.Injective g.sh.fn := by
  intro a a' h
  simp only [sh_fn, Gap.fnMap] at h
  split_ifs at h <;> omega

theorem PreOk.le_pre {fs : List (FuncInst H)} (hP : g.PreOk fs) : g.b ≤ g.pre.funcs.length := by
  rcases Nat.eq_zero_or_pos g.b with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hl : g.b - 1 < fs.length := by have := hP.1; omega
    have e := hP.2 (g.b - 1) (by omega)
    rw [List.getElem?_eq_getElem hl, Option.map_some] at e
    have := (List.getElem?_eq_some_iff.mp e).1
    omega

theorem funcs_gap_of {t : Store H} (hP : g.PreOk t.funcs) {a : Nat} {fi : FuncInst H}
    (h : t.funcs[a]? = some fi) : (g.rel t).funcs[g.sh.fn a]? = some (g.sh.finst fi) := by
  rw [funcs_gap g hP, h, Option.map_some]

theorem structs_gap (t : Store H) (a : Nat) :
    (g.rel t).structs[g.pre.structs.length + a]? = (t.structs[a]?).map g.sh.sinst := by
  rw [rel_structs, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map]

theorem arrays_gap (t : Store H) (a : Nat) :
    (g.rel t).arrays[g.pre.arrays.length + a]? = (t.arrays[a]?).map g.sh.ainst := by
  rw [rel_arrays, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map]

theorem exns_gap (t : Store H) (a : Nat) :
    (g.rel t).exns[g.pre.exns.length + a]? = (t.exns[a]?).map g.sh.xninst := by
  rw [rel_exns, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map]


theorem rel_addStruct (t : Store H) (si : StructInst) :
    g.rel (t.addStruct si) = (g.rel t).addStruct (g.sh.sinst si) := by
  simp [Gap.rel, Store.app, GShift.store, Store.addStruct]

theorem rel_addArray (t : Store H) (ai : ArrayInst) :
    g.rel (t.addArray ai) = (g.rel t).addArray (g.sh.ainst ai) := by
  simp [Gap.rel, Store.app, GShift.store, Store.addArray]

theorem global?_gap (t : Store H) (f : Frame) (x : GlobalIdx) :
    (g.rel t).global? (g.sh.frame f) x =
      (t.global? f x).map fun p => (g.sh.gl + p.1, g.sh.ginst p.2) := by
  simp only [Store.global?, GShift.frame_module, GShift.minst_globals, List.getElem?_map,
    Option.bind_eq_bind, rel_globals]
  cases f.module.globals[x.toNat]? with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Option.bind_some, sh_gl]
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_map]
    cases t.globals[a]? <;> rfl

theorem type?_frame (f : Frame) (x : TypeIdx) : (g.sh.frame f).type? x = f.type? x := rfl

end Basic

/-! ## Stacks -/

section Stacks

variable (δ : GShift)

theorem popN?_map (vs : List Val) (n : Nat) :
    popN? (vs.map δ.val) n = (popN? vs n).map fun p => (p.1.map δ.val, p.2.map δ.val) := by
  unfold popN?
  simp only [List.length_map]
  split <;> simp [List.map_take, List.map_drop]

theorem pop1?_map (vs : List Val) :
    pop1? (vs.map δ.val) = (pop1? vs).map fun p => (p.1.map δ.val, δ.val p.2) := by
  unfold pop1?
  simp only [popN?_map, Option.bind_eq_bind]
  cases popN? vs 1 with
  | none => rfl
  | some p =>
    obtain ⟨pre, args⟩ := p
    rcases args with _ | ⟨a, _ | _⟩ <;> rfl

theorem pop2?_map (vs : List Val) :
    pop2? (vs.map δ.val) =
      (pop2? vs).map fun p => (p.1.map δ.val, δ.val p.2.1, δ.val p.2.2) := by
  unfold pop2?
  simp only [popN?_map, Option.bind_eq_bind]
  cases popN? vs 2 with
  | none => rfl
  | some p =>
    obtain ⟨pre, args⟩ := p
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> rfl

end Stacks

/-! ## Constant evaluation -/

section Const

variable (g : Gap H)

/-- The relocation of a store and a value stack. -/
abbrev relSV (p : Store H × List Val) : Store H × List Val := (g.rel p.1, p.2.map g.sh.val)

theorem zip_map_val {α : Type} (l : List α) (args : List Val) :
    l.zip (args.map g.sh.val) = (l.zip args).map fun p => (p.1, g.sh.val p.2) := by
  rw [List.zip_map_right]
  rfl

theorem structNew?_gap (t : Store H) (f : Frame) (vs : List Val) (x : TypeIdx) :
    structNew? (g.rel t) (g.sh.frame f) (vs.map g.sh.val) x =
      (structNew? t f vs x).map (relSV g) := by
  unfold structNew?
  simp only [type?_frame, popN?_map, Option.bind_eq_bind]
  cases f.type? x with
  | none => rfl
  | some d =>
    simp only [Option.bind_some]
    cases expandStruct? d with
    | none => rfl
    | some fs =>
      simp only [Option.bind_some]
      cases popN? vs fs.length with
      | none => rfl
      | some p =>
        obtain ⟨pre, args⟩ := p
        simp only [Option.map_some, Option.bind_some, zip_map_val, List.all_map,
          Function.comp_def, GShift.packable_val]
        split
        · simp [relSV, rel_addStruct, GShift.sinst, Function.comp_def, GShift.fval_packField]
        · rfl

theorem arrayNewFixed?_gap (t : Store H) (f : Frame) (vs : List Val) (x : TypeIdx)
    (n : Fin (2 ^ 32)) :
    arrayNewFixed? (g.rel t) (g.sh.frame f) (vs.map g.sh.val) x n =
      (arrayNewFixed? t f vs x n).map (relSV g) := by
  unfold arrayNewFixed?
  simp only [type?_frame, popN?_map, Option.bind_eq_bind]
  cases f.type? x with
  | none => rfl
  | some d =>
    simp only [Option.bind_some]
    cases expandArray? d with
    | none => rfl
    | some ft =>
      simp only [Option.bind_some]
      cases popN? vs n.val with
      | none => rfl
      | some p =>
        obtain ⟨pre, args⟩ := p
        simp only [Option.map_some, Option.bind_some, List.all_map, Function.comp_def,
          GShift.packable_val]
        split
        · simp [relSV, rel_addArray, GShift.ainst, Function.comp_def, GShift.fval_packField]
        · rfl

section Instr

variable (t : Store H) (f : Frame) (vs : List Val)

theorem constInstr?_gap_intBinOp (tt : IntType) (op : IntBinOp) :
    constInstr? (g.rel t) (g.sh.frame f) (vs.map g.sh.val) (.intBinOp tt op) =
      (constInstr? t f vs (.intBinOp tt op)).map (relSV g) := by
  simp only [constInstr?, pop2?_map, Option.bind_eq_bind]
  split
  · rcases pop2? vs with _ | ⟨pre, v₁, v₂⟩
    · rfl
    simp only [Option.map_some, Option.bind_some, GShift.int?_val]
    rcases v₁.int? tt with _ | x
    · rfl
    rcases v₂.int? tt with _ | y
    · rfl
    simp only [Option.bind_some]
    cases Numerics.intBinOp tt op x y <;> simp [relSV]
  · rfl

theorem constInstr?_gap_anyConvertExtern :
    constInstr? (g.rel t) (g.sh.frame f) (vs.map g.sh.val) .anyConvertExtern =
      (constInstr? t f vs .anyConvertExtern).map (relSV g) := by
  simp only [constInstr?, pop1?_map, Option.bind_eq_bind]
  rcases pop1? vs with _ | ⟨pre, _ | _ | r⟩
  · rfl
  · rfl
  · rfl
  · cases r <;> simp [relSV, GShift.ref]

theorem constInstr?_gap_externConvertAny :
    constInstr? (g.rel t) (g.sh.frame f) (vs.map g.sh.val) .externConvertAny =
      (constInstr? t f vs .externConvertAny).map (relSV g) := by
  simp only [constInstr?, pop1?_map, Option.bind_eq_bind]
  rcases pop1? vs with _ | ⟨pre, _ | _ | r⟩
  · rfl
  · rfl
  · rfl
  by_cases hr : r = .null
  · subst hr
    simp [relSV]
  have hr' : g.sh.ref r ≠ .null := fun h => hr ((GShift.ref_eq_null_iff _).1 h)
  simp [relSV, hr, hr']

theorem constInstr?_gap_structNewDefault (x : TypeIdx) :
    constInstr? (g.rel t) (g.sh.frame f) (vs.map g.sh.val) (.structNewDefault x) =
      (constInstr? t f vs (.structNewDefault x)).map (relSV g) := by
  simp only [constInstr?, type?_frame, Option.bind_eq_bind]
  rcases f.type? x with _ | d
  · rfl
  simp only [Option.bind_some]
  rcases expandStruct? d with _ | fs
  · rfl
  simp only [Option.bind_some]
  rcases hm : fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) with _ | dvs
  · rfl
  simp only [Option.bind_some]
  conv => lhs; rw [← g.sh.map_val_mapM_default _ hm]
  rw [← List.map_append, structNew?_gap]

theorem constInstr?_gap_arrayNew (x : TypeIdx) :
    constInstr? (g.rel t) (g.sh.frame f) (vs.map g.sh.val) (.arrayNew x) =
      (constInstr? t f vs (.arrayNew x)).map (relSV g) := by
  simp only [constInstr?, pop2?_map, Option.bind_eq_bind]
  rcases pop2? vs with _ | ⟨pre, v, n⟩
  · rfl
  simp only [Option.map_some, Option.bind_some, GShift.int?_val]
  rcases n.int? .i32 with _ | k
  · rfl
  simp only [Option.bind_some]
  rw [← List.map_replicate, ← List.map_append, arrayNewFixed?_gap]

theorem constInstr?_gap_arrayNewDefault (x : TypeIdx) :
    constInstr? (g.rel t) (g.sh.frame f) (vs.map g.sh.val) (.arrayNewDefault x) =
      (constInstr? t f vs (.arrayNewDefault x)).map (relSV g) := by
  simp only [constInstr?, pop1?_map, type?_frame, Option.bind_eq_bind]
  rcases pop1? vs with _ | ⟨pre, n⟩
  · rfl
  simp only [Option.map_some, Option.bind_some, GShift.int?_val]
  rcases n.int? .i32 with _ | k
  · rfl
  simp only [Option.bind_some]
  rcases f.type? x with _ | d
  · rfl
  simp only [Option.bind_some]
  rcases expandArray? d with _ | ft
  · rfl
  simp only [Option.bind_some]
  rcases hv : defaultVal? (fieldStorage ft).unpack with _ | v
  · rfl
  simp only [Option.bind_some]
  conv => lhs; rw [← g.sh.val_defaultVal hv]
  rw [← List.map_replicate, ← List.map_append, arrayNewFixed?_gap]

end Instr

theorem constInstr?_gap (t : Store H) (f : Frame) (vs : List Val) (i : Instr) :
    constInstr? (g.rel t) (g.sh.frame f) (vs.map g.sh.val) i =
      (constInstr? t f vs i).map (relSV g) := by
  cases i with
  | refFunc x =>
    simp only [constInstr?, GShift.frame_module, GShift.minst_funcs, List.getElem?_map,
      Option.bind_eq_bind]
    cases f.module.funcs[x.toNat]? <;> simp [relSV]
  | refI31 =>
    simp only [constInstr?, pop1?_map, Option.bind_eq_bind]
    rcases pop1? vs with _ | ⟨pre, v⟩
    · rfl
    simp only [Option.map_some, Option.bind_some, GShift.int?_val]
    cases v.int? .i32 <;> simp [relSV]
  | globalGet x =>
    simp only [constInstr?, global?_gap, Option.bind_eq_bind]
    cases t.global? f x <;> simp [relSV, GShift.ginst]
  | intBinOp tt op => exact constInstr?_gap_intBinOp g t f vs tt op
  | anyConvertExtern => exact constInstr?_gap_anyConvertExtern g t f vs
  | externConvertAny => exact constInstr?_gap_externConvertAny g t f vs
  | structNew x => exact structNew?_gap g t f vs x
  | structNewDefault x => exact constInstr?_gap_structNewDefault g t f vs x
  | arrayNew x => exact constInstr?_gap_arrayNew g t f vs x
  | arrayNewDefault x => exact constInstr?_gap_arrayNewDefault g t f vs x
  | arrayNewFixed x n => exact arrayNewFixed?_gap g t f vs x n
  | _ => simp [constInstr?, relSV]

end Const

/-! ## Initialiser runs -/

section Eval

variable (g : Gap H)

theorem constExpr?_gap (t : Store H) (f : Frame) (e : Expr) :
    constExpr? (g.rel t) (g.sh.frame f) e = (constExpr? t f e).map (relSV g) := by
  unfold constExpr?
  suffices ∀ (vs : List Val) (t : Store H),
      e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 (g.sh.frame f) st.2 i)
          (g.rel t, vs.map g.sh.val) =
        (e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (t, vs)).map
          (relSV g) from this [] t
  induction e with
  | nil => intro vs t; rfl
  | cons i e ih =>
    intro vs t
    simp only [List.foldlM_cons, constInstr?_gap, Option.bind_eq_bind]
    cases constInstr? t f vs i with
    | none => rfl
    | some p => exact ih p.2 p.1

/-- The relocation of a store and a value. -/
abbrev relSV1 (p : Store H × Val) : Store H × Val := (g.rel p.1, g.sh.val p.2)

theorem evalConst?_gap (t : Store H) (f : Frame) (e : Expr) :
    evalConst? (g.rel t) (g.sh.frame f) e = (evalConst? t f e).map (relSV1 g) := by
  unfold evalConst?
  rw [constExpr?_gap]
  rcases constExpr? t f e with _ | ⟨t', _ | ⟨v, _ | _⟩⟩ <;> rfl

theorem allocGlobal_gap (t : Store H) (gt : CGlobalType) (v : Val) :
    allocGlobal (g.rel t) gt (g.sh.val v) =
      (g.rel (allocGlobal t gt v).1, g.sh.gl + (allocGlobal t gt v).2) := by
  simp [allocGlobal, Gap.rel, Gap.sh, Store.app, GShift.store, GShift.ginst]

theorem frame_withGlobal (f : Frame) (a : Nat) :
    { g.sh.frame f with module := { (g.sh.frame f).module with
        globals := (g.sh.frame f).module.globals ++ [g.sh.gl + a] } } =
      g.sh.frame { f with module := { f.module with globals := f.module.globals ++ [a] } } := by
  simp [GShift.frame, GShift.minst]

/-- The relocation of the result of `$evalglobals`. -/
abbrev relG (p : Store H × Frame × List Val) : Store H × Frame × List Val :=
  (g.rel p.1, g.sh.frame p.2.1, p.2.2.map g.sh.val)

theorem evalGlobals?_gap (t : Store H) (f : Frame) (gs : List CGlobalType) (es : List Expr) :
    evalGlobals? evalConst? (g.rel t) (g.sh.frame f) gs es =
      (evalGlobals? evalConst? t f gs es).map (relG g) := by
  induction gs generalizing t f es with
  | nil => cases es <;> rfl
  | cons g gs ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      simp only [evalGlobals?, evalConst?_gap]
      rcases evalConst? t f e with _ | ⟨t', v⟩
      · rfl
      · simp only [Option.map_some, relSV1, allocGlobal_gap, frame_withGlobal, ih]
        rcases evalGlobals? evalConst? (allocGlobal t' g v).1 _ gs es with _ | ⟨s'', f'', vs⟩
        · rfl
        · rfl

/-- The relocation of the result of `$evalexprs`. -/
abbrev relE (p : Store H × Frame × List Ref) : Store H × Frame × List Ref :=
  (g.rel p.1, g.sh.frame p.2.1, p.2.2.map g.sh.ref)

theorem evalExprs?_gap (t : Store H) (f : Frame) (es : List Expr) :
    evalExprs? evalConst? (g.rel t) (g.sh.frame f) es =
      (evalExprs? evalConst? t f es).map (relE g) := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih =>
    simp only [evalExprs?, evalConst?_gap]
    rcases evalConst? t f e with _ | ⟨t', _ | _ | r⟩
    · rfl
    · rfl
    · rfl
    · simp only [Option.map_some, relSV1, GShift.val_ref, ih]
      rcases evalExprs? evalConst? t' f es with _ | ⟨s'', f'', rs⟩ <;> rfl

/-- The relocation of the result of `$evalexprss`. -/
abbrev relEs (p : Store H × Frame × List (List Ref)) : Store H × Frame × List (List Ref) :=
  (g.rel p.1, g.sh.frame p.2.1, p.2.2.map (·.map g.sh.ref))

theorem evalExprss?_gap (t : Store H) (f : Frame) (ess : List (List Expr)) :
    evalExprss? evalConst? (g.rel t) (g.sh.frame f) ess =
      (evalExprss? evalConst? t f ess).map (relEs g) := by
  induction ess generalizing t f with
  | nil => rfl
  | cons es ess ih =>
    simp only [evalExprss?, evalExprs?_gap]
    rcases evalExprs? evalConst? t f es with _ | ⟨t', f', rs⟩
    · rfl
    · simp only [Option.map_some, relE, ih]
      rcases evalExprss? evalConst? t' f' ess with _ | ⟨s'', f'', rss⟩ <;> rfl

end Eval

/-! ## Allocation -/

section Alloc

variable (g : Gap H)

theorem allocMany_gap {α β : Type} (alloc₁ : Store H → β → Store H × Nat)
    (alloc₂ : Store H → α → Store H × Nat) (φ : α → β) (off : Nat)
    (h : ∀ t x, alloc₁ (g.rel t) (φ x) = (g.rel (alloc₂ t x).1, off + (alloc₂ t x).2))
    (t : Store H) (xs : List α) :
    allocMany alloc₁ (g.rel t) (xs.map φ) =
      (g.rel (allocMany alloc₂ t xs).1, (allocMany alloc₂ t xs).2.map (off + ·)) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => simp only [allocMany, List.map_cons, h, ih]

theorem allocTag_gap (t : Store H) (d : DefType) :
    allocTag (g.rel t) d = (g.rel (allocTag t d).1, g.sh.tg + (allocTag t d).2) := by
  simp [allocTag, Gap.rel, Gap.sh, Store.app, GShift.store]

theorem allocMem_gap (t : Store H) (d : MemoryType) :
    allocMem (g.rel t) d = (g.rel (allocMem t d).1, g.sh.me + (allocMem t d).2) := by
  simp [allocMem, Gap.rel, Gap.sh, Store.app, GShift.store]

theorem allocTable_gap (t : Store H) (tt : CTableType) (r : Ref) :
    allocTable (g.rel t) tt (g.sh.ref r) =
      (g.rel (allocTable t tt r).1, g.sh.ta + (allocTable t tt r).2) := by
  simp [allocTable, Gap.rel, Gap.sh, Store.app, GShift.store, GShift.tinst, List.map_replicate]

theorem allocData_gap (t : Store H) (b : ByteArray) :
    allocData (g.rel t) b = (g.rel (allocData t b).1, g.sh.da + (allocData t b).2) := by
  simp [allocData, Gap.rel, Gap.sh, Store.app, GShift.store]

theorem allocElem_gap (t : Store H) (rt : CRefType) (refs : List Ref) :
    allocElem (g.rel t) rt (refs.map g.sh.ref) =
      (g.rel (allocElem t rt refs).1, g.sh.el + (allocElem t rt refs).2) := by
  simp [allocElem, Gap.rel, Gap.sh, Store.app, GShift.store, GShift.einst]

theorem allocFunc_gap (t : Store H) (hb : g.b ≤ t.funcs.length) (d : DefType) (code : FuncCode H)
    (mi : ModuleInst) :
    allocFunc (g.rel t) d code (g.sh.minst mi) =
      (g.rel (allocFunc t d code mi).1, g.sh.fn (allocFunc t d code mi).2) := by
  simp only [allocFunc, Gap.rel, Store.app, GShift.store, sh_fn, fnMap_ge g hb, List.length_append,
    List.length_map, List.length_drop, List.drop_append_of_le_length hb, List.map_append,
    List.append_assoc, List.map_cons, List.map_nil, Prod.mk.injEq, and_true]
  rfl

theorem allocMany_func_gap (mi : ModuleInst) :
    ∀ (t : Store H), g.b ≤ t.funcs.length → ∀ xs : List (DefType × Func),
    (allocMany (fun s (p : DefType × Func) => allocFunc s p.1 (.wasm p.2) (g.sh.minst mi))
        (g.rel t) xs).1 =
      g.rel (allocMany (fun s (p : DefType × Func) => allocFunc s p.1 (.wasm p.2) mi) t xs).1
  | t, _, [] => rfl
  | t, hb, x :: xs => by
    simp only [allocMany]
    rw [allocFunc_gap g t hb]
    exact allocMany_func_gap mi _ (by simp [allocFunc]; omega) xs

variable (δ : GShift)

theorem tags_map : ∀ xas : List ExternAddr,
    ExternAddr.tags (xas.map δ.xa) = (ExternAddr.tags xas).map (δ.tg + ·)
  | [] => rfl
  | x :: xas => by cases x <;> simp [ExternAddr.tags, GShift.xa, tags_map xas]

theorem globals_map : ∀ xas : List ExternAddr,
    ExternAddr.globals (xas.map δ.xa) = (ExternAddr.globals xas).map (δ.gl + ·)
  | [] => rfl
  | x :: xas => by cases x <;> simp [ExternAddr.globals, GShift.xa, globals_map xas]

theorem mems_map : ∀ xas : List ExternAddr,
    ExternAddr.mems (xas.map δ.xa) = (ExternAddr.mems xas).map (δ.me + ·)
  | [] => rfl
  | x :: xas => by cases x <;> simp [ExternAddr.mems, GShift.xa, mems_map xas]

theorem tables_map : ∀ xas : List ExternAddr,
    ExternAddr.tables (xas.map δ.xa) = (ExternAddr.tables xas).map (δ.ta + ·)
  | [] => rfl
  | x :: xas => by cases x <;> simp [ExternAddr.tables, GShift.xa, tables_map xas]

theorem funcs_map : ∀ xas : List ExternAddr,
    ExternAddr.funcs (xas.map δ.xa) = (ExternAddr.funcs xas).map δ.fn
  | [] => rfl
  | x :: xas => by cases x <;> simp [ExternAddr.funcs, GShift.xa, funcs_map xas]

theorem allocExport?_minst (mi : ModuleInst) (e : Export) :
    allocExport? (δ.minst mi) e = (allocExport? mi e).map δ.xinst := by
  unfold allocExport?
  rcases e with ⟨nm, ix⟩
  cases ix <;> simp [GShift.minst, Option.map_map, Function.comp_def, GShift.xinst, GShift.xa]

theorem mapM_map_some {α β : Type} (F : α → Option β) (G : α → Option β) (g : β → β)
    (h : ∀ a, G a = (F a).map g) : ∀ l : List α, l.mapM G = (l.mapM F).map (·.map g)
  | [] => rfl
  | a :: l => by
    simp only [List.mapM_cons, h, mapM_map_some F G g h l, Option.bind_eq_bind]
    cases F a with
    | none => rfl
    | some b =>
      cases l.mapM F with
      | none => rfl
      | some bs => rfl

theorem zip_map_snd {α β : Type} (l : List α) (vs : List β) (g : β → β) :
    l.zip (vs.map g) = (l.zip vs).map fun p => (p.1, g p.2) := by
  rw [List.zip_map_right]
  rfl

theorem allocMany_gap_id {α : Type} (alloc : Store H → α → Store H × Nat) (off : Nat)
    (h : ∀ t x, alloc (g.rel t) x = (g.rel (alloc t x).1, off + (alloc t x).2))
    (t : Store H) (xs : List α) :
    allocMany alloc (g.rel t) xs =
      (g.rel (allocMany alloc t xs).1, (allocMany alloc t xs).2.map (off + ·)) := by
  simpa using allocMany_gap g alloc alloc id off h t xs

/-- The addresses of the module's own functions, mapped. -/
theorem range_gap (t : Store H) (hb : g.b ≤ t.funcs.length) (n : Nat) :
    (List.range n).map ((g.rel t).funcs.length + ·) =
      ((List.range n).map (t.funcs.length + ·)).map g.sh.fn := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _
  rw [Function.comp_apply, sh_fn, fnMap_ge g (Nat.le_trans hb (Nat.le_add_right _ i)),
    rel_funcs, List.length_append, List.length_map, List.length_drop]
  omega

theorem exportsInst_minst (δ : GShift) (A₁ B₁ A₂ B₂ A₃ B₃ A₄ B₄ A₅ R : List Nat) :
    ({ tags := A₁.map (fun x => δ.tg + x) ++ B₁.map (fun x => δ.tg + x)
       globals := A₂.map (fun x => δ.gl + x) ++ B₂.map (fun x => δ.gl + x)
       mems := A₃.map (fun x => δ.me + x) ++ B₃.map (fun x => δ.me + x)
       tables := A₄.map (fun x => δ.ta + x) ++ B₄.map (fun x => δ.ta + x)
       funcs := A₅.map δ.fn ++ R.map δ.fn } : ModuleInst) =
      δ.minst { tags := A₁ ++ B₁, globals := A₂ ++ B₂, mems := A₃ ++ B₃, tables := A₄ ++ B₄
                funcs := A₅ ++ R } := by
  simp [GShift.minst]

theorem moduleInst_minst (δ : GShift) (dts : List DefType)
    (A₁ B₁ A₂ B₂ A₃ B₃ A₄ B₄ A₅ R D E : List Nat) (X : List ExportInst) :
    ({ types := dts
       tags := A₁.map (fun x => δ.tg + x) ++ B₁.map (fun x => δ.tg + x)
       globals := A₂.map (fun x => δ.gl + x) ++ B₂.map (fun x => δ.gl + x)
       mems := A₃.map (fun x => δ.me + x) ++ B₃.map (fun x => δ.me + x)
       tables := A₄.map (fun x => δ.ta + x) ++ B₄.map (fun x => δ.ta + x)
       funcs := A₅.map δ.fn ++ R.map δ.fn
       datas := D.map (fun x => δ.da + x)
       elems := E.map (fun x => δ.el + x)
       exports := X.map δ.xinst } : ModuleInst) =
      δ.minst { types := dts, tags := A₁ ++ B₁, globals := A₂ ++ B₂, mems := A₃ ++ B₃
                tables := A₄ ++ B₄, funcs := A₅ ++ R, datas := D, elems := E
                exports := X } := by
  simp [GShift.minst]

theorem allocMany_funcs_eq {α : Type} (alloc : Store H → α → Store H × Nat)
    (h : ∀ t x, (alloc t x).1.funcs = t.funcs) :
    ∀ (t : Store H) (xs : List α), (allocMany alloc t xs).1.funcs = t.funcs
  | t, [] => rfl
  | t, x :: xs => by simp only [allocMany]; rw [allocMany_funcs_eq alloc h _ xs, h]

theorem allocModule?_gap (t : Store H) (hb : g.b ≤ t.funcs.length) (m : Module)
    (xas : List ExternAddr) (valsG : List Val) (refsT : List Ref) (refsE : List (List Ref)) :
    allocModule? (g.rel t) m (xas.map g.sh.xa) (valsG.map g.sh.val)
        (refsT.map g.sh.ref) (refsE.map (·.map g.sh.ref)) =
      (allocModule? t m xas valsG refsT refsE).map
        fun p => (g.rel p.1, g.sh.minst p.2) := by
  simp only [allocModule?, Option.bind_eq_bind, zip_map_snd, range_gap g t hb,
    allocMany_gap_id g allocTag _ (allocTag_gap g),
    allocMany_gap g (fun s (p : CGlobalType × Val) => allocGlobal s p.1 p.2)
      (fun s (p : CGlobalType × Val) => allocGlobal s p.1 p.2) (fun p => (p.1, g.sh.val p.2))
      _ (fun t p => allocGlobal_gap g t p.1 p.2),
    allocMany_gap_id g allocMem _ (allocMem_gap g),
    allocMany_gap g (fun s (p : CTableType × Ref) => allocTable s p.1 p.2)
      (fun s (p : CTableType × Ref) => allocTable s p.1 p.2) (fun p => (p.1, g.sh.ref p.2))
      _ (fun t p => allocTable_gap g t p.1 p.2),
    allocMany_gap_id g allocData _ (allocData_gap g),
    allocMany_gap g (fun s (p : CRefType × List Ref) => allocElem s p.1 p.2)
      (fun s (p : CRefType × List Ref) => allocElem s p.1 p.2)
      (fun p => (p.1, p.2.map g.sh.ref)) _ (fun t p => allocElem_gap g t p.1 p.2),
    tags_map, globals_map, mems_map, tables_map, funcs_map, exportsInst_minst,
    mapM_map_some _ _ _ (allocExport?_minst g.sh _)]
  generalize m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) = T
  rcases T with _ | tagTypes
  · rfl
  simp only [Option.bind_some]
  generalize m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = F
  rcases F with _ | funcTypes
  · rfl
  simp only [Option.bind_some]
  generalize List.mapM (allocExport? _) m.exports = X
  rcases X with _ | xi
  · rfl
  simp only [Option.map_some, Option.bind_some, Option.pure_def, moduleInst_minst]
  rw [allocMany_func_gap g _ _ (by
    rw [allocMany_funcs_eq (fun s (p : CRefType × List Ref) => allocElem s p.1 p.2)
      (fun _ _ => rfl), allocMany_funcs_eq allocData (fun _ _ => rfl),
      allocMany_funcs_eq (fun s (p : CTableType × Ref) => allocTable s p.1 p.2) (fun _ _ => rfl),
      allocMany_funcs_eq allocMem (fun _ _ => rfl),
      allocMany_funcs_eq (fun s (p : CGlobalType × Val) => allocGlobal s p.1 p.2) (fun _ _ => rfl),
      allocMany_funcs_eq allocTag (fun _ _ => rfl)]
    exact hb)]

end Alloc

/-! ## Instantiation -/

section Inst

variable (g : Gap H)

theorem frame_initial (t : Store H) (hb : g.b ≤ t.funcs.length) (m : Module)
    (xas : List ExternAddr) :
    (⟨[], ModuleInst.initial (g.rel t) m (xas.map g.sh.xa)⟩ : Frame) =
      g.sh.frame ⟨[], ModuleInst.initial t m xas⟩ := by
  simp only [ModuleInst.initial, GShift.frame, GShift.minst, globals_map, funcs_map,
    range_gap g t hb, List.map_append, List.map_nil]

/-- The relocation of a configuration. -/
def relC (c : Config H) : Config H := ⟨g.rel c.store, g.sh.frame c.frame, c.code⟩

open Silmaril.Proofs.Wasm.Component.Lime1RT.Inst (evalGlobals?_funcs evalExprs?_funcs
  evalExprss?_funcs)

theorem prepare?_gap (t : Store H) (hb : g.b ≤ t.funcs.length) (m : Module)
    (xas : List ExternAddr) :
    prepare? evalConst? (g.rel t) m (xas.map g.sh.xa) =
      (prepare? evalConst? t m xas).map fun p => (relC g p.1, p.2) := by
  unfold prepare?
  split_ifs
  · rw [frame_initial g t hb, evalGlobals?_gap]
    rcases h₁ : evalGlobals? evalConst? t _ _ _ with _ | ⟨s₁, f₁, valsG⟩
    · rfl
    · simp only [Option.map_some, relG]
      rw [evalExprs?_gap]
      rcases h₂ : evalExprs? evalConst? s₁ f₁ _ with _ | ⟨s₂, f₂, refsT⟩
      · rfl
      · simp only [Option.map_some, relE]
        rw [evalExprss?_gap]
        rcases h₃ : evalExprss? evalConst? s₂ f₂ _ with _ | ⟨s₃, f₃, refsE⟩
        · rfl
        · simp only [Option.map_some, relEs]
          have hb₃ : g.b ≤ s₃.funcs.length := by
            rw [evalExprss?_funcs h₃, evalExprs?_funcs h₂, evalGlobals?_funcs h₁]
            exact hb
          rw [allocModule?_gap g s₃ hb₃]
          rcases allocModule? s₃ m xas valsG refsT refsE with _ | ⟨s₄, mi⟩ <;> rfl
  · rfl

/-- **Without segments, direct instantiation commutes with the relocation.** -/
theorem instantiateDirect?_gap (t : Store H) (hb : g.b ≤ t.funcs.length) (m : Module)
    (xas : List ExternAddr) (hseg : m.data = [] ∧ m.elems = []) :
    instantiateDirect? (g.rel t) m (xas.map g.sh.xa) =
      (instantiateDirect? t m xas).map fun p => (g.rel p.1, g.sh.frame p.2.1, p.2.2) := by
  simp only [instantiateDirect?, prepareDirect?, prepare?_gap g t hb]
  rcases prepare? evalConst? t m xas with _ | ⟨c, st⟩
  · rfl
  · simp [initSegments?, initElem?, initData?, initElemList?, initDataList?, hseg.1, hseg.2,
      relC]

theorem globalAddrs_gap (t : Store H) (k : Nat) :
    globalAddrs (g.rel t).globals.length k =
      (globalAddrs t.globals.length k).map g.sh.xa := by
  simp [globalAddrs, GShift.xa, Function.comp_def, Nat.add_assoc]

/-- **Instantiating in the shared store is instantiating alone, relocated**, for modules
without data and element segments: in `g.rel t` against the mapped external addresses,
`instantiateOnce?` gives the mapped store and frame of its run in `t`. -/
theorem instantiateOnce?_gap (t : Store H) (hb : g.b ≤ t.funcs.length) (m : Module)
    (xas : List ExternAddr) (hseg : m.data = [] ∧ m.elems = []) :
    instantiateOnce? (g.rel t) m (xas.map g.sh.xa) =
      (instantiateOnce? t m xas).map fun p => (g.rel p.1, g.sh.frame p.2.1, p.2.2) := by
  unfold instantiateOnce?
  rw [frame_initial g t hb, evalGlobals?_gap]
  rcases h₁ : evalGlobals? evalConst? t _ _ _ with _ | ⟨s₁, f₁, vs⟩
  · rfl
  · simp only [Option.map_some, relG]
    rw [globalAddrs_gap, ← List.map_append]
    exact instantiateDirect?_gap g s₁ (by rw [evalGlobals?_funcs h₁]; exact hb) _ _ hseg

end Inst
