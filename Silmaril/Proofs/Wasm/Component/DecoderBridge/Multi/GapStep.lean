module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.GapShift
public import Silmaril.Proofs.Wasm.Component.Reference.ShiftStep

/-!
# Core steps in the shared store, imports kept in place

The IR runs a later core instance of a component alone, in a store `t` whose first `b`
functions are its imports; the reference machine runs it in the shared store `g.rel t`
(`Multi.GapShift`). This file shows that host-free Core 3.0 steps commute with that map,
following `Reference.ShiftStep` (copied and adapted): `step_gap` (every profile): a host-free
step `c ⟶ c'` of a thread whose frames have module instances without tags, memories, tables,
element or data segments and whose code holds no exception or host references (`Own.FrameGood`,
`Own.CodeGood`, for any ownership) is one host-free step `gC g c ⟶ gC g c'` (store `g.rel`,
frame and code mapped by `g.sh`), when the first `b` functions of the shared store are those of
`c` (`Gap.PreOk`) and the map of function addresses is injective; `steps_gap`: runs, keeping
`Reference.SplitGood`.

* `GShift.code`: the map of administrative code (references and frames);
* lookups and updates in `g.rel t` (`rel_setGlobal`, `rel_setStructField`,
  `rel_setArrayField`) and run-time type checks (`refOk_gap_iff`);
* the families: `ParametricStep.shift`, `NumericStep.shift_eq`, `VectorStep.shift_eq`,
  `VariableStep.shift`, `RefStep.shift`, `AggregateStep.shift`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own noHost elem?_none data?_none TableStep.not_good
  MemoryStep.not_good)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Component.Reference (map_modify' append_modify' Store.app)

variable {H : Type}

namespace GShift

variable (δ : GShift)

/-- Shift administrative code: its references and frames. -/
def code : List Admin → List Admin
  | [] => []
  | .ref r :: l => .ref (δ.ref r) :: code l
  | .label n c b :: l => .label n c (code b) :: code l
  | .handler n cs b :: l => .handler n cs (code b) :: code l
  | .frame n f b :: l => .frame n (δ.frame f) (code b) :: code l
  | a :: l => a :: code l

@[simp] theorem code_nil : δ.code [] = [] := by simp [code]
@[simp] theorem code_plain (i : Instr) (l : List Admin) :
    δ.code (.plain i :: l) = .plain i :: δ.code l := by simp [code]
@[simp] theorem code_ref (r : Ref) (l : List Admin) :
    δ.code (.ref r :: l) = .ref (δ.ref r) :: δ.code l := by simp [code]
@[simp] theorem code_callRefType (d : DefType) (l : List Admin) :
    δ.code (.callRefType d :: l) = .callRefType d :: δ.code l := by simp [code]
@[simp] theorem code_returnCallRefType (d : DefType) (l : List Admin) :
    δ.code (.returnCallRefType d :: l) = .returnCallRefType d :: δ.code l := by simp [code]
@[simp] theorem code_trap (l : List Admin) : δ.code (.trap :: l) = .trap :: δ.code l := by
  simp [code]
@[simp] theorem code_label (n : Nat) (c : List Instr) (b l : List Admin) :
    δ.code (.label n c b :: l) = .label n c (δ.code b) :: δ.code l := by simp [code]
@[simp] theorem code_handler (n : Nat) (cs : List Catch) (b l : List Admin) :
    δ.code (.handler n cs b :: l) = .handler n cs (δ.code b) :: δ.code l := by simp [code]
@[simp] theorem code_frame (n : Nat) (f : Frame) (b l : List Admin) :
    δ.code (.frame n f b :: l) = .frame n (δ.frame f) (δ.code b) :: δ.code l := by simp [code]

@[simp] theorem code_append (l₁ l₂ : List Admin) :
    δ.code (l₁ ++ l₂) = δ.code l₁ ++ δ.code l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => cases a <;> simp [ih]

@[simp] theorem code_cons_toAdmin (v : Val) (l : List Admin) :
    δ.code (v.toAdmin :: l) = (δ.val v).toAdmin :: δ.code l := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, val]

@[simp] theorem code_vals (vs : List Val) : δ.code (vals vs) = vals (vs.map δ.val) := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih => simpa [vals] using ih

@[simp] theorem code_expression (es : List Instr) : δ.code (expression es) = expression es := by
  induction es with
  | nil => simp [expression]
  | cons i es ih => simpa [expression] using ih

@[simp] theorem code_map_ref (l : List Ref) :
    δ.code (l.map Admin.ref) = (l.map δ.ref).map Admin.ref := by
  induction l with
  | nil => simp
  | cons r l ih => simp [ih]

@[simp] theorem code_constI32 (b : BitVec 32) (l : List Admin) :
    δ.code (constI32 b :: l) = constI32 b :: δ.code l := by
  simp [constI32, Val.i32, Val.toAdmin]

@[simp] theorem val_i32 (b : BitVec 32) : δ.val (Val.i32 b) = Val.i32 b := rfl
@[simp] theorem ref_exn (a : Nat) : δ.ref (.exn a) = .exn (δ.ex + a) := rfl
@[simp] theorem ref_host (a : Nat) : δ.ref (.host a) = .host a := rfl
@[simp] theorem fval_val (v : Val) : δ.fval (.val v) = .val (δ.val v) := rfl
@[simp] theorem fval_pack (p : PackType) (b : BitVec p.width) :
    δ.fval (.pack p b) = .pack p b := rfl
@[simp] theorem frame_locals (f : Frame) :
    (δ.frame f).locals = f.locals.map (Option.map δ.val) := rfl

theorem code_eq_nil_iff {l : List Admin} : δ.code l = [] ↔ l = [] := by
  cases l with
  | nil => simp
  | cons a l => cases a <;> simp

theorem code_callRef {c : Admin} (hc : c.IsCallRef) (l : List Admin) :
    δ.code (c :: l) = c :: δ.code l := by
  cases c <;> simp_all [Admin.IsCallRef]

theorem code_returnCallRef {c : Admin} (hc : c.IsReturnCallRef) (l : List Admin) :
    δ.code (c :: l) = c :: δ.code l := by
  cases c <;> simp_all [Admin.IsReturnCallRef]

theorem code_retToCallIn {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst)
    (l : List Admin) : δ.code (c.retToCallIn m :: l) = c.retToCallIn m :: δ.code l := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [Admin.IsReturnCallRef, Admin.retToCallIn]
  rename_i i
  cases i <;> simp_all
  split <;> simp

theorem retToCallIn_minst (c : Admin) (m : ModuleInst) :
    c.retToCallIn (δ.minst m) = c.retToCallIn m := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp [Admin.retToCallIn]

theorem frame_forCall (m : ModuleInst) (vs : List Val) (ls : List ValType) :
    δ.frame (Frame.forCall m vs ls) = Frame.forCall (δ.minst m) (vs.map δ.val) ls := by
  simp only [frame, Frame.forCall, List.map_append, List.map_map, Frame.mk.injEq, and_true,
    minst_types]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  cases h : defaultVal? ((liftVal t).substAll (m.types.map .dt)) with
  | none => rfl
  | some v => simp [val_defaultVal δ h]

@[simp] theorem frame_setLocal (f : Frame) (x : LocalIdx) (v : Val) :
    δ.frame (f.setLocal x v) = (δ.frame f).setLocal x (δ.val v) := by
  simp [frame, Frame.setLocal, List.map_set]

theorem unpackField_fval (sx : Option Signedness) (fv : FieldVal) :
    unpackField sx (δ.fval fv) = δ.val (unpackField sx fv) := by
  rcases fv with _ | ⟨_, _⟩ <;> rcases sx with _ | ⟨_ | _⟩ <;> rfl

theorem unpackable_fval (z : CStorageType) (sx : Option Signedness) (fv : FieldVal) :
    unpackable z sx (δ.fval fv) = unpackable z sx fv := by
  rcases fv with _ | ⟨_, _⟩ <;> rcases z with _ | _ <;> rcases sx with _ | _ <;> rfl

theorem ref_injective (hi : Function.Injective δ.fn) {r₁ r₂ : Ref} (h : δ.ref r₁ = δ.ref r₂) :
    r₁ = r₂ := by
  induction r₁ generalizing r₂ with
  | extern r ih => cases r₂ <;> simp [ref] at h ⊢; exact ih h
  | func a => cases r₂ <;> simp_all [ref]; exact hi h
  | _ => cases r₂ <;> simp_all [ref]

theorem sinst_new (d : DefType) (fs : List CFieldType) (vs : List Val) :
    δ.sinst ⟨d, (fs.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩ =
      ⟨d, (fs.zip (vs.map δ.val)).map fun (ft, v) => packField (fieldStorage ft) v⟩ := by
  simp only [sinst, StructInst.mk.injEq, true_and, List.map_map, List.zip_map_right]
  apply List.map_congr_left
  rintro ⟨ft, v⟩ -
  simp [fval_packField]

theorem ainst_new (d : DefType) (z : CStorageType) (vs : List Val) :
    δ.ainst ⟨d, vs.map (packField z)⟩ = ⟨d, (vs.map δ.val).map (packField z)⟩ := by
  simp [ainst, List.map_map, Function.comp_def, fval_packField]

end GShift

/-! ## Lookups and updates in the relocated store -/

section Rel

variable (g : Gap H)

/-- **A configuration in the shared store**: its store relocated (`Gap.rel`), its frame and code
mapped. -/
def gC (c : Config H) : Config H :=
  ⟨g.rel c.store, g.sh.frame c.frame, g.sh.code c.code⟩

theorem structs_length_gap (t : Store H) :
    (g.rel t).structs.length = g.pre.structs.length + t.structs.length := by simp

theorem arrays_length_gap (t : Store H) :
    (g.rel t).arrays.length = g.pre.arrays.length + t.arrays.length := by simp

theorem rel_setGlobal (t : Store H) (a : Nat) (v : Val) :
    g.rel (t.setGlobal a v) = (g.rel t).setGlobal (g.pre.globals.length + a) (g.sh.val v) := by
  simp only [Gap.rel, Store.app, GShift.store, Store.setGlobal, Store.mk.injEq, and_true, true_and]
  rw [map_modify' g.sh.ginst (fun g => { g with value := v })
    (fun gi => { gi with value := g.sh.val v }) (fun _ => rfl), append_modify']

theorem rel_setStructField (t : Store H) (a i : Nat) (fv : FieldVal) :
    g.rel (t.setStructField a i fv) =
      (g.rel t).setStructField (g.pre.structs.length + a) i (g.sh.fval fv) := by
  simp only [Gap.rel, Store.app, GShift.store, Store.setStructField, Store.mk.injEq, and_true,
    true_and]
  rw [map_modify' _ _ (fun x => { x with fields := x.fields.set i (g.sh.fval fv) })
    (fun _ => by simp [GShift.sinst, List.map_set]), append_modify']

theorem rel_setArrayField (t : Store H) (a i : Nat) (fv : FieldVal) :
    g.rel (t.setArrayField a i fv) =
      (g.rel t).setArrayField (g.pre.arrays.length + a) i (g.sh.fval fv) := by
  simp only [Gap.rel, Store.app, GShift.store, Store.setArrayField, Store.mk.injEq, and_true,
    true_and]
  rw [map_modify' _ _ (fun x => { x with fields := x.fields.set i (g.sh.fval fv) })
    (fun _ => by simp [GShift.ainst, List.map_set]), append_modify']

theorem arrays_gap_of {t : Store H} {a : Nat} {ai : ArrayInst} (h : t.arrays[a]? = some ai) :
    (g.rel t).arrays[g.pre.arrays.length + a]? = some (g.sh.ainst ai) := by
  rw [arrays_gap, h, Option.map_some]

theorem structs_gap_of {t : Store H} {a : Nat} {si : StructInst} (h : t.structs[a]? = some si) :
    (g.rel t).structs[g.pre.structs.length + a]? = some (g.sh.sinst si) := by
  rw [structs_gap, h, Option.map_some]

theorem exns_gap_of {t : Store H} {a : Nat} {e : ExnInst} (h : t.exns[a]? = some e) :
    (g.rel t).exns[g.pre.exns.length + a]? = some (g.sh.xninst e) := by
  rw [exns_gap, h, Option.map_some]

@[simp] theorem gC_mk (s : Store H) (f : Frame) (l : List Admin) :
    gC g ⟨s, f, l⟩ = ⟨g.rel s, g.sh.frame f, g.sh.code l⟩ := rfl

/-! ### Run-time type checks -/

theorem refOk_gap {t : Store H} (hP : g.PreOk t.funcs) {r : Ref} {τ : CRefType}
    (h : RefOk t r τ) :
    RefOk (g.rel t) (g.sh.ref r) τ := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | @struct a si hs => exact RefOk.struct (si := g.sh.sinst si) (structs_gap_of g hs)
  | @array a ai ha => exact RefOk.array (ai := g.sh.ainst ai) (arrays_gap_of g ha)
  | @func a fi hf => exact RefOk.func (fi := g.sh.finst fi) (funcs_gap_of g hP hf)
  | @exn a e he => exact RefOk.exn (e := g.sh.xninst e) (exns_gap_of g he)
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih (by rwa [Ne, GShift.ref_eq_null_iff])
  | sub _ hok hs ih => exact .sub ih hok hs

theorem GShift.ref_eq_i31_inv {δ : GShift} {r : Ref} {b : BitVec 31} (h : δ.ref r = .i31 b) :
    r = .i31 b := by
  cases r <;> simp_all [GShift.ref]

theorem GShift.ref_eq_struct_inv {δ : GShift} {r : Ref} {a' : Nat} (h : δ.ref r = .struct a') :
    ∃ a, r = .struct a ∧ δ.st + a = a' := by
  cases r <;> simp_all [GShift.ref]

theorem GShift.ref_eq_array_inv {δ : GShift} {r : Ref} {a' : Nat} (h : δ.ref r = .array a') :
    ∃ a, r = .array a ∧ δ.ar + a = a' := by
  cases r <;> simp_all [GShift.ref]

theorem GShift.ref_eq_func_inv {δ : GShift} {r : Ref} {a' : Nat} (h : δ.ref r = .func a') :
    ∃ a, r = .func a ∧ δ.fn a = a' := by
  cases r <;> simp_all [GShift.ref]

theorem GShift.ref_eq_exn_inv {δ : GShift} {r : Ref} {a' : Nat} (h : δ.ref r = .exn a') :
    ∃ a, r = .exn a ∧ δ.ex + a = a' := by
  cases r <;> simp_all [GShift.ref]

theorem GShift.ref_eq_host_inv {δ : GShift} {r : Ref} {a : Nat} (h : δ.ref r = .host a) :
    r = .host a := by
  cases r <;> simp_all [GShift.ref]

theorem GShift.ref_eq_extern_inv {δ : GShift} {r r' : Ref} (h : δ.ref r = .extern r') :
    ∃ r₀, r = .extern r₀ ∧ δ.ref r₀ = r' := by
  cases r <;> simp_all [GShift.ref]

theorem refOk_gap_back {t : Store H} (hP : g.PreOk t.funcs) {r' : Ref} {τ : CRefType} (h : RefOk (g.rel t) r' τ) :
    ∀ r, g.sh.ref r = r' → RefOk t r τ := by
  induction h with
  | null =>
    intro r hr
    rw [(GShift.ref_eq_null_iff _).mp hr]
    exact .null
  | i31 b =>
    intro r hr
    rw [GShift.ref_eq_i31_inv hr]
    exact .i31 b
  | @struct a' si' hs =>
    intro r hr
    obtain ⟨a, rfl, rfl⟩ : ∃ a, r = .struct a ∧ g.sh.st + a = a' := GShift.ref_eq_struct_inv hr
    obtain ⟨si, h1, rfl⟩ : ∃ si, t.structs[a]? = some si ∧ g.sh.sinst si = si' :=
      Option.map_eq_some_iff.mp ((structs_gap g t a).symm.trans hs)
    exact RefOk.struct (si := si) h1
  | @array a' ai' hs =>
    intro r hr
    obtain ⟨a, rfl, rfl⟩ : ∃ a, r = .array a ∧ g.sh.ar + a = a' := GShift.ref_eq_array_inv hr
    obtain ⟨ai, h1, rfl⟩ : ∃ ai, t.arrays[a]? = some ai ∧ g.sh.ainst ai = ai' :=
      Option.map_eq_some_iff.mp ((arrays_gap g t a).symm.trans hs)
    exact RefOk.array (ai := ai) h1
  | @func a' fi' hf =>
    intro r hr
    obtain ⟨a, rfl, rfl⟩ : ∃ a, r = .func a ∧ g.sh.fn a = a' := GShift.ref_eq_func_inv hr
    obtain ⟨fi, h1, rfl⟩ : ∃ fi, t.funcs[a]? = some fi ∧ g.sh.finst fi = fi' :=
      Option.map_eq_some_iff.mp ((funcs_gap g hP a).symm.trans hf)
    exact RefOk.func (fi := fi) h1
  | @exn a' e' he =>
    intro r hr
    obtain ⟨a, rfl, rfl⟩ : ∃ a, r = .exn a ∧ g.sh.ex + a = a' := GShift.ref_eq_exn_inv hr
    obtain ⟨e, h1, -⟩ : ∃ e, t.exns[a]? = some e ∧ g.sh.xninst e = e' :=
      Option.map_eq_some_iff.mp ((exns_gap g t a).symm.trans he)
    exact RefOk.exn h1
  | host a =>
    intro r hr
    rw [GShift.ref_eq_host_inv hr]
    exact .host a
  | @extern r₁ _ hn ih =>
    intro r hr
    obtain ⟨r₀, rfl, rfl⟩ : ∃ r₀, r = .extern r₀ ∧ g.sh.ref r₀ = r₁ :=
      GShift.ref_eq_extern_inv hr
    exact .extern (ih r₀ rfl) (fun h0 => hn (by rw [h0]; rfl))
  | sub _ hok hs ih => intro r hr; exact .sub (ih r hr) hok hs

theorem refOk_gap_iff {t : Store H} (hP : g.PreOk t.funcs) {r : Ref} {τ : CRefType} :
    RefOk (g.rel t) (g.sh.ref r) τ ↔ RefOk t r τ :=
  ⟨fun h => refOk_gap_back g hP h r rfl, refOk_gap g hP⟩

end Rel

/-! ## The families -/

section Families

variable (g : Gap H)

@[simp] theorem ainst_fields_length (δ : GShift) (ai : ArrayInst) :
    (δ.ainst ai).fields.length = ai.fields.length := by simp [GShift.ainst]

@[simp] theorem sinst_fields_length (δ : GShift) (si : StructInst) :
    (δ.sinst si).fields.length = si.fields.length := by simp [GShift.sinst]

@[simp] theorem finst_type (δ : GShift) (fi : FuncInst H) : (δ.finst fi).type = fi.type := rfl
@[simp] theorem finst_code (δ : GShift) (fi : FuncInst H) : (δ.finst fi).code = fi.code := rfl
@[simp] theorem finst_module (δ : GShift) (fi : FuncInst H) :
    (δ.finst fi).module = δ.minst fi.module := rfl

theorem instRef_minst (δ : GShift) (m : ModuleInst) (rt : RefType) :
    (δ.minst m).instRef rt = m.instRef rt := rfl

theorem blockType?_minst (δ : GShift) (m : ModuleInst) (bt : BlockType) :
    (δ.minst m).blockType? bt = m.blockType? bt := by
  cases bt <;> rfl

theorem ParametricStep.shift {is is' : List Admin} (h : ParametricStep is is') (δ : GShift) :
    ParametricStep (δ.code is) (δ.code is') := by
  cases h with
  | unreachable => simpa using ParametricStep.unreachable
  | nop => simpa using ParametricStep.nop
  | drop v => simpa using ParametricStep.drop (δ.val v)
  | selectTrue hc => simpa using ParametricStep.selectTrue (v₁ := δ.val _) (v₂ := δ.val _) hc
  | selectFalse v₁ v₂ ts => simpa using ParametricStep.selectFalse (δ.val v₁) (δ.val v₂) ts

theorem NumericStep.shift_eq {P : Profile} {is is' : List Admin} (h : NumericStep P is is')
    (δ : GShift) : δ.code is = is ∧ δ.code is' = is' := by
  cases h <;> simp

theorem VectorStep.shift_eq {P : Profile} {is is' : List Admin} (h : VectorStep P is is')
    (δ : GShift) : δ.code is = is ∧ δ.code is' = is' := by
  cases h <;> simp

theorem VariableStep.shift {P : Profile} {c c' : Config H} (h : VariableStep c c') :
    Step P noHost (gC g c) (gC g c') := by
  cases h with
  | @localGet s f x v hl =>
    have hl' : (g.sh.frame f).local? x = some (some (g.sh.val v)) := by
      have hl₀ : f.locals[x.toNat]? = some (some v) := hl
      simp [Frame.local?, List.getElem?_map, hl₀]
    simpa [gC] using Step.variable (P := P) (host := noHost)
      (VariableStep.localGet (s := g.rel s) hl')
  | @localSet s f x v hx =>
    simpa [gC] using Step.variable (P := P) (host := noHost)
      (VariableStep.localSet (s := g.rel s) (f := g.sh.frame f) (v := g.sh.val v)
        (x := x) (by simpa using hx))
  | @localTee s f x v =>
    simpa [gC] using Step.variable (P := P) (host := noHost)
      (VariableStep.localTee (s := g.rel s) (f := g.sh.frame f) (v := g.sh.val v) (x := x))
  | @globalGet s f x a gi hg =>
    have hg' : (g.rel s).global? (g.sh.frame f) x =
        some (g.sh.gl + a, g.sh.ginst gi) := by rw [global?_gap, hg]; rfl
    simpa [gC, GShift.ginst] using Step.variable (P := P) (host := noHost)
      (VariableStep.globalGet (s := g.rel s) (f := g.sh.frame f) hg')
  | @globalSet s f x a gi v hg =>
    have hg' : (g.rel s).global? (g.sh.frame f) x =
        some (g.sh.gl + a, g.sh.ginst gi) := by rw [global?_gap, hg]; rfl
    simpa [gC, rel_setGlobal] using Step.variable (P := P) (host := noHost)
      (VariableStep.globalSet (s := g.rel s) (f := g.sh.frame f) (v := g.sh.val v) hg')

theorem RefStep.shift {P : Profile} {c c' : Config H} (h : RefStep c c')
    (hP : g.PreOk c.store.funcs) (hi : Function.Injective g.sh.fn) :
    Step P noHost (gC g c) (gC g c') := by
  cases h with
  | @refNull s f ht =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.refNull (s := g.rel s) (f := g.sh.frame f) ht)
  | @refFunc s f x a hx =>
    have hx' : (g.sh.frame f).module.funcs[x.toNat]? = some (g.sh.fn a) := by
      simp [List.getElem?_map, hx]
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.refFunc (s := g.rel s) (f := g.sh.frame f) hx')
  | @refI31 s f i =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.refI31 (s := g.rel s) (f := g.sh.frame f) i)
  | @isNullTrue s f =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.isNullTrue (s := g.rel s) (f := g.sh.frame f))
  | @isNullFalse s f r hr =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.isNullFalse (s := g.rel s) (f := g.sh.frame f) (r := g.sh.ref r)
        (by rwa [Ne, GShift.ref_eq_null_iff]))
  | @asNonNullNull s f =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.asNonNullNull (s := g.rel s) (f := g.sh.frame f))
  | @asNonNullAddr s f r hr =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.asNonNullAddr (s := g.rel s) (f := g.sh.frame f) (r := g.sh.ref r)
        (by rwa [Ne, GShift.ref_eq_null_iff]))
  | @eqNull s f =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.eqNull (s := g.rel s) (f := g.sh.frame f))
  | @eqTrue s f r hr =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.eqTrue (s := g.rel s) (f := g.sh.frame f) (r := g.sh.ref r)
        (by rwa [Ne, GShift.ref_eq_null_iff]))
  | @eqFalse s f r₁ r₂ hr =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.eqFalse (s := g.rel s) (f := g.sh.frame f) (r₁ := g.sh.ref r₁)
        (r₂ := g.sh.ref r₂) (fun e => hr (GShift.ref_injective _ hi e)))
  | @testTrue s f r rt hr =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.testTrue (s := g.rel s) (f := g.sh.frame f) (r := g.sh.ref r) (rt := rt)
        ((refOk_gap_iff g hP).mpr hr))
  | @testFalse s f r rt hr =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.testFalse (s := g.rel s) (f := g.sh.frame f) (r := g.sh.ref r) (rt := rt)
        (fun h' => hr ((refOk_gap_iff g hP).mp h')))
  | @castSucceed s f r rt hr =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.castSucceed (s := g.rel s) (f := g.sh.frame f) (r := g.sh.ref r)
        (rt := rt) ((refOk_gap_iff g hP).mpr hr))
  | @castFail s f r rt hr =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.castFail (s := g.rel s) (f := g.sh.frame f) (r := g.sh.ref r) (rt := rt)
        (fun h' => hr ((refOk_gap_iff g hP).mp h')))
  | @i31GetNull s f sx =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.i31GetNull (s := g.rel s) (f := g.sh.frame f) sx)
  | @i31GetNum s f sx i =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.i31GetNum (s := g.rel s) (f := g.sh.frame f) sx i)
  | @externConvertNull s f =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.externConvertNull (s := g.rel s) (f := g.sh.frame f))
  | @externConvertAddr s f r hr =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.externConvertAddr (s := g.rel s) (f := g.sh.frame f) (r := g.sh.ref r)
        (by rwa [Ne, GShift.ref_eq_null_iff]))
  | @anyConvertNull s f =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.anyConvertNull (s := g.rel s) (f := g.sh.frame f))
  | @anyConvertAddr s f r =>
    simpa [gC] using Step.reference (P := P) (host := noHost)
      (RefStep.anyConvertAddr (s := g.rel s) (f := g.sh.frame f) (g.sh.ref r))

end Families

section Aggregate

variable (g : Gap H)

private theorem structNew_shift {P : Profile} {s : Store H} {f : Frame} {x : TypeIdx}
    {d : DefType} {fs : Ty (.list .field)} {vs : List Val} (hd : f.type? x = some d)
    (he : Expand d (.struct fs)) (hn : vs.length = fs.length)
    (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2) :
    Step P noHost (gC g ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩)
      (gC g ⟨s.addStruct ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩,
        f, [.ref (.struct s.structs.length)]⟩) := by
  have hp' : ∀ q ∈ fs.toList.zip (vs.map g.sh.val), packable (fieldStorage q.1) q.2 := by
    intro q hq
    have hq' : q ∈ (fs.toList.zip vs).map (Prod.map id g.sh.val) := by
      simpa only [List.zip_map_right] using hq
    obtain ⟨⟨ft, v⟩, hm, hq''⟩ := List.mem_map.mp hq'
    exact hq'' ▸ by simpa [GShift.packable_val] using hp _ hm
  have hst : Step P noHost
      ⟨g.rel s, g.sh.frame f, vals (vs.map g.sh.val) ++ [.plain (.structNew x)]⟩
      ⟨(g.rel s).addStruct ⟨d, (fs.toList.zip (vs.map g.sh.val)).map
          fun (ft, v) => packField (fieldStorage ft) v⟩, g.sh.frame f,
        [.ref (.struct (g.rel s).structs.length)]⟩ :=
    Step.aggregate (AggregateStep.structNew (by simpa [type?_frame] using hd) he
      (by simpa using hn) hp')
  show Step P noHost ⟨g.rel s, g.sh.frame f, g.sh.code (vals vs ++ _)⟩
    ⟨g.rel (s.addStruct _), g.sh.frame f, g.sh.code _⟩
  rw [rel_addStruct, GShift.sinst_new, GShift.code_append, GShift.code_vals]
  simpa [structs_length_gap] using hst

private theorem arrayNewFixed_shift {P : Profile} {s : Store H} {f : Frame} {x : TypeIdx}
    {n : Fin (2 ^ 32)} {d : DefType} {ft : CFieldType} {vs : List Val}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hn : vs.length = n.val)
    (hp : ∀ v ∈ vs, packable (fieldStorage ft) v) :
    Step P noHost (gC g ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x n)]⟩)
      (gC g ⟨s.addArray ⟨d, vs.map (packField (fieldStorage ft))⟩, f,
        [arrRef s.arrays.length]⟩) := by
  have hp' : ∀ v ∈ vs.map g.sh.val, packable (fieldStorage ft) v := by
    intro v hv
    obtain ⟨w, hw, hv'⟩ := List.mem_map.mp hv
    exact hv' ▸ by simpa [GShift.packable_val] using hp w hw
  have hst : Step P noHost
      ⟨g.rel s, g.sh.frame f, vals (vs.map g.sh.val) ++ [.plain (.arrayNewFixed x n)]⟩
      ⟨(g.rel s).addArray ⟨d, (vs.map g.sh.val).map (packField (fieldStorage ft))⟩,
        g.sh.frame f, [arrRef (g.rel s).arrays.length]⟩ :=
    Step.aggregate (AggregateStep.arrayNewFixed (by simpa [type?_frame] using hd) he
      (by simpa using hn) hp')
  show Step P noHost ⟨g.rel s, g.sh.frame f, g.sh.code (vals vs ++ _)⟩
    ⟨g.rel (s.addArray _), g.sh.frame f, g.sh.code _⟩
  rw [rel_addArray, GShift.ainst_new, GShift.code_append, GShift.code_vals]
  simpa [arrays_length_gap] using hst

/-- **Aggregate steps commute with the relocation**, for frames without element and data
segments. -/
theorem AggregateStep.shift {P : Profile} {c c' : Config H} (h : AggregateStep c c')
    (he₀ : c.frame.module.elems = []) (hd₀ : c.frame.module.datas = []) :
    Step P noHost (gC g c) (gC g c') := by
  cases h with
  | structNew hd he hn hp => exact structNew_shift g hd he hn hp
  | @structNewDefault s f x d fs vs hd he hdef =>
    simpa [gC, GShift.map_val_mapM_default _ _ hdef] using Step.aggregate (P := P)
      (host := noHost) (AggregateStep.structNewDefault (s := g.rel s) (f := g.sh.frame f)
        (by simpa [type?_frame] using hd) he hdef)
  | @structGetNull s f sx x i =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.structGetNull (s := g.rel s) (f := g.sh.frame f) (sx := sx) (x := x)
        (i := i))
  | @structGetStruct s f sx x i a si fv d fs ft hs hfv hd he hi hu =>
    simpa [gC, GShift.unpackField_fval] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.structGetStruct (s := g.rel s) (f := g.sh.frame f) (sx := sx) (i := i)
        (fv := g.sh.fval fv) (structs_gap_of g hs) (by simp [GShift.sinst, hfv])
        (by simpa [type?_frame] using hd) he hi (by rwa [GShift.unpackable_fval]))
  | @structSetNull s f x i v =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.structSetNull (s := g.rel s) (f := g.sh.frame f) (x := x) (i := i)
        (v := g.sh.val v))
  | @structSetStruct s f x i v a d fs ft si hd he hi hs hfl hp =>
    simpa [gC, rel_setStructField, GShift.fval_packField] using Step.aggregate (P := P)
      (host := noHost) (AggregateStep.structSetStruct (s := g.rel s) (f := g.sh.frame f)
        (v := g.sh.val v) (by simpa [type?_frame] using hd) he hi (structs_gap_of g hs)
        (by simpa using hfl) (by rwa [GShift.packable_val]))
  | @arrayNew s f x v n =>
    simpa [gC, List.map_replicate] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayNew (s := g.rel s) (f := g.sh.frame f) (x := x) (g.sh.val v) n)
  | @arrayNewDefault s f x n d ft v hd he hv =>
    simpa [gC, List.map_replicate, GShift.val_defaultVal _ hv] using Step.aggregate (P := P)
      (host := noHost) (AggregateStep.arrayNewDefault (s := g.rel s) (f := g.sh.frame f)
        (by simpa [type?_frame] using hd) he hv)
  | arrayNewFixed hd he hn hp => exact arrayNewFixed_shift g hd he hn hp
  | arrayNewElemOob he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayNewElemAlloc he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayNewDataOob _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | arrayNewDataNum _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | @arrayGetNull s f sx x i =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayGetNull (s := g.rel s) (f := g.sh.frame f) (sx := sx) (x := x)
        (i := i))
  | @arrayGetOob s f sx x i a ai ha hl =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayGetOob (s := g.rel s) (f := g.sh.frame f) (sx := sx) (x := x)
        (arrays_gap_of g ha) (by simpa using hl))
  | @arrayGetArray s f sx x i a ai fv d ft ha hfv hd he hu =>
    simpa [gC, GShift.unpackField_fval] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayGetArray (s := g.rel s) (f := g.sh.frame f) (sx := sx) (i := i)
        (fv := g.sh.fval fv) (arrays_gap_of g ha) (by simp [GShift.ainst, hfv])
        (by simpa [type?_frame] using hd) he (by rwa [GShift.unpackable_fval]))
  | @arraySetNull s f x i v =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arraySetNull (s := g.rel s) (f := g.sh.frame f) (x := x) (i := i)
        (v := g.sh.val v))
  | @arraySetOob s f x i v a ai ha hl =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arraySetOob (s := g.rel s) (f := g.sh.frame f) (x := x)
        (v := g.sh.val v) (arrays_gap_of g ha) (by simpa using hl))
  | @arraySetArray s f x i v a ai d ft ha hl hd he hp =>
    simpa [gC, rel_setArrayField, GShift.fval_packField] using Step.aggregate (P := P)
      (host := noHost) (AggregateStep.arraySetArray (s := g.rel s) (f := g.sh.frame f)
        (v := g.sh.val v) (arrays_gap_of g ha) (by simpa using hl)
        (by simpa [type?_frame] using hd) he (by rwa [GShift.packable_val]))
  | @arrayLenNull s f =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayLenNull (s := g.rel s) (f := g.sh.frame f))
  | @arrayLenArray s f a ai ha =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayLenArray (s := g.rel s) (f := g.sh.frame f)
        (arrays_gap_of g ha))
  | @arrayFillNull s f x i n v =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayFillNull (s := g.rel s) (f := g.sh.frame f) (x := x) (i := i)
        (n := n) (v := g.sh.val v))
  | @arrayFillOob s f x i n v a ai ha hl =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayFillOob (s := g.rel s) (f := g.sh.frame f) (x := x)
        (v := g.sh.val v) (arrays_gap_of g ha) (by simpa using hl))
  | @arrayFillZero s f x i v a ai ha hl =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayFillZero (s := g.rel s) (f := g.sh.frame f) (x := x)
        (v := g.sh.val v) (arrays_gap_of g ha) (by simpa using hl))
  | @arrayFillSucc s f x i n v a ai ha hl hn =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayFillSucc (s := g.rel s) (f := g.sh.frame f) (x := x)
        (v := g.sh.val v) (arrays_gap_of g ha) (by simpa using hl) hn)
  | @arrayCopyNull₁ s f x₁ x₂ i₁ i₂ n r =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyNull₁ (s := g.rel s) (f := g.sh.frame f) (x₁ := x₁)
        (x₂ := x₂) (i₁ := i₁) (i₂ := i₂) (n := n) (r := g.sh.ref r))
  | @arrayCopyNull₂ s f x₁ x₂ i₁ i₂ n r =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyNull₂ (s := g.rel s) (f := g.sh.frame f) (x₁ := x₁)
        (x₂ := x₂) (i₁ := i₁) (i₂ := i₂) (n := n) (r := g.sh.ref r))
  | @arrayCopyOob₁ s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ha hl =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyOob₁ (s := g.rel s) (f := g.sh.frame f) (x₁ := x₁)
        (x₂ := x₂) (i₂ := i₂) (a₂ := g.pre.arrays.length + a₂) (arrays_gap_of g ha)
        (by simpa using hl))
  | @arrayCopyOob₂ s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₂ ha hl =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyOob₂ (s := g.rel s) (f := g.sh.frame f) (x₁ := x₁)
        (x₂ := x₂) (i₁ := i₁) (a₁ := g.pre.arrays.length + a₁) (arrays_gap_of g ha)
        (by simpa using hl))
  | @arrayCopyZero s f x₁ x₂ i₁ i₂ a₁ a₂ ai₁ ai₂ ha₁ ha₂ hl =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyZero (s := g.rel s) (f := g.sh.frame f) (x₁ := x₁)
        (x₂ := x₂) (arrays_gap_of g ha₁) (arrays_gap_of g ha₂) (by simpa using hl))
  | @arrayCopyLe s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ ha₁ ha₂ hl hn hd he hle =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyLe (s := g.rel s) (f := g.sh.frame f)
        (arrays_gap_of g ha₁) (arrays_gap_of g ha₂) (by simpa using hl) hn
        (by simpa [type?_frame] using hd) he hle)
  | @arrayCopyGt s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ ha₁ ha₂ hl hn hd he hgt =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyGt (s := g.rel s) (f := g.sh.frame f)
        (arrays_gap_of g ha₁) (arrays_gap_of g ha₂) (by simpa using hl) hn
        (by simpa [type?_frame] using hd) he hgt)
  | @arrayInitElemNull s f x y i j n =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayInitElemNull (s := g.rel s) (f := g.sh.frame f) (x := x) (y := y)
        (i := i) (j := j) (n := n))
  | @arrayInitElemOob₁ s f x y i j n a ai ha hl =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayInitElemOob₁ (s := g.rel s) (f := g.sh.frame f) (x := x) (y := y)
        (j := j) (arrays_gap_of g ha) (by simpa using hl))
  | arrayInitElemOob₂ he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayInitElemZero _ he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayInitElemSucc _ he => exact nomatch (elem?_none he₀).symm.trans he
  | @arrayInitDataNull s f x y i j n =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayInitDataNull (s := g.rel s) (f := g.sh.frame f) (x := x) (y := y)
        (i := i) (j := j) (n := n))
  | @arrayInitDataOob₁ s f x y i j n a ai ha hl =>
    simpa [gC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayInitDataOob₁ (s := g.rel s) (f := g.sh.frame f) (x := x) (y := y)
        (j := j) (arrays_gap_of g ha) (by simpa using hl))
  | arrayInitDataOob₂ _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | arrayInitDataZero _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | arrayInitDataNum _ _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat

end Aggregate

/-! ## One step -/

section Main

variable (g : Gap H)

set_option linter.unusedTactic false in
/-- **A host-free Core step commutes with the map into the shared store**, for threads whose module
instances have no tags, memories, tables, element or data segments and whose code holds no
exception or host references (for any ownership `O`). -/
theorem step_gap {P : Profile} {c c' : Config H} (h : Step P noHost c c') {O : Own} :
    O.FrameGood c.frame → O.CodeGood c.code → g.PreOk c.store.funcs →
      Function.Injective g.sh.fn → Step P noHost (gC g c) (gC g c') := by
  induction h with
  | parametric h =>
    intro _ _ hP hinj
    exact Step.parametric (ParametricStep.shift h g.sh)
  | numeric h =>
    intro _ _ hP hinj
    obtain ⟨e1, e2⟩ : g.sh.code _ = _ ∧ g.sh.code _ = _ := NumericStep.shift_eq h g.sh
    simp only [gC, e1, e2]
    exact .numeric h
  | vector h =>
    intro _ _ hP hinj
    obtain ⟨e1, e2⟩ : g.sh.code _ = _ ∧ g.sh.code _ = _ := VectorStep.shift_eq h g.sh
    simp only [gC, e1, e2]
    exact .vector h
  | «variable» h => intro _ _ hP hinj; exact VariableStep.shift g h
  | table h => intro hf _ hP hinj; exact (TableStep.not_good h hf).elim
  | memory h => intro hf _ hP hinj; exact (MemoryStep.not_good h hf).elim
  | reference h => intro _ _ hP hinj; exact RefStep.shift g h hP hinj
  | aggregate h => intro hf _ hP hinj; exact AggregateStep.shift g h hf.1.elems hf.1.datas
  | @ctxtInstrs s s' f f' vs is is' rest _ hne ih =>
    intro hf hc hP hinj
    have hci : O.CodeGood is := (O.codeGood_append.mp (O.codeGood_append.mp hc).1).2
    have hst : Step P noHost (gC g ⟨s, f, is⟩) (gC g ⟨s', f', is'⟩) := ih hf hci hP hinj
    simp only [gC, GShift.code_append, GShift.code_vals]
    exact Step.ctxtInstrs hst (by simpa [GShift.code_eq_nil_iff] using hne)
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    intro hf hc hP hinj
    have hst : Step P noHost (gC g ⟨s, f, is⟩) (gC g ⟨s', f', is'⟩) :=
      ih hf ((O.codeGood_single_label ..).mp hc) hP hinj
    simpa using Step.ctxtLabel (n := n) (cont := cont) hst
  | @ctxtHandler s s' f f' n cs is is' _ ih =>
    intro hf hc hP hinj
    have hst : Step P noHost (gC g ⟨s, f, is⟩) (gC g ⟨s', f', is'⟩) :=
      ih hf ((O.codeGood_single_handler ..).mp hc) hP hinj
    simpa using Step.ctxtHandler (n := n) (cs := cs) hst
  | @ctxtFrame s s' f fi fi' n is is' _ ih =>
    intro hf hc hP hinj
    obtain ⟨hfi, hcb⟩ : O.FrameGood fi ∧ O.CodeGood is := (O.codeGood_single_frame ..).mp hc
    have hst : Step P noHost (gC g ⟨s, fi, is⟩) (gC g ⟨s', fi', is'⟩) := ih hfi hcb hP hinj
    simpa using Step.ctxtFrame (f := g.sh.frame f) (n := n) hst
  | @block s f bt body vs t₁ t₂ hbt hm =>
    intro _ _ hP hinj
    simpa [gC] using Step.block (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (vs := vs.map g.sh.val) (body := body)
      (by rwa [GShift.frame_module, blockType?_minst]) (by simpa using hm)
  | @loop s f bt body vs t₁ t₂ hbt hm =>
    intro _ _ hP hinj
    simpa [gC] using Step.loop (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (vs := vs.map g.sh.val) (body := body)
      (by rwa [GShift.frame_module, blockType?_minst]) (by simpa using hm)
  | @ifTrue s f c bt b₁ b₂ hc0 =>
    intro _ _ hP hinj
    simpa [gC] using Step.ifTrue (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (bt := bt) (b₁ := b₁) (b₂ := b₂) hc0
  | @ifFalse s f bt b₁ b₂ =>
    intro _ _ hP hinj
    simpa [gC] using Step.ifFalse (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (bt := bt) (b₁ := b₁) (b₂ := b₂)
  | @labelVals s f n cont vs =>
    intro _ _ hP hinj
    simpa [gC] using Step.labelVals (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (n := n) (cont := cont) (vs := vs.map g.sh.val)
  | @brLabelZero s f n cont vs' vs l rest hl hn =>
    intro _ _ hP hinj
    simpa [gC] using Step.brLabelZero (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (cont := cont) (vs' := vs'.map g.sh.val)
      (vs := vs.map g.sh.val) (rest := g.sh.code rest) hl (by simpa using hn)
  | @brLabelSucc s f n cont vs l rest hl =>
    intro _ _ hP hinj
    simpa [gC] using Step.brLabelSucc (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (n := n) (cont := cont) (vs := vs.map g.sh.val)
      (rest := g.sh.code rest) hl
  | @brHandler s f n cs vs l rest =>
    intro _ _ hP hinj
    simpa [gC] using Step.brHandler (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (n := n) (cs := cs) (vs := vs.map g.sh.val) (l := l)
      (rest := g.sh.code rest)
  | @brIfTrue s f c l hc0 =>
    intro _ _ hP hinj
    simpa [gC] using Step.brIfTrue (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l := l) hc0
  | @brIfFalse s f l =>
    intro _ _ hP hinj
    simpa [gC] using Step.brIfFalse (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l := l)
  | @brTableLt s f i ls l' l hi =>
    intro _ _ hP hinj
    simpa [gC] using Step.brTableLt (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l' := l') hi
  | @brTableGe s f i ls l' hi =>
    intro _ _ hP hinj
    simpa [gC] using Step.brTableGe (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l' := l') hi
  | @brOnNullNull s f l =>
    intro _ _ hP hinj
    simpa [gC] using Step.brOnNullNull (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l := l)
  | @brOnNullAddr s f v l hv =>
    intro _ _ hP hinj
    have hv' : g.sh.val v ≠ .ref .null := by
      cases v <;> simp_all [GShift.ref_eq_null_iff]
    simpa [gC] using Step.brOnNullAddr (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l := l) hv'
  | @brOnNonNullNull s f l =>
    intro _ _ hP hinj
    simpa [gC] using Step.brOnNonNullNull (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l := l)
  | @brOnNonNullAddr s f v l hv =>
    intro _ _ hP hinj
    have hv' : g.sh.val v ≠ .ref .null := by
      cases v <;> simp_all [GShift.ref_eq_null_iff]
    simpa [gC] using Step.brOnNonNullAddr (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l := l) hv'
  | @brOnCastSucceed s f r l rt₁ rt₂ hr =>
    intro _ _ hP hinj
    simpa [gC] using Step.brOnCastSucceed (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l := l) (rt₁ := rt₁) (r := g.sh.ref r) (rt₂ := rt₂)
      ((refOk_gap_iff g hP).mpr hr)
  | @brOnCastFail s f r l rt₁ rt₂ hr =>
    intro _ _ hP hinj
    simpa [gC] using Step.brOnCastFail (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l := l) (rt₁ := rt₁) (r := g.sh.ref r) (rt₂ := rt₂)
      (fun h' => hr ((refOk_gap_iff g hP).mp h'))
  | @brOnCastFailSucceed s f r l rt₁ rt₂ hr =>
    intro _ _ hP hinj
    simpa [gC] using Step.brOnCastFailSucceed (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l := l) (rt₁ := rt₁) (r := g.sh.ref r) (rt₂ := rt₂)
      ((refOk_gap_iff g hP).mpr hr)
  | @brOnCastFailFail s f r l rt₁ rt₂ hr =>
    intro _ _ hP hinj
    simpa [gC] using Step.brOnCastFailFail (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (l := l) (rt₁ := rt₁) (r := g.sh.ref r) (rt₂ := rt₂)
      (fun h' => hr ((refOk_gap_iff g hP).mp h'))
  | @call s f x a fi hx hfi =>
    intro _ _ hP hinj
    simpa [gC] using Step.call (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (x := x) (by simp [List.getElem?_map, hx]) (funcs_gap_of g hP hfi)
  | @callRefNull s f c hcr =>
    intro _ _ hP hinj
    simpa [gC, GShift.code_callRef _ hcr] using Step.callRefNull (P := P) (host := noHost)
      (s := g.rel s) (f := g.sh.frame f) hcr
  | @callRefFunc s f c vs a fi ps rs code hcr hfi he hn hcode =>
    intro _ _ hP hinj
    simpa [gC, GShift.code_callRef _ hcr, GShift.frame_forCall] using
      Step.callRefFunc (P := P) (host := noHost) (s := g.rel s) (f := g.sh.frame f)
        (vs := vs.map g.sh.val) hcr (funcs_gap_of g hP hfi) he (by simpa using hn) hcode
  | callRefHost _ _ _ _ _ hhost => intro _ _ hP hinj; exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => intro _ _ hP hinj; exact hhost.elim
  | @returnCall s f x a fi hx hfi =>
    intro _ _ hP hinj
    simpa [gC] using Step.returnCall (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (x := x) (by simp [List.getElem?_map, hx]) (funcs_gap_of g hP hfi)
  | @returnCallRefLabel s f k cont vs c rest hcr =>
    intro _ _ hP hinj
    simpa [gC, GShift.code_returnCallRef _ hcr] using
      Step.returnCallRefLabel (P := P) (host := noHost) (s := g.rel s) (f := g.sh.frame f)
        (k := k) (cont := cont) (vs := vs.map g.sh.val) (rest := g.sh.code rest) hcr
  | @returnCallRefHandler s f k cs vs c rest hcr =>
    intro _ _ hP hinj
    simpa [gC, GShift.code_returnCallRef _ hcr] using
      Step.returnCallRefHandler (P := P) (host := noHost) (s := g.rel s)
        (f := g.sh.frame f) (k := k) (cs := cs) (vs := vs.map g.sh.val)
        (rest := g.sh.code rest) hcr
  | @returnCallRefFrameNull s f fi k vs c rest hcr =>
    intro _ _ hP hinj
    simpa [gC, GShift.code_returnCallRef _ hcr] using
      Step.returnCallRefFrameNull (P := P) (host := noHost) (s := g.rel s)
        (f := g.sh.frame f) (fi := g.sh.frame fi) (k := k) (vs := vs.map g.sh.val)
        (rest := g.sh.code rest) hcr
  | @returnCallRefFrameAddr s f fi k vs' vs a c rest fn ps rs hcr hfn he hn =>
    intro _ _ hP hinj
    simpa [gC, GShift.code_returnCallRef _ hcr, GShift.code_retToCallIn _ hcr,
      GShift.retToCallIn_minst] using Step.returnCallRefFrameAddr (P := P) (host := noHost)
        (s := g.rel s) (f := g.sh.frame f) (fi := g.sh.frame fi) (k := k)
        (vs' := vs'.map g.sh.val) (vs := vs.map g.sh.val) (rest := g.sh.code rest) hcr
        (funcs_gap_of g hP hfn) he (by simpa using hn)
  | @callIndirect s f x y =>
    intro _ _ hP hinj
    simpa [gC] using Step.callIndirect (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (x := x) (y := y)
  | @returnCallIndirect s f x y =>
    intro _ _ hP hinj
    simpa [gC] using Step.returnCallIndirect (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (x := x) (y := y)
  | @frameVals s f fi n vs hn =>
    intro _ _ hP hinj
    simpa [gC] using Step.frameVals (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (fi := g.sh.frame fi) (vs := vs.map g.sh.val)
      (by simpa using hn)
  | @returnFrame s f fi n vs' vs rest hn =>
    intro _ _ hP hinj
    simpa [gC] using Step.returnFrame (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (fi := g.sh.frame fi) (vs' := vs'.map g.sh.val)
      (vs := vs.map g.sh.val) (rest := g.sh.code rest) (by simpa using hn)
  | @returnLabel s f n cont vs rest =>
    intro _ _ hP hinj
    simpa [gC] using Step.returnLabel (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (n := n) (cont := cont) (vs := vs.map g.sh.val)
      (rest := g.sh.code rest)
  | @returnHandler s f n cs vs rest =>
    intro _ _ hP hinj
    simpa [gC] using Step.returnHandler (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (n := n) (cs := cs) (vs := vs.map g.sh.val)
      (rest := g.sh.code rest)
  | throw ht =>
    intro hf _ hP hinj
    exact absurd ht (by simp [Silmaril.Proofs.Wasm.Game.Linking.Split.tag?_none hf.1.tags])
  | @throwRefNull s f =>
    intro _ _ hP hinj
    simpa [gC] using Step.throwRefNull (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f)
  | throwRefInstrs _ =>
    intro _ hc hP hinj
    exact (Own.not_codeGood_throwing hc (by simp [throwing]; exact .inr (.inl rfl))).elim
  | throwRefLabel =>
    intro _ hc hP hinj
    exact (Own.not_codeGood_throwing ((O.codeGood_single_label ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefFrame =>
    intro _ hc hP hinj
    exact (Own.not_codeGood_throwing ((O.codeGood_single_frame ..).mp hc).2
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerEmpty =>
    intro _ hc hP hinj
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatch _ _ =>
    intro _ hc hP hinj
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatchRef _ _ =>
    intro _ hc hP hinj
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatchAll =>
    intro _ hc hP hinj
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatchAllRef =>
    intro _ hc hP hinj
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerNext _ =>
    intro _ hc hP hinj
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | @tryTable s f bt cs body vs t₁ t₂ hbt hm =>
    intro _ _ hP hinj
    simpa [gC] using Step.tryTable (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (cs := cs) (body := body) (vs := vs.map g.sh.val)
      (by rwa [GShift.frame_module, blockType?_minst]) (by simpa using hm)
  | @handlerVals s f n cs vs =>
    intro _ _ hP hinj
    simpa [gC] using Step.handlerVals (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (n := n) (cs := cs) (vs := vs.map g.sh.val)
  | @trapInstrs s f vs rest hne =>
    intro _ _ hP hinj
    simpa [gC] using Step.trapInstrs (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (vs := vs.map g.sh.val) (rest := g.sh.code rest)
      (by simpa [GShift.code_eq_nil_iff] using hne)
  | @trapLabel s f n cont =>
    intro _ _ hP hinj
    simpa [gC] using Step.trapLabel (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (n := n) (cont := cont)
  | @trapHandler s f n cs =>
    intro _ _ hP hinj
    simpa [gC] using Step.trapHandler (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (n := n) (cs := cs)
  | @trapFrame s f fi n =>
    intro _ _ hP hinj
    simpa [gC] using Step.trapFrame (P := P) (host := noHost) (s := g.rel s)
      (f := g.sh.frame f) (fi := g.sh.frame fi) (n := n)

end Main

/-! ## Runs -/

section Runs

open Silmaril.Proofs.Wasm.Game.Linking.Split (PartRel step_sim)
open Silmaril.Proofs.Wasm.Component.Reference (SplitGood SplitGood.step)

variable (g : Gap H)

/-- **Host-free runs of the split fragment commute with the map into the shared store.** -/
theorem steps_gap {P : Profile} {c c' : Config H}
    (h : Relation.ReflTransGen (Step P noHost) c c') (hg : SplitGood c)
    (hP : g.PreOk c.store.funcs) (hinj : Function.Injective g.sh.fn) :
    Relation.ReflTransGen (Step P noHost) (gC g c) (gC g c') ∧ SplitGood c' ∧
      c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => exact ⟨.refl, hg, rfl⟩
  | tail _ hst ih =>
    obtain ⟨hrun, hg₁, hfs⟩ := ih
    obtain ⟨ρ, O, σ, hR, hf, hc⟩ := hg₁
    have hfs' := (Silmaril.Wasm.SingleThreaded.Step.framesLocal hst).1
    exact ⟨hrun.tail (step_gap g hst hf hc (by rw [hfs]; exact hP) hinj),
      SplitGood.step hst ⟨ρ, O, σ, hR, hf, hc⟩, hfs'.trans hfs⟩

end Runs

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
