module

public import SqliteWasm.WholeModule
public import SqliteWasmArtifactEntries
public import Silmaril.Wasm.Execution.Core.Instantiation
import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (DefType Expand)
open SqliteWasmArtifact (definedFunction?)

set_option maxRecDepth 65536
set_option maxHeartbeats 400000

private theorem mappedIndex {A B : Type} (get : A → Option B) :
    ∀ {xs : List A} {ys : List B} {i : Nat} {x : A} {y : B},
      xs.mapM get = some ys → xs[i]? = some x → get x = some y → ys[i]? = some y
  := by
    intro xs
    induction xs with
    | nil => intro ys i x y hm hx hg; simp at hx
    | cons a as ih =>
      intro ys i x y hm hx hg
      have hm' : (get a).bind (fun b => (as.mapM get).bind (fun bs => some (b :: bs))) =
          some ys := by simpa only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] using hm
      obtain ⟨b, hb, rest⟩ := Option.bind_eq_some_iff.mp hm'
      obtain ⟨bs, hs, same⟩ := Option.bind_eq_some_iff.mp rest
      have hy : b :: bs = ys := Option.some.inj same
      subst ys
      cases i with
      | zero =>
        have hax : a = x := Option.some.inj hx
        subst x
        exact hb.symm.trans hg
      | succ i =>
        change bs[i]? = some y
        exact ih (ys := bs) (i := i) hs hx hg

private theorem getAllocatedFunction {H : Type} {s allocated : Store H} {mi : ModuleInst}
    {m : Module} {imports : List ExternAddr} {globals : List Val} {tables : List Ref}
    {elements : List (List Ref)} {ordinal : Nat} {fn : Func} {d : DefType}
    (allocatedModule : allocModule? s m imports globals tables elements = some (allocated, mi))
    (functionAt : m.funcs[ordinal]? = some fn)
    (typeAt : (allocTypes m.types)[fn.type.toNat]? = some d) :
    mi.funcs[(ExternAddr.funcs imports).length + ordinal]? = some (s.funcs.length + ordinal) ∧
    allocated.funcs[s.funcs.length + ordinal]? = some ⟨d, mi, .wasm fn⟩ := by
  obtain ⟨_, types, _, _, allTypes, _, instanceEq, storeEq⟩ := allocModule?_inv allocatedModule
  have inRange := (List.getElem?_eq_some_iff.mp functionAt).1
  have lookup := mappedIndex (fun f : Func => (allocTypes m.types)[f.type.toNat]?)
    allTypes functionAt typeAt
  have zipped : (types.zip m.funcs)[ordinal]? = some (d, fn) :=
    List.getElem?_zip_eq_some.mpr ⟨lookup, functionAt⟩
  constructor
  · rw [instanceEq]
    change ((ExternAddr.funcs imports) ++ (List.range m.funcs.length).map (s.funcs.length + ·))[(ExternAddr.funcs imports).length + ordinal]? = _
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_map,
      List.getElem?_range inRange]
    rfl
  · rw [storeEq]
    change (s.funcs ++ (types.zip m.funcs).map (fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H)))[s.funcs.length + ordinal]? = _
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_map, zipped]
    rfl

private def constructor : Func := (definedFunction? sqlite 23).get rfl
private def initializerEntry : Func := (definedFunction? sqlite 25).get rfl
private def setupEntry : Func := (definedFunction? sqlite 1516).get rfl

private def constructorType : DefType := ((allocTypes sqlite.types)[constructor.type.toNat]?).get rfl
private def initializerType : DefType := ((allocTypes sqlite.types)[initializerEntry.type.toNat]?).get rfl
private def setupType : DefType := ((allocTypes sqlite.types)[setupEntry.type.toNat]?).get rfl

private theorem constructorExpanded : Expand constructorType (.func .nil .nil) := .mk rfl
private theorem initializerExpanded : Expand initializerType (.func .nil .nil) := .mk rfl
private theorem setupExpanded : Expand setupType (.func .nil .nil) := .mk rfl

/-- The function entry at a reactor slot binds the named definition and its runtime signature. -/
def StartupBinding {H : Type} (allocated : Store H) (mi : ModuleInst) (slot : Nat) (fn : Func) :
    Prop :=
  ∃ address fi, mi.funcs[slot]? = some address ∧ allocated.funcs[address]? = some fi ∧
    fi.module = mi ∧ fi.code = .wasm fn ∧ Expand fi.type (.func .nil .nil)

private theorem bindReactorSlot {H : Type} {s allocated : Store H} {mi : ModuleInst}
    {imports : List ExternAddr} {globals : List Val} {tables : List Ref}
    {elements : List (List Ref)} {ordinal : Nat} {fn : Func} {d : DefType}
    (alloc : allocModule? s sqlite imports globals tables elements = some (allocated, mi))
    (imported : (ExternAddr.funcs imports).length = 23)
    (functionAt : sqlite.funcs[ordinal]? = some fn)
    (typeAt : (allocTypes sqlite.types)[fn.type.toNat]? = some d)
    (expand : Expand d (.func .nil .nil)) :
    StartupBinding allocated mi (23 + ordinal) fn := by
  obtain ⟨slot, entry⟩ := getAllocatedFunction alloc functionAt typeAt
  rw [imported] at slot
  exact ⟨_, _, slot, entry, rfl, rfl, expand⟩

/-- Allocation of the pinned reactor binds its three startup functions when the supplied
address list has the reactor's 23 function imports. -/
theorem allocatedStartupBindings {H : Type} {s allocated : Store H} {mi : ModuleInst}
    {imports : List ExternAddr} {globals : List Val} {tables : List Ref} {elements : List (List Ref)}
    (alloc : allocModule? s sqlite imports globals tables elements = some (allocated, mi))
    (imported : (ExternAddr.funcs imports).length = 23) :
    StartupBinding allocated mi 23 ((definedFunction? sqlite 23).get rfl) ∧
    StartupBinding allocated mi 25 ((definedFunction? sqlite 25).get rfl) ∧
    StartupBinding allocated mi 1516 ((definedFunction? sqlite 1516).get rfl) := by
  exact ⟨bindReactorSlot (ordinal := 0) alloc imported rfl rfl constructorExpanded,
    bindReactorSlot (ordinal := 2) alloc imported rfl rfl initializerExpanded,
    bindReactorSlot (ordinal := 1493) alloc imported rfl rfl setupExpanded⟩

private theorem allocExport_extra (view : ModuleInst) (types : List DefType)
    (data elements : List Nat) (exports : List ExportInst) :
    allocExport? { view with types := types, datas := data, elems := elements, exports := exports } =
      allocExport? view := by
  funext e
  unfold allocExport?
  cases e.index <;> rfl

private theorem allocatedExports {H : Type} {s allocated : Store H} {m : Module} {mi : ModuleInst}
    {imports : List ExternAddr} {globals : List Val} {tables : List Ref} {elements : List (List Ref)}
    (alloc : allocModule? s m imports globals tables elements = some (allocated, mi)) :
    m.exports.mapM (allocExport? mi) = some mi.exports := by
  obtain ⟨tagTypes, _, xi, _, _, built, view, _⟩ := allocModule?_inv alloc
  let baseView : ModuleInst :=
    { tags := ExternAddr.tags imports ++ List.range' s.tags.length tagTypes.length,
      globals := ExternAddr.globals imports ++ List.range' s.globals.length (min m.globals.length globals.length),
      mems := ExternAddr.mems imports ++ List.range' s.mems.length m.memories.length,
      tables := ExternAddr.tables imports ++ List.range' s.tables.length (min m.tables.length tables.length),
      funcs := ExternAddr.funcs imports ++ (List.range m.funcs.length).map (s.funcs.length + ·) }
  have shape : mi =
      { baseView with
        types := allocTypes m.types
        datas := List.range' s.datas.length m.data.length
        elems := List.range' s.elems.length (min m.elems.length elements.length)
        exports := xi } := view
  rw [shape, allocExport_extra baseView]
  exact built

theorem allocatedInitializeExport {H : Type} {s allocated : Store H} {mi : ModuleInst}
    {imports : List ExternAddr} {globals : List Val} {tables : List Ref} {elements : List (List Ref)}
    (alloc : allocModule? s sqlite imports globals tables elements = some (allocated, mi))
    (imported : (ExternAddr.funcs imports).length = 23) :
    ∃ address fi, mi.exports.find? (·.name == "_initialize") =
      some ⟨"_initialize", .func address⟩ ∧
      mi.funcs[25]? = some address ∧ allocated.funcs[address]? = some fi ∧
      fi.module = mi ∧ fi.code = .wasm ((definedFunction? sqlite 25).get rfl) ∧
      Expand fi.type (.func .nil .nil) := by
  obtain ⟨_, init, _⟩ := allocatedStartupBindings alloc imported
  obtain ⟨address, fi, slot, entry, instanceEq, code, expanded⟩ := init
  have built := allocatedExports alloc
  have leading : sqlite.exports =
      ⟨"memory", .memory ⟨0⟩⟩ :: ⟨"_initialize", .func ⟨25⟩⟩ :: sqlite.exports.drop 2 := rfl
  have initBuilt : allocExport? mi ⟨"_initialize", .func ⟨25⟩⟩ =
      some ⟨"_initialize", .func address⟩ := by
    change (mi.funcs[25]?.map ExternAddr.func).map (ExportInst.mk "_initialize") = _
    rw [slot]
    rfl
  rw [leading] at built
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, initBuilt, Option.bind_some] at built
  obtain ⟨memory, memoryBuilt, tail⟩ := Option.bind_eq_some_iff.mp built
  have explicit : (((sqlite.exports.drop 2).mapM (allocExport? mi)).bind fun other =>
      some (memory :: ⟨"_initialize", .func address⟩ :: other)) = some mi.exports := by
    simpa only [Option.bind_assoc, Option.bind_some] using tail
  obtain ⟨other, _, all⟩ := Option.bind_eq_some_iff.mp explicit
  have exportsEq : memory :: ⟨"_initialize", .func address⟩ :: other = mi.exports := Option.some.inj all
  have memoryName : memory.name = "memory" := by
    unfold allocExport? at memoryBuilt
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp memoryBuilt
    rfl
  refine ⟨address, fi, ?_, slot, entry, instanceEq, code, expanded⟩
  rw [← exportsEq]
  simp [memoryName]


end SqliteWasm
