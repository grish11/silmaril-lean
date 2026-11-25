module

public import SqliteWasm.IntrinsicInitializer
public import SqliteWasm.InitializerFlag
public import SqliteWasm.ThreadSetup
public import SqliteWasm.StartupBindings
import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs

@[expose] public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (CGlobalType Expand)

set_option maxRecDepth 65536
set_option maxHeartbeats 400000

def initializerAddress (base : BitVec 32) : Nat := (base + 59328#32).toNat

def initializerMark (mem : MemInst) (base : BitVec 32) : MemInst :=
  { mem with bytes := Memory.writeSlice mem.bytes (initializerAddress base) (Memory.encodeLE 4 1) }

private theorem markSize (mem : MemInst) (base : BitVec 32)
    (zero : Memory.load mem.bytes (initializerAddress base) 4 = some 0) :
    (initializerMark mem base).bytes.size = mem.bytes.size := by
  have bound : initializerAddress base + 4 ≤ mem.bytes.size := by
    by_contra! out
    unfold Memory.load Memory.readBytes at zero
    rw [ite_eq_right (show ¬ initializerAddress base + 4 ≤ mem.bytes.size by omega)] at zero
    cases zero
  apply Memory.writeBytes_size mem.bytes (Memory.encodeLE 4 1) _ (initializerAddress base)
  simp [Memory.writeBytes, initializerMark, bound]

private theorem markedLookup {H : Type} {s : Store H} {f : Frame} {address : Nat} {mem : MemInst}
    {base : BitVec 32} (entry : s.mems[address]? = some mem)
    (mapping : f.module.mems[0]? = some address) :
    (s.setMem address (initializerMark mem base)).mem? f ⟨0⟩ =
      some (address, initializerMark mem base) := by
  change (f.module.mems[(0 : Nat)]?.bind fun a =>
    (s.mems.set address (initializerMark mem base))[a]?.bind fun m => some (a, m)) = _
  rw [mapping, Option.bind_some, List.getElem?_set_self (List.getElem?_eq_some_iff.mp entry).1]
  rfl

private theorem setSameMemory {H : Type} (s : Store H) (a : Nat) (mem mem' : MemInst) :
    (s.setMem a mem).setMem a mem' = s.setMem a mem' := by
  simp [Store.setMem, List.set_set]

theorem originalSetupDeclarations :
    (Binary.Core.decode? originalBytes.toByteArray).map (fun m =>
      (m.imports.all (fun i => match i.type with | .func _ => true | _ => false),
        m.globals[1]?.map Global.init,
        m.memories.map fun memory => (memory.address, memory.limits.min.val))) =
      some (true, some [.intConst .i32 0], [(.i32, 2)]) := by
  rw [originalDecode]
  rfl

theorem initializerSignature : sqlite.functionSignature? ⟨25⟩ = some ⟨[], []⟩ := rfl

private theorem enterInvocation {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {a : Nat} {fi : FuncInst H} {fn : Func}
    (entry : s.funcs[a]? = some fi) (code : fi.code = .wasm fn)
    (signature : Expand fi.type (.func .nil .nil)) :
    Step P host (invoke s a [])
      ⟨s, {}, [.frame 0 (Frame.forCall fi.module [] fn.locals)
        [.label 0 [] (expression fn.body)]]⟩ := by
  unfold invoke
  rw [entry]
  exact Step.callRefFunc (c := .callRefType fi.type) (vs := []) trivial entry signature rfl code

/-- Successful execution of the linked reactor initializer when its flag is zero. The two
Wasm callees resolve as specified, and the initializer and setup call select the same memory. -/
theorem initializerReturns {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {init thread ctor : FuncInst H}
    {aInit aThread aCtor aMem aGlobal : Nat} {mem : MemInst} {base : BitVec 32}
    {globalType : CGlobalType}
    (initSlot : caller.module.funcs[25]? = some aInit)
    (initEntry : s.funcs[aInit]? = some init) (initCode : init.code = .wasm initializerFunction)
    (initType : Expand init.type (.func .nil .nil))
    (threadSlot : init.module.funcs[1516]? = some aThread)
    (threadEntry : s.funcs[aThread]? = some thread) (threadCode : thread.code = .wasm threadSetupFunction)
    (threadType : Expand thread.type (.func .nil .nil))
    (ctorSlot : init.module.funcs[23]? = some aCtor)
    (ctorEntry : s.funcs[aCtor]? = some ctor) (ctorCode : ctor.code = .wasm initializerConstructor)
    (ctorType : Expand ctor.type (.func .nil .nil))
    (initMem : init.module.mems[0]? = some aMem) (threadMem : thread.module.mems[0]? = some aMem)
    (memEntry : s.mems[aMem]? = some mem)
    (global : s.global? (Frame.forCall init.module [] initializerFunction.locals) ⟨1⟩ =
      some (aGlobal, ⟨globalType, .i32 base⟩))
    (zero : Memory.load mem.bytes (initializerAddress base) 4 = some 0)
    (bound : 59984 ≤ mem.bytes.size) :
    ∃ word : BitVec 32, Memory.load (initializerMark mem base).bytes 59892 4 = some word ∧
      Steps P host ⟨s, caller, [.plain (.call ⟨25⟩)]⟩
        ⟨s.setMem aMem (threadSetupMemory (initializerMark mem base) word), caller, []⟩ ∧
      Steps P host (invoke s aInit [])
        ⟨s.setMem aMem (threadSetupMemory (initializerMark mem base) word), {}, []⟩ := by
  let f := Frame.forCall init.module [] initializerFunction.locals
  let marked := initializerMark mem base
  let markedStore := s.setMem aMem marked
  have mapped : s.mem? f ⟨0⟩ = some (aMem, mem) := by
    change (init.module.mems[0]?.bind fun a => s.mems[a]?.bind fun m => some (a, m)) = _
    rw [initMem, Option.bind_some, memEntry]
    rfl
  have guard := initializerZeroFlag (P := P) (host := host) global mapped zero
  have markedBound : 59984 ≤ marked.bytes.size := (markSize mem base zero).symm ▸ bound
  have threadMapped : markedStore.mem? (Frame.forCall thread.module [] threadSetupFunction.locals) ⟨0⟩ =
      some (aMem, marked) := markedLookup memEntry threadMem
  obtain ⟨word, loaded, setup⟩ := threadSetupReturns (P := P) (host := host) (s := markedStore) (caller := f)
    threadSlot threadEntry threadCode threadType threadMapped markedBound
  let after := s.setMem aMem (threadSetupMemory marked word)
  change Steps P host ⟨markedStore, f, [.plain (.call ⟨1516⟩)]⟩
    ⟨(s.setMem aMem marked).setMem aMem (threadSetupMemory marked word), f, []⟩ at setup
  rw [setSameMemory] at setup
  have constructor := initializerConstructorReturns (P := P) (host := host) (s := after) (caller := f)
    ctorSlot ctorEntry ctorCode ctorType
  have calls : Steps P host ⟨markedStore, f, expression [.call ⟨1516⟩, .call ⟨23⟩]⟩ ⟨after, f, []⟩ :=
    (setup.ctxtInstrs (vs := []) (rest := [.plain (.call ⟨23⟩)])).trans constructor
  have body : Steps P host ⟨s, f, expression initializerFunction.body⟩ ⟨after, f, []⟩ :=
    guard.trans calls
  have lookup := Step.call (P := P) (host := host) (x := ⟨25⟩) initSlot initEntry
  have enter := Step.callRefFunc (P := P) (host := host) (f := caller)
    (c := .callRefType init.type) (vs := []) trivial initEntry initType rfl initCode
  have finishBody : Steps P host ⟨s, f, [.label 0 [] (expression initializerFunction.body)]⟩
      ⟨after, f, []⟩ := (body.label (n := 0) (cont := [])).tail (Step.labelVals (vs := []))
  have finish (outer : Frame) :
      Steps P host ⟨s, outer, [.frame 0 f [.label 0 [] (expression initializerFunction.body)]]⟩
        ⟨after, outer, []⟩ :=
    (finishBody.frame (f := outer) (n := 0)).tail (Step.frameVals (vs := []) rfl)
  exact ⟨word, loaded, (lookup.steps.tail enter).trans (finish caller),
    (enterInvocation (P := P) (host := host) initEntry initCode initType).steps.trans (finish {})⟩

/-- A successful allocation supplies the three function entries. The later runtime state must
retain those entries and provide the global, memory and zero flag needed by the initializer. -/
theorem initializerReturnsAfterAllocation {H : Type} {P : Profile} {host : HostSemantics H}
    {before allocated runtime : Store H} {mi : ModuleInst}
    {imports : List ExternAddr} {globals : List Val} {tables : List Ref}
    {elements : List (List Ref)} {aMem aGlobal : Nat} {mem : MemInst} {base : BitVec 32}
    {globalType : CGlobalType}
    (alloc : allocModule? before sqlite imports globals tables elements = some (allocated, mi))
    (imported : (ExternAddr.funcs imports).length = 23)
    (sameFunctions : runtime.funcs = allocated.funcs)
    (memorySlot : mi.mems[0]? = some aMem) (memoryEntry : runtime.mems[aMem]? = some mem)
    (global : runtime.global? { module := mi } ⟨1⟩ = some (aGlobal, ⟨globalType, .i32 base⟩))
    (zero : Memory.load mem.bytes (initializerAddress base) 4 = some 0)
    (bound : 59984 ≤ mem.bytes.size) :
    ∃ address word, mi.exports.find? (·.name == "_initialize") = some ⟨"_initialize", .func address⟩ ∧
      mi.funcs[25]? = some address ∧ InvokeOk runtime address [] ∧
      Memory.load (initializerMark mem base).bytes 59892 4 = some word ∧
      Steps P host ⟨runtime, { module := mi }, [.plain (.call ⟨25⟩)]⟩
        ⟨runtime.setMem aMem (threadSetupMemory (initializerMark mem base) word), { module := mi }, []⟩ ∧
      Steps P host (invoke runtime address [])
        ⟨runtime.setMem aMem (threadSetupMemory (initializerMark mem base) word), {}, []⟩ := by
  obtain ⟨ctorBinding, _, threadBinding⟩ := allocatedStartupBindings alloc imported
  obtain ⟨aInit, init, exported, initSlot, initEntry, initModule, initCode, initType⟩ :=
    allocatedInitializeExport alloc imported
  obtain ⟨aThread, thread, threadSlot, threadEntry, threadModule, threadCode, threadType⟩ := threadBinding
  obtain ⟨aCtor, ctor, ctorSlot, ctorEntry, _, ctorCode, ctorType⟩ := ctorBinding
  have globalInit : runtime.global? (Frame.forCall init.module [] initializerFunction.locals) ⟨1⟩ =
      some (aGlobal, ⟨globalType, .i32 base⟩) := by
    rw [initModule]
    exact global
  have runtimeInit : runtime.funcs[aInit]? = some init := sameFunctions.symm ▸ initEntry
  obtain ⟨word, loaded, run, invoked⟩ := initializerReturns (P := P) (host := host) (aThread := aThread) (aCtor := aCtor)
    (caller := { module := mi }) (init := init) (thread := thread) (ctor := ctor) (aInit := aInit)
    initSlot runtimeInit initCode initType
    (by rw [initModule]; exact threadSlot) (by rw [sameFunctions]; exact threadEntry) threadCode threadType
    (by rw [initModule]; exact ctorSlot) (by rw [sameFunctions]; exact ctorEntry) ctorCode ctorType
    (by rw [initModule]; exact memorySlot) (by rw [threadModule]; exact memorySlot)
    memoryEntry globalInit zero bound
  exact ⟨aInit, word, exported, initSlot, ⟨init, .nil, .nil, runtimeInit, initType, .nil⟩, loaded, run, invoked⟩

/-- A successfully loaded nonzero flag traps the linked initializer before either callee. -/
theorem initializerTrapsOnNonzero {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {caller : Frame} {init : FuncInst H} {aInit aMem aGlobal : Nat}
    {mem : MemInst} {base word : BitVec 32} {globalType : CGlobalType}
    (slot : caller.module.funcs[25]? = some aInit)
    (entry : s.funcs[aInit]? = some init) (code : init.code = .wasm initializerFunction)
    (signature : Expand init.type (.func .nil .nil))
    (mapped : s.mem? (Frame.forCall init.module [] initializerFunction.locals) ⟨0⟩ = some (aMem, mem))
    (global : s.global? (Frame.forCall init.module [] initializerFunction.locals) ⟨1⟩ =
      some (aGlobal, ⟨globalType, .i32 base⟩))
    (loaded : Memory.load mem.bytes (initializerAddress base) 4 = some word)
    (nonzero : word ≠ 0) :
    Steps P host ⟨s, caller, [.plain (.call ⟨25⟩)]⟩ ⟨s, caller, [.trap]⟩ ∧
    Steps P host (invoke s aInit []) ⟨s, {}, [.trap]⟩ := by
  let f := Frame.forCall init.module [] initializerFunction.locals
  have body := initializerNonzeroFlag (P := P) (host := host) global mapped loaded nonzero
  have lookup := Step.call (P := P) (host := host) (x := ⟨25⟩) slot entry
  have enter := Step.callRefFunc (P := P) (host := host) (f := caller)
    (c := .callRefType init.type) (vs := []) trivial entry signature rfl code
  have finishBody : Steps P host ⟨s, f, [.label 0 [] (expression initializerFunction.body)]⟩
      ⟨s, f, [.trap]⟩ := (body.label (n := 0) (cont := [])).tail Step.trapLabel
  have finish (outer : Frame) :
      Steps P host ⟨s, outer, [.frame 0 f [.label 0 [] (expression initializerFunction.body)]]⟩
        ⟨s, outer, [.trap]⟩ :=
    (finishBody.frame (f := outer) (n := 0)).tail Step.trapFrame
  exact ⟨(lookup.steps.tail enter).trans (finish caller),
    (enterInvocation (P := P) (host := host) entry code signature).steps.trans (finish {})⟩

private def checkedWrites (mem : MemInst) (writes : List (Nat × BitVec 32)) : MemInst :=
  writes.foldl (fun current (offset, word) =>
    { current with bytes := Memory.writeSlice current.bytes offset (Memory.encodeLE 4 word.toNat) }) mem

private theorem checkedWrites_leaveFlag (mem : MemInst) (writes : List (Nat × BitVec 32))
    (within : ∀ q ∈ writes, q.1 + 4 ≤ mem.bytes.size ∧ (59332 ≤ q.1 ∨ q.1 + 4 ≤ 59328)) :
    Memory.load (checkedWrites mem writes).bytes 59328 4 = Memory.load mem.bytes 59328 4 := by
  induction writes generalizing mem with
  | nil => rfl
  | cons q more ih =>
    obtain ⟨offset, value⟩ := q
    obtain ⟨fits, outside⟩ := within (offset, value) List.mem_cons_self
    let bytes := Memory.encodeLE 4 value.toNat
    let next := { mem with bytes := Memory.writeSlice mem.bytes offset bytes }
    have wrote : Memory.writeBytes mem.bytes offset bytes = some next.bytes := by
      simp [Memory.writeBytes, next, bytes, fits]
    have sizes := Memory.writeBytes_size _ _ _ _ wrote
    have rest := ih next fun w hw => by
      obtain ⟨bound, disjoint⟩ := within w (List.mem_cons_of_mem _ hw)
      exact ⟨sizes.symm ▸ bound, disjoint⟩
    have unchanged := Memory.readBytes_writeBytes_disjoint _ _ _ offset 59328 4 wrote
      (by simpa [bytes] using outside)
    change Memory.load (checkedWrites next more).bytes 59328 4 = _
    rw [rest]
    unfold Memory.load
    rw [unchanged]

/-- For the zero base declared by the pinned module, the eight setup writes leave the flag marked. -/
theorem initializerFlagStaysMarked (mem : MemInst) (word : BitVec 32)
    (bound : 59984 ≤ mem.bytes.size) :
    Memory.load (threadSetupMemory (initializerMark mem 0) word).bytes 59328 4 = some 1 := by
  let marked := initializerMark mem 0
  have wrote : Memory.writeBytes mem.bytes 59328 (Memory.encodeLE 4 1) = some marked.bytes := by
    simp [Memory.writeBytes, initializerMark, initializerAddress, marked,
      show 59332 ≤ mem.bytes.size by omega]
  have markedBound : 59984 ≤ marked.bytes.size :=
    (Memory.writeBytes_size _ _ _ _ wrote).symm ▸ bound
  let writes : List (Nat × BitVec 32) :=
    [(59924, 59924), (59980, 0), (59976, 65536), (59972, 126112), (59932, 59924),
      (59928, 59924), (59936, word), (59320, 65536)]
  have good : ∀ q ∈ writes, q.1 + 4 ≤ marked.bytes.size ∧ (59332 ≤ q.1 ∨ q.1 + 4 ≤ 59328) := by
    intro q h
    simp [writes] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
  exact (checkedWrites_leaveFlag marked writes good).trans (Memory.load_store _ _ 59328 4 1 wrote)


end SqliteWasm
