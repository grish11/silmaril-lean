module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Proofs

open Execution.Runtime (Frame FuncAddr FuncInst Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall

theorem indirect_step_iff {H : Type} {base : Store H} {memory : Memory32 base}
    {site : IndirectSite} {active : Frame} {bytes : ByteArray} {stack : List Value}
    {selector : BitVec 32} {rest : List Admin} {dst : Config H} (linked : site.Linked base active.module) :
    Internal ⟨memory.store bytes, active,
      values (stack ++ [Value.int .i32 selector]) ++ .source (.callIndirect site.typeIndex) :: rest⟩ dst ↔
      ∃ target, site.Lookup base selector target ∧
        dst = ⟨memory.store bytes, active, values stack ++ IndirectSite.lookupHead target :: rest⟩ := by
  have tableFound : frameTable (memory.store bytes) active = some site.table := linked.tableAt
  change Step CallFrame.limeNoHost _ _ ↔ _
  rw [Computed.lime_call_indirect_iff tableFound linked.signatureAt]
  constructor
  · rintro (⟨entry | entry, rfl⟩ | ⟨address, fn, entry, allocated, rfl⟩)
    · exact ⟨none, .bounds entry, rfl⟩
    · exact ⟨none, .null entry, rfl⟩
    · have allocation : base.funcs[address.value]? = some fn := allocated
      by_cases same : fn.type = site.signature
      · obtain ⟨declared, found, registered⟩ := linked.entries address (List.mem_of_getElem? entry)
        rw [allocation] at found
        cases found
        cases fn with
        | host actual code =>
          change actual = site.signature at same
          subst actual
          exact ⟨_, .host entry allocation, by simp [IndirectSite.lookupHead, FuncInst.type]⟩
        | wasm actual module body =>
          rcases registered same with ⟨callee, found⟩ | ⟨callee, found, allocated⟩
          · have exactAllocation := linked.graphAllocated address callee found
            have declType := congrArg FuncInst.type (Option.some.inj (allocation.symm.trans exactAllocation))
            exact ⟨_, .wasm (callee := ⟨address, callee⟩) entry found exactAllocation (declType.symm.trans same),
              by simp [IndirectSite.lookupHead, same]⟩
          · have declType := congrArg FuncInst.type (Option.some.inj (allocation.symm.trans allocated))
            exact ⟨_, .memory (callee := ⟨address, callee⟩) entry found allocated (declType.symm.trans same),
              by simp [IndirectSite.lookupHead, same]⟩
      · exact ⟨none, .mismatch entry allocation same, by simp [IndirectSite.lookupHead, same]⟩
  · rintro ⟨target, found, rfl⟩
    cases found with
    | bounds entry => exact .inl ⟨.inl entry, rfl⟩
    | null entry => exact .inl ⟨.inr entry, rfl⟩
    | @mismatch address fn entry allocated different =>
      exact .inr ⟨address, fn, entry, allocated, by simp [IndirectSite.lookupHead, different]⟩
    | @host address code entry allocated =>
      exact .inr ⟨address, .host site.signature code, entry, allocated,
        by simp [IndirectSite.lookupHead, FuncInst.type]⟩

    | @wasm callee entry _ allocated typed =>
      exact .inr ⟨callee.address, _, entry, allocated, by simp [IndirectSite.lookupHead, FuncInst.type, typed]⟩

    | @memory callee entry _ allocated typed =>
      exact .inr ⟨callee.address, _, entry, allocated, by simp [IndirectSite.lookupHead, FuncInst.type, typed]⟩

private theorem failure_excludes_allocation {H : Type} {base : Store H} {site : IndirectSite}
    {selector : BitVec 32} {address : FuncAddr} {fn : FuncInst Wasm.Lime1.Func H}
    (entry : site.table.refs[selector.toNat]? = some (some address))
    (allocated : base.funcs[address.value]? = some fn) (typed : fn.type = site.signature)
    (failure : site.Lookup base selector none) : False := by
  cases failure with
  | bounds missing =>
    rw [entry] at missing
    cases missing
  | null empty =>
    rw [entry] at empty
    cases empty
  | mismatch present found different =>
    rw [entry] at present
    cases present
    rw [allocated] at found
    cases found
    exact different typed

private theorem lookup_trap {H : Type} {base : Store H} {site : IndirectSite}
    {selector : BitVec 32} {target : Option (IndirectTarget H)}
    (failure : site.Lookup base selector none) (lookup : site.Lookup base selector target) :
    target = none := by
  cases lookup with
  | bounds | null | mismatch => rfl
  | host entry allocated => exact (failure_excludes_allocation entry allocated rfl failure).elim
  | wasm entry _ allocated typed => exact (failure_excludes_allocation entry allocated typed failure).elim
  | memory entry _ allocated typed => exact (failure_excludes_allocation entry allocated typed failure).elim

theorem indirect_trap_iff {H : Type} {base : Store H} {memory : Memory32 base}
    {site : IndirectSite} {active : Frame} {bytes : ByteArray} {stack : List Value}
    {selector : BitVec 32} {rest : List Admin} {dst : Config H}
    (linked : site.Linked base active.module) (failure : site.Lookup base selector none) :
    Internal ⟨memory.store bytes, active,
      values (stack ++ [Value.int .i32 selector]) ++ .source (.callIndirect site.typeIndex) :: rest⟩ dst ↔
      dst = ⟨memory.store bytes, active, values stack ++ .trap :: rest⟩ := by
  rw [indirect_step_iff linked]
  constructor
  · rintro ⟨target, lookup, eq⟩
    cases lookup_trap failure lookup
    exact eq
  · intro eq
    exact ⟨none, failure, eq⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Proofs
