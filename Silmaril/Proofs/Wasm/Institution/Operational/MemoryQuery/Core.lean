module

public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery.Proofs

open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Wasm.Numerics

theorem core_sound {H : Type} {P : Profile} {s : Store H} {f : Frame} {a : Nat} {m : MemInst}
    (memory : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query out : State} (edge : Edge m.bytes query out) :
    Step P noHost ⟨s, f, coreCode query⟩ ⟨s, f, coreCode out⟩ := by
  cases invert edge with
  | size =>
    have step := MemoryStep.size (P := P) memory
    rw [is32] at step
    exact .memory step
  | load addr bits read =>
    have load : Memory.load m.bytes (effAddr addr.toNat arg.toCore) 4 = some bits := by
      simpa [effAddr, arg, Wasm.V1.MemArg.toCore, Wasm.V1.widen32] using read
    have step := MemoryStep.loadIntVal (P := P) (t := .i32) (a := .i32) (i := addr) memory load
    change MemoryStep P ⟨s, f, coreCode (.load addr)⟩
      ⟨s, f, [.plain (.intConst .i32 (bits.setWidth 32))]⟩ at step
    rw [BitVec.setWidth_eq] at step
    exact .memory step
  | loadTrap addr bound =>
    apply Step.memory
    apply MemoryStep.loadIntOob (a := .i32) (i := addr) memory
    change m.bytes.size < addr.toNat + 4
    exact bound

private theorem memory_readback {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {a : Nat} {m : MemInst} {input : List Admin} {target : Config H}
    (step : MemoryStep P ⟨s, f, input⟩ target) (query : State) (sub : List.Sublist input (coreCode query))
    (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32) :
    ∃ out, input = coreCode query ∧ Edge m.bytes query out ∧ target = ⟨s, f, coreCode out⟩ := by
  cases step with
  | size found =>
    have op := sub.subset (List.Mem.head _)
    cases query <;> simp [coreCode] at op
    subst_vars
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    refine ⟨.value _, rfl, fact .size, ?_⟩
    rw [is32]
    rfl
  | @loadIntVal _ _ t x offset w i address mi bits found read =>
    have op := sub.subset (List.Mem.tail _ (List.Mem.head _))
    have operand := sub.subset (List.Mem.head _)
    cases query <;> simp [coreCode] at op
    rename_i queryAddress
    obtain ⟨rfl, rfl, rfl⟩ := op
    cases w <;> simp [coreCode, AddrType.intType] at operand
    case i64 => cases (Instr.intConst.inj operand).1
    have same : i = queryAddress := eq_of_heq (Instr.intConst.inj operand).2
    subst i
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    change Memory.load m.bytes queryAddress.toNat 4 = some (show BitVec 32 from bits) at read
    refine ⟨.value bits, rfl, fact (.load _ _ read), ?_⟩
    change (⟨s, f, [.plain (.intConst .i32 (BitVec.setWidth 32 (show BitVec 32 from bits)))]⟩ : Config H) = _
    rw [BitVec.setWidth_eq]
    rfl
  | @loadIntOob _ _ t x offset w i address mi found bound =>
    have op := sub.subset (List.Mem.tail _ (List.Mem.head _))
    have operand := sub.subset (List.Mem.head _)
    cases query <;> simp [coreCode] at op
    rename_i queryAddress
    obtain ⟨rfl, rfl, rfl⟩ := op
    cases w <;> simp [coreCode, AddrType.intType] at operand
    case i64 => cases (Instr.intConst.inj operand).1
    have same : i = queryAddress := eq_of_heq (Instr.intConst.inj operand).2
    subst i
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Option.some.inj found
    change m.bytes.size < queryAddress.toNat + 4 at bound
    exact ⟨.trap, rfl, fact (.loadTrap _ bound), rfl⟩
  | _ =>
    have checked := sub.subset
    cases query <;> simp [coreCode] at checked

theorem core_readback {H : Type} {P : Profile} {s : Store H} {f : Frame} {a : Nat} {m : MemInst}
    (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query : State} {dst : Config H} (step : Step P noHost ⟨s, f, coreCode query⟩ dst) :
    ∃ out, Edge m.bytes query out ∧ dst = ⟨s, f, coreCode out⟩ := by
  have go {op : Admin} (family : famOf op = .memory)
      (first : (fnv (coreCode query)).2 = [op]) :
      ∃ out, Edge m.bytes query out ∧ dst = ⟨s, f, coreCode out⟩ := by
    rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp step with head | bubble
    · obtain ⟨saved, args, op', tail, next, firstHead, eq, hh, rfl⟩ := fnv_headDec head
      have same := (congrArg Prod.snd firstHead).symm.trans first
      simp only [List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have fam := hh.fam_inv (by rw [family]; decide)
      rw [family] at fam
      change coreCode query = vals saved ++ (vals args ++ [op']) at eq
      have sub : List.Sublist (vals args ++ [op']) (coreCode query) := by
        rw [eq]
        exact List.sublist_append_right _ _
      obtain ⟨out, whole, edge, rfl⟩ := memory_readback (show MemoryStep P _ _ from fam)
        query sub lookup is32
      have length := congrArg List.length eq
      have len := congrArg List.length whole
      simp only [List.length_append, vals, List.length_map, List.length_cons] at length len
      have empty : saved = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst saved
      exact ⟨out, edge, by simp [vals]⟩
    · obtain ⟨_, _, _, _, _, ⟨eq, _, _⟩ | ⟨_, eq, _, _⟩⟩ := fnv_bubble bubble <;>
        have last := (congrArg Prod.snd eq).symm.trans first <;>
        have same := (List.cons.inj last).1 <;>
        rw [← same] at family <;> contradiction
  cases query with
  | size => exact go rfl rfl
  | load addr => exact go rfl rfl
  | value bits => exact (not_step_vals (W := [.num ⟨.int .i32, bits⟩]) step).elim
  | trap => exact (not_step_trap step).elim

end Silmaril.Wasm.Institution.Operational.MemoryQuery.Proofs
