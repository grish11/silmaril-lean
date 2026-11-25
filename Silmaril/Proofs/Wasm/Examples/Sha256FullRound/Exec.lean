module

public import Silmaril.Wasm.Examples.Sha256FullRound.Defs
import Silmaril.Wasm.Examples.Sha256Round.Thms
import Silmaril.Wasm.Execution.Core.Properties
import Silmaril.Proofs.Wasm.Examples.Sha256FullRound.Arithmetic
import Silmaril.Proofs.Wasm.Examples.Sha256FullRound.Memory

public section
namespace Silmaril.Proofs.Wasm.Examples.Sha256FullRound

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
open Silmaril.Wasm.Examples Silmaril.Wasm.Examples.Sha256FullRound
open Silmaril.Wasm.Validation
open Silmaril.Crypto.SHA256.Kernel (Word)

variable {H : Type} {o : GrowOracle}

private theorem get_locals (s : Store H) (f : Frame) {locals : List LocalIdx} {args : List Val}
    (lookup : List.Forall₂ (fun idx val => f.local? idx = some (some val)) locals args) :
    Steps (profile o) noHost ⟨s, f, expression (locals.map Instr.localGet)⟩ ⟨s, f, vals args⟩ := by
  induction lookup with
  | nil => exact .refl
  | @cons index val indices args atIndex _ ih =>
    have step : Step (profile o) noHost ⟨s, f, expression [.localGet index]⟩
        ⟨s, f, vals [val]⟩ := .variable (.localGet atIndex)
    refine (step.steps.ctxtInstrs (vs := []) (rest := expression (indices.map Instr.localGet))).trans ?_
    simpa [vals] using ih.ctxtInstrs (vs := [val]) (rest := [])

private theorem framed {s final : Store H} {caller initial last : Frame}
    {body : Expr} {out : List Val} {resultCount : Nat}
    (steps : Steps (profile o) noHost ⟨s, initial, expression body⟩ ⟨final, last, vals out⟩)
    (resultSize : out.length = resultCount) :
    Steps (profile o) noHost
      ⟨s, caller, [.frame resultCount initial [.label resultCount [] (expression body)]]⟩
      ⟨final, caller, vals out⟩ := by
  have label := (steps.label (n := resultCount) (cont := [])).tail (Step.labelVals (vs := out))
  exact (Steps.frame (f := caller) (n := resultCount) label).tail (Step.frameVals resultSize)

private theorem call_function {s final : Store H} {caller last : Frame}
    {index : FuncIdx} {address : Nat} {fn : FuncInst H} {code : Func}
    {args out : List Val} {ps rs : Ty (.list .val)}
    (slot : caller.module.funcs[index.toNat]? = some address)
    (located : s.funcs[address]? = some fn)
    (sig : Expand fn.type (.func ps rs)) (codeEq : fn.code = .wasm code)
    (arity : args.length = ps.length) (resultSize : out.length = rs.length)
    (body : Steps (profile o) noHost
      ⟨s, Frame.forCall fn.module args code.locals, expression code.body⟩ ⟨final, last, vals out⟩) :
    Steps (profile o) noHost ⟨s, caller, vals args ++ expression [.call index]⟩
      ⟨final, caller, vals out⟩ := by
  have start := Step.call (P := profile o) (host := (noHost : HostSemantics H)) slot located
  have begins : Steps (profile o) noHost ⟨s, caller, vals args ++ expression [.call index]⟩
      ⟨s, caller, vals args ++ [.ref (.func address), .callRefType fn.type]⟩ := by
    simpa [expression] using start.steps.ctxtInstrs (vs := args) (rest := [])
  exact begins.trans (Relation.ReflTransGen.head
    (Step.callRefFunc (c := .callRefType fn.type) trivial located sig arity codeEq)
    (framed body resultSize))

private theorem compute_local {s : Store H} {f : Frame} {indices : List LocalIdx}
    {args : List Val} {callee : FuncIdx} {target : LocalIdx} {result : Val}
    (reads : List.Forall₂ (fun idx val => f.local? idx = some (some val)) indices args)
    (calls : Steps (profile o) noHost ⟨s, f, vals args ++ expression [.call callee]⟩
      ⟨s, f, vals [result]⟩)
    (valid : target.toNat < f.locals.length) :
    Steps (profile o) noHost
      ⟨s, f, expression (indices.map Instr.localGet ++ [.call callee, .localSet target])⟩
      ⟨s, f.setLocal target result, []⟩ := by
  have begins := (get_locals (o := o) s f reads).ctxtInstrs (vs := [])
    (rest := expression [.call callee, .localSet target])
  have evaluated := calls.ctxtInstrs (vs := []) (rest := expression [.localSet target])
  have setValue : Step (profile o) noHost ⟨s, f, vals [result] ++ expression [.localSet target]⟩
      ⟨s, f.setLocal target result, []⟩ := .variable (.localSet valid)
  have finish : Steps (profile o) noHost
      ⟨s, f, vals [] ++ vals args ++ expression [.call callee, .localSet target]⟩
      ⟨s, f.setLocal target result, []⟩ := by
    simpa [expression, vals, List.append_assoc] using evaluated.tail setValue
  simpa only [expression, vals, List.map_append, List.map_nil, List.nil_append] using begins.trans finish

private theorem memory_lookup {s : Store H} {f : Frame} {address : Nat} {mem : MemInst}
    (mapped : s.mem? f ⟨0⟩ = some (address, mem)) :
    f.module.mems[0]? = some address ∧ s.mems[address]? = some mem := by
  unfold Store.mem? at mapped
  cases slot : f.module.mems[0]? with
  | none => simp [Idx.toNat, slot, bind, Option.bind] at mapped
  | some target =>
    cases located : s.mems[target]? with
    | none => simp [Idx.toNat, slot, located, bind, Option.bind] at mapped
    | some actual =>
      simp [Idx.toNat, slot, located, bind, Option.bind, pure] at mapped
      obtain ⟨rfl, rfl⟩ := mapped
      exact ⟨rfl, located⟩

private theorem memory_remap {s : Store H} {f g : Frame} {address : Nat} {mem : MemInst}
    (mapped : s.mem? f ⟨0⟩ = some (address, mem)) (sameModule : g.module = f.module)
    (updated : MemInst) : (s.setMem address updated).mem? g ⟨0⟩ = some (address, updated) := by
  obtain ⟨hm, hs⟩ := memory_lookup mapped
  have inRange := (getElem?_eq_some_iff.mp hs).choose
  simp [Store.mem?, Idx.toNat, sameModule, hm, Store.setMem, List.getElem?_set_self inRange,
    bind, Option.bind, pure]

private theorem store_local {s : Store H} {f : Frame} {address : Nat} {mem : MemInst}
    {dst : Word} {target : Destination} {word : Word}
    (mapped : s.mem? f ⟨0⟩ = some (address, mem))
    (dest : f.local? ⟨0⟩ = some (some (.i32 dst)))
    (source : f.local? target.2 = some (some (.i32 word)))
    (bounds : dst.toNat + 32 ≤ mem.bytes.size) :
    Steps (profile o) noHost ⟨s, f, expression (stores [target])⟩
      ⟨s.setMem address {mem with bytes := writeWord dst.toNat (target.1, word) mem.bytes}, f, []⟩ := by
  obtain ⟨slot, localIndex⟩ := target
  have getDst : Step (profile o) noHost ⟨s, f, expression [.localGet ⟨0⟩]⟩
      ⟨s, f, vals [.i32 dst]⟩ := .variable (.localGet dest)
  have getWord : Step (profile o) noHost ⟨s, f, expression [.localGet localIndex]⟩
      ⟨s, f, vals [.i32 word]⟩ := .variable (.localGet source)
  have store : Step (profile o) noHost
      ⟨s, f, vals [.i32 dst, .i32 word] ++ expression [storeInstr slot]⟩
      ⟨s.setMem address {mem with bytes := writeWord dst.toNat (slot, word) mem.bytes}, f, []⟩ := by
    apply Step.memory
    apply MemoryStep.storeIntVal (a := .i32) mapped
    have offsetFits : 4 * slot.val < 2 ^ 64 := by have := slot.isLt; omega
    change Memory.store mem.bytes (dst.toNat + (4 * slot.val) % (2 ^ 64)) (count := 4)
      (word.setWidth 32) = _
    rw [Nat.mod_eq_of_lt offsetFits, BitVec.setWidth_eq]
    exact store_word dst.toNat slot word mem.bytes bounds
  refine (getDst.steps.ctxtInstrs (vs := []) (rest := expression [.localGet localIndex, storeInstr slot])).trans ?_
  exact (getWord.steps.ctxtInstrs (vs := [.i32 dst]) (rest := expression [storeInstr slot])).tail store

private theorem store_sequence (targets : List Destination) (output : Vector Word 8)
    {s : Store H} {f : Frame} {address : Nat} {mem : MemInst} {dst : Word}
    (mapped : s.mem? f ⟨0⟩ = some (address, mem))
    (dest : f.local? ⟨0⟩ = some (some (.i32 dst)))
    (sources : ∀ target ∈ targets, f.local? target.2 = some (some (.i32 output[target.1])))
    (bounds : dst.toNat + 32 ≤ mem.bytes.size) :
    Steps (profile o) noHost ⟨s, f, expression (stores targets)⟩
      ⟨s.setMem address {mem with bytes := writeWords dst.toNat (slotWords targets output) mem.bytes},
        f, []⟩ := by
  induction targets generalizing s mem with
  | nil =>
    obtain ⟨_, located⟩ := memory_lookup mapped
    obtain ⟨inRange, value⟩ := getElem?_eq_some_iff.mp located
    have unchanged : s.setMem address mem = s := by
      simp only [Store.setMem, ← value, List.set_getElem_self inRange]
    simpa [stores, expression, slotWords, writeWords, unchanged] using
      (Relation.ReflTransGen.refl : Steps (profile o) noHost ⟨s, f, []⟩ ⟨s, f, []⟩)
  | cons target tail ih =>
    let updated := {mem with bytes := writeWord dst.toNat (target.1, output[target.1]) mem.bytes}
    have updateSize : updated.bytes.size = mem.bytes.size := by
      exact writes_size dst.toNat [(target.1, output[target.1])] mem.bytes bounds
    have headStep := store_local (o := o) mapped dest (sources target List.mem_cons_self) bounds
    have rest := ih (memory_remap mapped (g := f) rfl updated)
      (fun t ht => sources t (List.mem_cons_of_mem _ ht)) (updateSize ▸ bounds)
    have done := (headStep.ctxtInstrs (vs := []) (rest := expression (stores tail))).trans rest
    simpa [stores, expression, List.flatMap_cons, slotWords, writeWords, Store.setMem,
      List.set_set, updated] using done

private theorem sequence {s middle final : Store H} {f g h : Frame} {first rest : Expr}
    (left : Steps (profile o) noHost ⟨s, f, expression first⟩ ⟨middle, g, []⟩)
    (right : Steps (profile o) noHost ⟨middle, g, expression rest⟩ ⟨final, h, []⟩) :
    Steps (profile o) noHost ⟨s, f, expression (first ++ rest)⟩ ⟨final, h, []⟩ := by
  have lifted := left.ctxtInstrs (vs := []) (rest := expression rest)
  simpa only [expression, vals, List.map_append, List.map_nil, List.nil_append] using lifted.trans right

private theorem body_steps (o : GrowOracle) (dst : Word) (x : Input) (d : Word)
    (s : Store H) (mi : ModuleInst) (address : Nat) (mem : MemInst)
    (links : Linkage s mi) (mapped : s.mem? {module := mi} ⟨0⟩ = some (address, mem))
    (bounds : dst.toNat + 32 ≤ mem.bytes.size)
    (typedA : ConfigOk (Sha256Round.entry x s mi) [.i32])
    (typedE : ConfigOk (eEntry x d (s.setMem address (memoryAfterA dst x d mem)) mi) [.i32]) :
    Steps (profile o) noHost ⟨s, wrapperFrame dst x d mi, expression roundBody⟩
      ⟨s.setMem address {mem with bytes := roundMemory dst.toNat (outputWords x d) mem.bytes},
        frameAfterE dst x d mi, []⟩ := by
  let words := outputWords x d
  let entry := wrapperFrame dst x d mi
  let afterA := frameAfterA dst x d mi
  let afterE := frameAfterE dst x d mi
  let memA := memoryAfterA dst x d mem
  let sA := s.setMem address memA

  have aBody := Sha256Round.steps_fixture o x d s mi typedA
  have aCall : Steps (profile o) noHost ⟨s, entry, vals (aValues x) ++ expression [.call ⟨0⟩]⟩
      ⟨s, entry, vals [.i32 words[0]]⟩ :=
    call_function (ps := Ty.ofList (List.replicate 9 .i32)) (rs := .cons .i32 .nil)
      links.aSlot links.aCode (Expand.iff.mpr rfl) rfl rfl rfl aBody
  have readsA : List.Forall₂ (fun idx val => entry.local? idx = some (some val)) aLocals (aValues x) :=
    .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl
      (.cons rfl (.cons rfl .nil))))))))
  have computeFirst : Steps (profile o) noHost ⟨s, entry, expression computeA⟩ ⟨s, afterA, []⟩ :=
    compute_local readsA aCall (by change 11 < 12; decide)

  have readsFirst : ∀ target ∈ firstWrites, afterA.local? target.2 = some (some (.i32 words[target.1])) := by
    intro target member
    simp only [firstWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  have storeFirst : Steps (profile o) noHost
      ⟨s, afterA, expression (stores firstWrites)⟩ ⟨sA, afterA, []⟩ :=
    store_sequence firstWrites words mapped rfl readsFirst bounds

  have eBodySteps := runI_steps_typed (o := o) (eBody.length + 1) typedE
  rw [run_e o x d sA mi] at eBodySteps
  have eCall : Steps (profile o) noHost ⟨sA, afterA, vals (eValues x d) ++ expression [.call ⟨1⟩]⟩
      ⟨sA, afterA, vals [.i32 words[4]]⟩ :=
    call_function (ps := Ty.ofList (List.replicate 7 .i32)) (rs := .cons .i32 .nil)
      links.eSlot links.eCode (Expand.iff.mpr rfl) rfl rfl rfl eBodySteps
  have readsE : List.Forall₂ (fun idx val => afterA.local? idx = some (some val)) eLocals (eValues x d) :=
    .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl .nil))))))
  have computeFifth : Steps (profile o) noHost ⟨sA, afterA, expression computeE⟩ ⟨sA, afterE, []⟩ :=
    compute_local readsE eCall (by change 10 < 12; decide)

  have readsFinal : ∀ target ∈ finalWrites, afterE.local? target.2 = some (some (.i32 words[target.1])) := by
    intro target member
    simp only [finalWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  have sizeA : memA.bytes.size = mem.bytes.size :=
    writes_size dst.toNat (slotWords firstWrites words) mem.bytes bounds
  have storeFinal := store_sequence (o := o) finalWrites words
    (memory_remap mapped (g := afterE) rfl memA) rfl readsFinal (sizeA ▸ bounds)
  have storesDone : Steps (profile o) noHost ⟨sA, afterE, expression (stores finalWrites)⟩
      ⟨s.setMem address {mem with bytes := roundMemory dst.toNat words mem.bytes}, afterE, []⟩ := by
    simpa only [sA, memA, memoryAfterA, roundMemory, slotWords, List.map_append, writeWords,
      List.foldl_append, Store.setMem, List.set_set] using storeFinal
  simpa only [roundBody, List.append_assoc] using sequence computeFirst (sequence storeFirst (sequence computeFifth storesDone))

theorem call_round (o : GrowOracle) (dst : Word) (x : Input) (d : Word)
    (s : Store H) (caller : Frame) (mi : ModuleInst) (index : FuncIdx)
    (calleeAddr address : Nat) (mem : MemInst)
    (wrapperSlot : caller.module.funcs[index.toNat]? = some calleeAddr)
    (wrapperCode : s.funcs[calleeAddr]? = some (roundInstance mi))
    (links : Linkage s mi) (mapped : s.mem? {module := mi} ⟨0⟩ = some (address, mem))
    (bounds : dst.toNat + 32 ≤ mem.bytes.size)
    (typedA : ConfigOk (Sha256Round.entry x s mi) [.i32])
    (typedE : ConfigOk (eEntry x d (s.setMem address (memoryAfterA dst x d mem)) mi) [.i32]) :
    let bytes := roundMemory dst.toNat (outputWords x d) mem.bytes
    Steps (profile o) noHost ⟨s, caller, vals (roundValues dst x d) ++ expression [.call index]⟩
      ⟨s.setMem address {mem with bytes := bytes}, caller, []⟩ ∧
    OutputOk mem.bytes bytes dst.toNat (outputWords x d) := by
  refine ⟨?_, round_output dst.toNat (outputWords x d) mem.bytes bounds⟩
  exact call_function (ps := Ty.ofList (List.replicate 11 .i32)) (rs := .nil) (out := [])
    wrapperSlot wrapperCode (Expand.iff.mpr rfl) rfl rfl rfl
    (body_steps o dst x d s mi address mem links mapped bounds typedA typedE)

end Silmaril.Proofs.Wasm.Examples.Sha256FullRound
