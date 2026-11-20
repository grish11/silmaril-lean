module

import Silmaril.Wasm.Execution.Core.Intrinsic.Call.Thms
import Silmaril.Wasm.Execution.Core.Properties
import Silmaril.Wasm.Validation.Check.Validate

/-! A finite, immutable, single-signature call machine. Recursive calls name
table slots; only the runtime continuation grows. This is a test model, not a
second public Core AST. -/

namespace Silmaril.Wasm.IntrinsicRecursiveDemo

open Execution.Core Execution.Core.Intrinsic Validation Numerics

private def localZero : LocalIdx := ⟨0⟩
private def signatureGroup := RecType.mk [⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]
private def signature : DefType := (Context.rollGroup {} signatureGroup)[0]'(by decide +kernel)
private theorem expands : Expand signature (.func (.cons .i32 .nil) (.cons .i32 .nil)) :=
  Expand.iff.mpr rfl

private def index {count : Nat} (bounded : count ≤ 2 ^ 32) (slot : Fin count) : FuncIdx :=
  ⟨⟨slot.val, Nat.lt_of_lt_of_le slot.isLt bounded⟩⟩

private inductive Code (count : Nat) : List IntType → Type where
  | done : Code count [.i32]
  | get {stack} : Code count (.i32 :: stack) → Code count stack
  | call {below} : Fin count → Code count (.i32 :: below) → Code count (.i32 :: below)
  | trap {stack} : Code count stack

private def Code.erase {count : Nat} (bounded : count ≤ 2 ^ 32) :
    {stack : List IntType} → Code count stack → List Instr
  | _, .done => []
  | _, .get next => .localGet localZero :: next.erase bounded
  | _, .call slot next => .call (index bounded slot) :: next.erase bounded
  | _, .trap => [.unreachable]

private def raw {count : Nat} (bounded : count ≤ 2 ^ 32) (body : Code count []) : Func :=
  ⟨⟨0⟩, [], body.erase bounded⟩

private structure Table {count : Nat} (store : Store Unit) where
  bounded : count ≤ 2 ^ 32
  instance_ : ModuleInst
  address : Fin count → Nat
  body : Fin count → Code count []
  resolve : ∀ slot, instance_.funcs[slot.val]? = some (address slot)
  lookup : ∀ slot, store.funcs[address slot]? =
    some ⟨signature, instance_, .wasm (raw bounded (body slot))⟩

private def word (bits : BitVec 32) : Val := .num ⟨.int .i32, bits⟩
private def frame (instance_ : ModuleInst) (parameter : BitVec 32) : Frame :=
  ⟨[some (word parameter)], instance_⟩

private inductive Kont (count : Nat) where
  | root (outer : Frame)
  | save {below : List IntType} (parameter : BitVec 32) (saved : Values below)
      (resume : Code count (.i32 :: below)) (outer : Kont count)

private def Kont.rootFrame : Kont count → Frame
  | .root outer => outer
  | .save _ _ _ outer => outer.rootFrame

private inductive Machine {count : Nat} {store : Store Unit} (table : Table (count := count) store) where
  | active {stack : List IntType} (parameter : BitVec 32) (values : Values stack)
      (code : Code count stack) (kont : Kont count)
  | returned (bits : BitVec 32) (outer : Frame)
  | trapped (outer : Frame)

private def pop {count : Nat} {store : Store Unit} {table : Table (count := count) store}
    (bits : BitVec 32) : Kont count → Machine table
  | .root outer => .returned bits outer
  | .save parameter saved resume outer => .active parameter (.cons (kind := .i32) bits saved) resume outer

private def tick {count : Nat} {store : Store Unit} (table : Table (count := count) store) :
    Machine table → Machine table
  | .active parameter values (.get next) kont =>
    .active parameter (.cons (kind := .i32) parameter values) next kont
  | .active parameter (.cons arg saved) (.call slot resume) kont =>
    .active arg .nil (table.body slot) (.save parameter saved resume kont)
  | .active _ (.cons bits .nil) .done kont => pop bits kont
  | .active _ _ .trap kont => .trapped kont.rootFrame
  | terminal => terminal

private inductive Outcome where
  | returned (bits : BitVec 32)
  | trapped
  | exhausted
  deriving DecidableEq

private def run {count : Nat} {store : Store Unit} (table : Table (count := count) store) :
    Nat → Machine table → Outcome
  | _, .returned bits _ => .returned bits
  | _, .trapped _ => .trapped
  | 0, .active .. => .exhausted
  | fuel + 1, active@(.active ..) => run table fuel (tick table active)

private def Kont.plug {count : Nat} {store : Store Unit} (table : Table (count := count) store) :
    Kont count → Frame → List Admin → Config Unit
  | .root outer, current, code => ⟨store, outer, [.frame 1 current [.label 1 [] code]]⟩
  | .save parameter saved resume outer, current, code =>
    outer.plug table (frame table.instance_ parameter)
      (vals saved.erase.reverse ++ [.frame 1 current [.label 1 [] code]] ++
        expression (resume.erase table.bounded))

private def activeConfig {count : Nat} {store : Store Unit} (table : Table (count := count) store)
    {stack : List IntType} (parameter : BitVec 32) (values : Values stack) (code : Code count stack)
    (kont : Kont count) : Config Unit :=
  kont.plug table (frame table.instance_ parameter)
    (vals values.erase.reverse ++ expression (code.erase table.bounded))

private def Machine.erase {count : Nat} {store : Store Unit} (table : Table (count := count) store) :
    Machine table → Config Unit
  | .active parameter values code kont => activeConfig table parameter values code kont
  | .returned bits outer => ⟨store, outer, vals [word bits]⟩
  | .trapped outer => ⟨store, outer, [.trap]⟩

private theorem plug_steps {count : Nat} {store : Store Unit} (table : Table (count := count) store)
    (kont : Kont count) {current : Frame} {before after : List Admin} {P : Profile}
    {host : HostSemantics Unit}
    (steps : Steps P host ⟨store, current, before⟩ ⟨store, current, after⟩) :
    Steps P host (kont.plug table current before) (kont.plug table current after) := by
  induction kont generalizing current before after with
  | root => exact Steps.frame (Steps.label steps)
  | save parameter saved resume outer liftOuter =>
    exact liftOuter (Steps.ctxtInstrs (vs := saved.erase.reverse)
      (rest := expression (resume.erase table.bounded)) (Steps.frame (Steps.label steps)))

private theorem push_sound {count : Nat} {store : Store Unit} (table : Table (count := count) store)
    {P : Profile} {host : HostSemantics Unit} {below : List IntType} (slot : Fin count)
    (parameter arg : BitVec 32) (saved : Values below) (resume : Code count (.i32 :: below))
    (kont : Kont count) :
    Steps P host (activeConfig table parameter (.cons (kind := .i32) arg saved) (.call slot resume) kont)
      (activeConfig table arg .nil (table.body slot) (.save parameter saved resume kont)) := by
  let callee : FuncInst Unit := ⟨signature, table.instance_, .wasm (raw table.bounded (table.body slot))⟩
  let current := frame table.instance_ parameter
  have resolve : Step P host ⟨store, current, [.plain (.call (index table.bounded slot))]⟩
      ⟨store, current, [.ref (.func (table.address slot)), .callRefType signature]⟩ :=
    Step.call (fi := callee) (table.resolve slot) (table.lookup slot)
  have enter : Step P host
      ⟨store, current, [(word arg).toAdmin, .ref (.func (table.address slot)), .callRefType signature]⟩
      ⟨store, current, [.frame 1 (frame table.instance_ arg)
        [.label 1 [] (expression ((table.body slot).erase table.bounded))]]⟩ :=
    Step.callRefFunc (c := .callRefType signature) (vs := [word arg]) (code := raw table.bounded (table.body slot))
      trivial (table.lookup slot) expands rfl rfl
  have entry := (Steps.ctxtInstrs (vs := [word arg]) (rest := []) resolve.steps).tail enter
  apply plug_steps table kont
  simpa only [activeConfig, Kont.plug, Code.erase, Values.erase, List.reverse_cons, List.reverse_nil, vals,
    List.map_append, List.map_cons, List.map_nil, List.nil_append, List.append_assoc,
    List.append_nil, expression, word, List.cons_append] using
    Steps.ctxtInstrs (vs := saved.erase.reverse) (rest := expression (resume.erase table.bounded)) entry

private theorem leave_frame {store : Store Unit} {P : Profile} {host : HostSemantics Unit}
    (outer inner : Frame) (bits : BitVec 32) :
    Steps P host ⟨store, outer, [.frame 1 inner [.label 1 [] (vals [word bits])]]⟩
      ⟨store, outer, vals [word bits]⟩ :=
  (Step.ctxtFrame Step.labelVals).steps.tail (.frameVals rfl)

private theorem pop_sound {count : Nat} {store : Store Unit} (table : Table (count := count) store)
    {P : Profile} {host : HostSemantics Unit} {below : List IntType}
    (parameter bits : BitVec 32) (saved : Values below) (resume : Code count (.i32 :: below))
    (caller : BitVec 32) (kont : Kont count) :
    Steps P host (activeConfig table parameter (.cons (kind := .i32) bits .nil) .done (.save caller saved resume kont))
      (activeConfig table caller (.cons (kind := .i32) bits saved) resume kont) := by
  let outer := frame table.instance_ caller
  let inner := frame table.instance_ parameter
  apply plug_steps table kont
  simpa only [activeConfig, Kont.plug, Code.erase, Values.erase, List.reverse_cons, List.reverse_nil,
    vals, List.map_append, List.map_cons, List.map_nil, List.nil_append, List.append_assoc,
    List.append_nil, expression, word, List.cons_append] using
    Steps.ctxtInstrs (vs := saved.erase.reverse) (rest := expression (resume.erase table.bounded))
      (leave_frame outer inner bits)

private theorem get_sound {count : Nat} {store : Store Unit} (table : Table (count := count) store)
    {P : Profile} {host : HostSemantics Unit} {stack : List IntType} (parameter : BitVec 32)
    (values : Values stack) (next : Code count (.i32 :: stack)) (kont : Kont count) :
    Steps P host (activeConfig table parameter values (.get next) kont)
      (activeConfig table parameter (.cons (kind := .i32) parameter values) next kont) := by
  have get : Step P host ⟨store, frame table.instance_ parameter, [.plain (.localGet localZero)]⟩
      ⟨store, frame table.instance_ parameter, [(word parameter).toAdmin]⟩ := .variable (.localGet rfl)
  apply plug_steps table kont
  simpa only [activeConfig, Code.erase, Values.erase, List.reverse_cons, vals, List.map_append,
    List.map_cons, List.map_nil, List.append_assoc, expression, word, List.cons_append, List.nil_append] using
    Steps.ctxtInstrs (vs := values.erase.reverse) (rest := expression (next.erase table.bounded)) get.steps

private theorem clear_trap {store : Store Unit} {P : Profile} {host : HostSemantics Unit}
    (current : Frame) (saved : List Val) (rest : List Admin) :
    Steps P host ⟨store, current, vals saved ++ [.trap] ++ rest⟩ ⟨store, current, [.trap]⟩ := by
  by_cases nonempty : saved ≠ [] ∨ rest ≠ []
  · exact (Step.trapInstrs nonempty).steps
  · push Not at nonempty
    obtain ⟨rfl, rfl⟩ := nonempty
    exact .refl

private theorem close_trap {count : Nat} {store : Store Unit} (table : Table (count := count) store)
    {P : Profile} {host : HostSemantics Unit} (kont : Kont count) (current : Frame) :
    Steps P host (kont.plug table current [.trap]) ⟨store, kont.rootFrame, [.trap]⟩ := by
  have exit (outer inner : Frame) :
      Steps P host ⟨store, outer, [.frame 1 inner [.label 1 [] [.trap]]]⟩ ⟨store, outer, [.trap]⟩ :=
    (Step.ctxtFrame Step.trapLabel).steps.tail Step.trapFrame
  induction kont generalizing current with
  | root outer => exact exit outer current
  | save parameter saved resume outer finish =>
    let caller := frame table.instance_ parameter
    let rest := expression (resume.erase table.bounded)
    exact (plug_steps table outer ((Steps.ctxtInstrs (vs := saved.erase.reverse) (rest := rest)
      (exit caller current)).trans (clear_trap caller saved.erase.reverse rest))).trans (finish caller)

private theorem tick_sound {count : Nat} {store : Store Unit} (table : Table (count := count) store)
    {P : Profile} {host : HostSemantics Unit} (state : Machine table) :
    Steps P host (state.erase table) ((tick table state).erase table) := by
  cases state with
  | returned | trapped => exact .refl
  | active parameter values code kont =>
    cases code with
    | done =>
      cases values with
      | cons bits tail =>
        cases tail
        cases kont with
        | root outer => exact leave_frame outer (frame table.instance_ parameter) bits
        | save caller saved resume outer => exact pop_sound table parameter bits saved resume caller outer
    | get next => exact get_sound table parameter values next kont
    | call slot resume =>
      cases values with
      | cons arg saved => exact push_sound table slot parameter arg saved resume kont
    | trap =>
      let current := frame table.instance_ parameter
      have step : Step P host ⟨store, current, [.plain .unreachable]⟩ ⟨store, current, [.trap]⟩ :=
        .parametric .unreachable
      have trapped := (Steps.ctxtInstrs (vs := values.erase.reverse) (rest := []) step.steps).trans
        (clear_trap current values.erase.reverse [])
      change Steps P host (kont.plug table current (vals values.erase.reverse ++ [.plain .unreachable]))
        ⟨store, kont.rootFrame, [.trap]⟩
      simpa only [List.append_nil] using (plug_steps table kont trapped).trans (close_trap table kont current)

private def self : Fin 2 := 0
private def base : Fin 2 := 1
private def demoBody (slot : Fin 2) : Code 2 [] :=
  if slot = self then .get (.call self .done) else .get .done

private def demoInst : ModuleInst := { types := [signature], funcs := List.ofFn Fin.val (n := 2) }
private theorem demoBound : (2 : Nat) ≤ 2 ^ 32 := by decide +kernel
private def demoStore : Store Unit :=
  { funcs := List.ofFn fun slot => ⟨signature, demoInst, .wasm (raw demoBound (demoBody slot))⟩ }

private def demoTable : Table (count := 2) demoStore where
  bounded := demoBound
  instance_ := demoInst
  address := Fin.val
  body := demoBody
  resolve slot := by simp only [demoInst, List.getElem?_ofFn, dite_eq_left slot.isLt]
  lookup slot := by simp only [demoStore, List.getElem?_ofFn, dite_eq_left slot.isLt]

private def demoContext : Context := { types := [signature], funcs := [signature, signature] }

private theorem signatureOk : TyOk {} signature := TyOk.check_sound (by decide +kernel)

private theorem demoFunctionOk (slot : Fin 2) : FuncOk demoContext (raw demoBound (demoBody slot)) signature := by
  apply defaultCheckers_sound.func
  by_cases isSelf : slot = self
  · subst slot; decide +kernel
  · have isBase : slot = base := by
      apply Fin.ext
      have nonzero : slot.val ≠ 0 := fun zero => isSelf (Fin.ext zero)
      have bounded := slot.isLt
      change slot.val = 1
      omega
    subst slot
    decide +kernel

private theorem demoStoreOk : StoreOk demoStore := by
  have instanceOk : ModuleInstOk demoStore demoInst demoContext :=
    ModuleInstOk.mk (k := 0) (by simpa [demoInst] using signatureOk) .nil .nil
      (.cons (.func (demoTable.lookup self)) (.cons (.func (demoTable.lookup base)) .nil)) .nil .nil
      (by simp [demoInst]) .nil (by simp [demoInst]) (by simp [demoInst]) (by simp [demoInst]) (by simp)
  constructor <;> try (solve | simp [demoStore])
  intro fn membership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp membership
  exact .wasm signatureOk instanceOk rfl (demoFunctionOk slot) (Sub.refl _ (k := .def) trivial signature)

private def start (bits : BitVec 32) : Machine demoTable := .active bits .nil (demoBody self) (.root {})
private def save (bits : BitVec 32) (outer : Kont 2) : Kont 2 := .save bits .nil .done outer

private theorem two_recursive_pushes {P : Profile} {host : HostSemantics Unit} (bits : BitVec 32) :
    Steps P host ((start bits).erase demoTable)
      ((Machine.active bits .nil (demoBody self) (save bits (save bits (.root {})))).erase demoTable) := by
  have step := tick_sound (P := P) (host := host) demoTable
  let initial := start bits
  let first := tick demoTable initial
  let second := tick demoTable first
  let third := tick demoTable second
  exact (((step initial).trans (step first)).trans (step second)).trans (step third)

example : run demoTable 64 (start 42) = .exhausted := by decide +kernel
example : run demoTable 8 (.active 42 .nil (.get (.call base .done)) (.root {})) = .returned 42 := by
  decide +kernel
example : run demoTable 1 (.active 42 .nil .trap (.root {})) = .trapped := by decide +kernel

#print axioms push_sound
#print axioms pop_sound
#print axioms tick_sound
#print axioms demoStoreOk
#print axioms two_recursive_pushes

end Silmaril.Wasm.IntrinsicRecursiveDemo
