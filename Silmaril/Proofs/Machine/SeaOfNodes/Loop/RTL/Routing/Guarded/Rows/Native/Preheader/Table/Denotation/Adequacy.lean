module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Denotation.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Prog run_returned)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Primitive encode_injective inputEnv instruction instruction_deterministic)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {arity : Nat} {entrySigs sigs : List (List PortTy)}

private theorem witnessed_iff {α : Type} (observe : α → Prop)
    (unique : ∀ {a b}, observe a → observe b → a = b) (a : α) :
    a ∈ (⟨∃ b, observe b, Classical.choose⟩ : Part α) ↔ observe a := by
  rw [Part.mem_mk_iff]
  constructor
  · rintro ⟨witness, rfl⟩
    exact Classical.choose_spec witness
  · intro seen
    let witness : ∃ b, observe b := ⟨a, seen⟩
    exact ⟨witness, unique (Classical.choose_spec witness) seen⟩

private theorem packed_injective :
    Function.Injective (Generic.packResult model (out := word)) :=
  fun _ _ same => encode_injective model (Value.pair.inj same).1

theorem mem_rtlDenote_iff (target : Prog Reg) (input : WordTuple arity)
    (initial final : Memory) (value : Word) :
    (value, final) ∈ rtlDenote target input initial ↔ target.oracle 0 (words input) initial [value] final := by
  refine witnessed_iff (fun result : Word × Memory => result ∈ Rows.rtlObservation target input initial)
    ?_ (value, final)
  rintro ⟨x, memX⟩ ⟨y, memY⟩ left right
  have ⟨values, memory⟩ := target.oracle_deterministic 0 (words input) initial [x] memX [y] memY left right
  exact Prod.ext (List.cons.inj values).1 memory

theorem mem_lambdaDenote_iff (target : Region (Primitive WordOp)) (input : WordTuple arity)
    (initial final : Memory) (value : Word) :
    (value, final) ∈ lambdaDenote target input initial ↔
      Eval (instruction model) (inputEnv model input) target initial 0
        (Generic.packResult model (out := word) value) final := by
  refine witnessed_iff (fun result : Word × Memory => result ∈ Rows.lambdaObservation target input initial)
    ?_ (value, final)
  rintro ⟨x, memX⟩ ⟨y, memY⟩ left right
  have ⟨_, payload, memory⟩ := Eval.deterministic (instruction_deterministic model) left right
  exact Prod.ext (packed_injective payload) memory

theorem mem_rtlDenote_iff_runMain (target : Prog Reg) (input : WordTuple arity)
    (initial final : Memory) (value : Word) :
    (value, final) ∈ rtlDenote target input initial ↔
      ∃ fuel, target.runMain fuel 0 (words input) initial = .returned [value] final := by
  rw [mem_rtlDenote_iff]
  constructor
  · rintro ⟨start, started, finish, steps, result⟩
    obtain ⟨fuel, observed⟩ := fuel_of_steps steps result
    exact ⟨fuel, by simpa only [Prog.runMain, started] using observed⟩
  · rintro ⟨fuel, observed⟩
    unfold Prog.runMain at observed
    split at observed
    · exact ⟨_, by assumption, run_returned observed⟩
    · cases observed

variable {g : SourceWithEntry arity entrySigs sigs} {targets : Checked.Phi.Targets}

theorem lambda_run_succ_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (value : Word) (budget : Nat) :
    Generic.Fuel.run model (inputEnv model input) (budget + 1) targets.2 =
        some (0, Generic.packResult model (out := word) value) ↔
      ∃ count ≤ budget, g.ReturnsAfter model input count (g.initial model input) value := by
  rw [Table.lambda_run_succ accepted, ← g.evalBackedges_eq_some_iff model input value budget]
  cases g.evalBackedges model budget input with
  | none => simp
  | some actual =>
    constructor
    · intro observed
      exact congrArg some (packed_injective (congrArg Prod.snd (Option.some.inj observed)))
    · intro same
      rw [same]
      rfl

private theorem lambda_run_iff_returns (accepted : lowerChecked g = some targets)
    (input : WordTuple arity) (value : Word) :
    (∃ visits, Generic.Fuel.run model (inputEnv model input) visits targets.2 =
        some (0, Generic.packResult model (out := word) value)) ↔ g.Returns model input value := by
  constructor
  · rintro ⟨visits, observed⟩
    cases visits with
    | zero =>
      obtain ⟨_, _, _, rfl⟩ := Table.lowerChecked_sound accepted
      rw [Generic.Fuel.run_zero g model input] at observed
      cases observed
    | succ budget =>
      obtain ⟨count, _, returned⟩ := (lambda_run_succ_iff accepted input value budget).mp observed
      exact ⟨count, returned⟩
  · rintro ⟨count, returned⟩
    exact ⟨count + 1, (lambda_run_succ_iff accepted input value count).mpr ⟨count, le_rfl, returned⟩⟩

theorem mem_lambdaDenote_iff_run (accepted : lowerChecked g = some targets)
    (input : WordTuple arity) (initial final : Memory) (value : Word) :
    (value, final) ∈ lambdaDenote targets.2 input initial ↔ final = initial ∧
      ∃ visits, Generic.Fuel.run model (inputEnv model input) visits targets.2 =
        some (0, Generic.packResult model (out := word) value) := by
  rw [mem_lambdaDenote_iff, Table.lambda_return_iff accepted, lambda_run_iff_returns accepted]
  constructor
  · rintro ⟨actual, returned, _, packed, memory⟩
    obtain rfl := packed_injective packed
    exact ⟨memory, returned⟩
  · rintro ⟨memory, returned⟩
    exact ⟨value, returned, rfl, rfl, memory⟩

private theorem mem_native (input : WordTuple arity) (initial final : Memory) (value : Word) :
    (value, final) ∈ nativeDenote g input initial ↔ g.Returns model input value ∧ final = initial := by
  let source : Part Word := g.denote model input
  change (value, final) ∈ source.map (fun word => (word, initial)) ↔ _
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨actual, present, same⟩
    obtain ⟨wordEq, memory⟩ := Prod.mk.inj same
    subst actual
    exact ⟨(g.returns_iff_mem_denote model input value).mpr present, memory.symm⟩
  · rintro ⟨returned, rfl⟩
    exact ⟨value, (g.returns_iff_mem_denote model input value).mp returned, rfl⟩

theorem denotations_eq (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial : Memory) :
    rtlDenote targets.1 input initial = nativeDenote g input initial ∧
      lambdaDenote targets.2 input initial = nativeDenote g input initial := by
  obtain ⟨p, recognized, _, _⟩ := Table.lowerChecked_sound accepted
  constructor
  · apply Part.ext
    rintro ⟨value, final⟩
    rw [mem_rtlDenote_iff_runMain, mem_native]
    constructor
    · rintro ⟨fuel, observed⟩
      obtain ⟨count, actual, returned, _, words, memory⟩ :=
        (Table.rtl_runMain_fuel_iff recognized accepted input initial final [value] fuel).mp observed
      obtain rfl := (List.cons.inj words).1
      exact ⟨⟨count, returned⟩, memory⟩
    · rintro ⟨⟨count, returned⟩, memory⟩
      exact ⟨p.rtlFuel count,
        (Table.rtl_runMain_fuel_iff recognized accepted input initial final [value] _).mpr
          ⟨count, value, returned, le_rfl, rfl, memory⟩⟩
  · apply Part.ext
    rintro ⟨value, final⟩
    rw [mem_lambdaDenote_iff_run accepted, lambda_run_iff_returns accepted, mem_native]
    exact and_comm

theorem denotations_none_iff (accepted : lowerChecked g = some targets)
    (input : WordTuple arity) (initial : Memory) :
    (rtlDenote targets.1 input initial = Part.none ↔ g.denote model input = Part.none) ∧
      (lambdaDenote targets.2 input initial = Part.none ↔ g.denote model input = Part.none) := by
  obtain ⟨rtl, typed⟩ := denotations_eq accepted input initial
  have source : nativeDenote g input initial = Part.none ↔ g.denote model input = Part.none := by
    simp only [Part.eq_none_iff']
    rfl
  rw [rtl, typed]
  exact ⟨source, source⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs
