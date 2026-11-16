module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Compiler.Thms
import all Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Compiler.Defs
import all Init.Data.String.Search
import all Init.Data.String.Slice.Numeric
import all Init.Data.String.Slice.Pattern
import all Init.Data.String.Basic
import all Init.Data.Int.Repr
import all Init.Data.Repr

@[expose] public section
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Compiler.Examples
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Logic.Kore.Operational.Conditional.WasmBranch

abbrev local0 : LocalIdx := ⟨⟨0, by decide⟩⟩
abbrev local1 : LocalIdx := ⟨⟨1, by decide⟩⟩
def noTail : List String → List Admin := fun _ => []

/-- Concatenates the two existing unchanged manually authored rule fixtures. -/
def bytes : String := authoredZeroBytes ++ authoredNonzeroBytes

def names : Context := ⟨"Var'Unds'DotVar2", "VarX", "Var'Unds'Gen5", "Var'Unds'DotVar0"⟩
def programFor (entry zero nonzero : String) (z n : Int) : CheckedProgram :=
  let r0 : Rule := ⟨entry, zero, .zero, .counter, z⟩
  let r1 : Rule := ⟨entry, nonzero, .nonzero, .counter, n⟩
  ⟨[⟨.ruleAxiom, [], r0.tree names, []⟩, ⟨.ruleAxiom, [], r1.tree names, []⟩],
    [(names, r0), (names, r1)]⟩

def program : CheckedProgram := programFor "a" "b" "c" 11 13

private theorem checked_of_parsed (input : String) (p : CheckedProgram)
    (parsed : ((Text.tokenize input).bind fun tokens =>
      Text.declarations (tokens.length + 1) tokens) = some p.declarations)
    (elaborated : p.declarations.mapM elaborate = some p.checked) : check input = some p := by
  change ((Text.tokenize input).bind fun tokens =>
    (Text.declarations (tokens.length + 1) tokens).bind fun ds =>
      (ds.mapM elaborate).bind fun pairs => some (⟨ds, pairs⟩ : CheckedProgram)) = _
  rw [← Option.bind_assoc, parsed]
  simp only [Option.bind_some, elaborated]

/-- Both original byte declarations parse before the compiler is involved. -/
theorem checked_bytes : check bytes = some program := by
  apply checked_of_parsed
  · decide +kernel
  · cbv

theorem program_axioms : program.axioms =
    [⟨"a", "b", .zero, .counter, 11⟩, ⟨"a", "c", .nonzero, .counter, 13⟩] := by
  unfold CheckedProgram.axioms program programFor
  cbv

def output : (p : CheckedProgram) × Compiled p local1 noTail :=
  ⟨program, {
    layout := ⟨"a", "b", "c", by decide, by decide, by decide, .empty,
      BodyDraft.assignBody local1 (BitVec.ofInt 32 11),
      BodyDraft.assignBody local1 (BitVec.ofInt 32 13), noTail⟩
    zeroLiteral := 11
    nonzeroLiteral := 13
    installed := program_axioms
    zeroBody := rfl
    nonzeroBody := rfl
    blockType := rfl
    tail := rfl
    zeroRange := by decide
    nonzeroRange := by decide }⟩

theorem compiled_bytes : compileText bytes local1 noTail = some output := by
  unfold compileText
  rw [checked_bytes]
  simp [compile, plan, program_axioms, Native.rules, output]

theorem code_from_bytes : output.2.layout.entry = "a" ∧
    output.2.layout.zero = "b" ∧ output.2.layout.nonzero = "c" ∧
    output.2.zeroLiteral = 11 ∧ output.2.nonzeroLiteral = 13 ∧
    output.2.layout.zeroBody = BodyDraft.assignBody local1 (BitVec.ofInt 32 11) ∧
    output.2.layout.nonzeroBody = BodyDraft.assignBody local1 (BitVec.ofInt 32 13) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Real source transition, with no supplied installed-list premise. -/
theorem raw_move (tail : List String) (q k : BitVec 32) :
    Source.RawStep output.1.declarations (Native.entrySource output.2.layout tail q k)
      (Native.afterSource output.2.layout tail q output.2.zeroLiteral output.2.nonzeroLiteral) := by
  apply (Source.rawStep_iff_step (compileText_sound compiled_bytes).1 _ _).mpr
  rw [output.2.installed]
  exact (Native.source_step_iff _ _ _ _ _ _ _).mpr rfl

/-- A populated initialized frame meets all runtime premises. The post is the
actual raw-source successor; its counter is11or13 as computed from the bytes. -/
theorem actual_matching {H : Type} (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) (s : Store H) (tail : List String) (q k : BitVec 32)
    (rest : List Admin) :
    let f : Frame := { locals := [some (Val.i32 q), some (Val.i32 k)] }
    (Silmaril.Logic.Matching.FixedPoint.expandModal
      (Silmaril.Logic.CTL.expandMu
        (NativeTotal.predicateModel P host (native output.2.layout .entry s f [] tail rest local0)
          (Native.postRelated output.2.layout s f [] tail rest local0 local1 q
            output.2.zeroLiteral output.2.nonzeroLiteral
            (Native.afterSource output.2.layout tail q output.2.zeroLiteral output.2.nonzeroLiteral))))).Satisfies
      (Silmaril.Logic.Matching.FixedPoint.encodeModal NativeTotal.eventuallyTarget.toMu) := by
  exact compileText_raw_matching compiled_bytes P host s _ [] tail rest local0 q k
    (by decide) (by change (1 : Nat) < 2; decide) ⟨rfl, rfl⟩ _ (raw_move tail q k)

/-- Source changes modify actual emitted names and native literal instructions. -/
def changedBytes : String := "  axiom{} \\rewrites{SortGeneratedTopCell{}} (\n      \\and{SortGeneratedTopCell{}} (\n        Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"start\")),Var'Unds'DotVar2:SortK{})),\\and{SortValCell{}}(Lbl'-LT-'val'-GT-'{}(VarX:SortInt{}),Var'Unds'Gen5:SortValCell{})),Var'Unds'DotVar0:SortGeneratedCounterCell{}),\n        \\equals{SortBool{},SortGeneratedTopCell{}}(\n        Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{},\\dv{SortInt{}}(\"0\")),\n        \\dv{SortBool{}}(\"true\"))),\n      \\and{SortGeneratedTopCell{}} (\n      Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"doneZero\")),Var'Unds'DotVar2:SortK{})),Var'Unds'Gen5:SortValCell{}),Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"17\"))), \\top{SortGeneratedTopCell{}}()))\n  []\n  axiom{} \\rewrites{SortGeneratedTopCell{}} (\n      \\and{SortGeneratedTopCell{}} (\n        Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"start\")),Var'Unds'DotVar2:SortK{})),\\and{SortValCell{}}(Lbl'-LT-'val'-GT-'{}(VarX:SortInt{}),Var'Unds'Gen5:SortValCell{})),Var'Unds'DotVar0:SortGeneratedCounterCell{}),\n        \\equals{SortBool{},SortGeneratedTopCell{}}(\n        LblnotBool'Unds'{}(Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{},\\dv{SortInt{}}(\"0\"))),\n        \\dv{SortBool{}}(\"true\"))),\n      \\and{SortGeneratedTopCell{}} (\n      Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"c\")),Var'Unds'DotVar2:SortK{})),Var'Unds'Gen5:SortValCell{}),Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"19\"))), \\top{SortGeneratedTopCell{}}()))\n  []\n"

def changedProgram : CheckedProgram := programFor "start" "doneZero" "c" 17 19

theorem changed_checked : check changedBytes = some changedProgram := by
  apply checked_of_parsed
  · decide +kernel
  · cbv

theorem changed_axioms : changedProgram.axioms =
    [⟨"start", "doneZero", .zero, .counter, 17⟩, ⟨"start", "c", .nonzero, .counter, 19⟩] := by
  unfold CheckedProgram.axioms changedProgram programFor
  cbv

def changed : (p : CheckedProgram) × Compiled p local1 noTail :=
  ⟨changedProgram, {
    layout := ⟨"start", "doneZero", "c", by decide, by decide, by decide, .empty,
      BodyDraft.assignBody local1 (BitVec.ofInt 32 17),
      BodyDraft.assignBody local1 (BitVec.ofInt 32 19), noTail⟩
    zeroLiteral := 17
    nonzeroLiteral := 19
    installed := changed_axioms
    zeroBody := rfl
    nonzeroBody := rfl
    blockType := rfl
    tail := rfl
    zeroRange := by decide
    nonzeroRange := by decide }⟩

theorem changed_compiles : compileText changedBytes local1 noTail = some changed := by
  unfold compileText
  rw [changed_checked]
  simp [compile, plan, changed_axioms, Native.rules, changed]

theorem changed_code : changed.2.layout.entry = "start" ∧
    changed.2.layout.zero = "doneZero" ∧ changed.2.zeroLiteral = 17 ∧
    changed.2.nonzeroLiteral = 19 ∧
    changed.2.layout.zeroBody = BodyDraft.assignBody local1 (BitVec.ofInt 32 17) ∧
    changed.2.layout.nonzeroBody = BodyDraft.assignBody local1 (BitVec.ofInt 32 19) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The changed source is interpreted, not merely carried as unused bytes. -/
theorem changed_raw_move (tail : List String) (q k : BitVec 32) :
    Source.RawStep changed.1.declarations (Native.entrySource changed.2.layout tail q k)
      (Native.afterSource changed.2.layout tail q changed.2.zeroLiteral changed.2.nonzeroLiteral) := by
  apply (Source.rawStep_iff_step (compileText_sound changed_compiles).1 _ _).mpr
  rw [changed.2.installed]
  exact (Native.source_step_iff _ _ _ _ _ _ _).mpr rfl

theorem changed_actual_matching {H : Type} (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) (s : Store H) (tail : List String) (q k : BitVec 32)
    (rest : List Admin) :
    let f : Frame := { locals := [some (Val.i32 q), some (Val.i32 k)] }
    (Silmaril.Logic.Matching.FixedPoint.expandModal
      (Silmaril.Logic.CTL.expandMu
        (NativeTotal.predicateModel P host (native changed.2.layout .entry s f [] tail rest local0)
          (Native.postRelated changed.2.layout s f [] tail rest local0 local1 q
            changed.2.zeroLiteral changed.2.nonzeroLiteral
            (Native.afterSource changed.2.layout tail q changed.2.zeroLiteral changed.2.nonzeroLiteral))))).Satisfies
      (Silmaril.Logic.Matching.FixedPoint.encodeModal NativeTotal.eventuallyTarget.toMu) := by
  exact compileText_raw_matching changed_compiles P host s _ [] tail rest local0 q k
    (by decide) (by change (1 : Nat) < 2; decide) ⟨rfl, rfl⟩ _ (changed_raw_move tail q k)

/-- Existing checked singleton bytes cannot supply a complementary branch. -/
example : compileText authoredZeroBytes local1 noTail = none := by
  unfold compileText
  cases hp : check authoredZeroBytes with
  | none => simp
  | some p =>
    have installed : p.axioms = [⟨"a", "b", .zero, .counter, 11⟩] := by
      simpa only [hp, Option.map_some, Option.some.injEq] using authored_zero_checked
    simp [compile, plan, installed]

/-- Source range checking remains effective before compilation. -/
example : compileText outOfRangeBytes local1 noTail = none := by
  simp [compileText, out_of_range_rejected]

/-- Compiler-specific rejection on otherwise elaboratable source rule trees. -/
def fromRules (rs : List Rule) : CheckedProgram :=
  ⟨rs.map (fun r => ⟨.ruleAxiom, [], r.tree names, []⟩), []⟩

example : compile (fromRules [⟨"a", "b", .zero, .val, 11⟩,
    ⟨"a", "c", .nonzero, .counter, 13⟩]) local1 noTail = none := by
  unfold compile plan CheckedProgram.axioms
  unfold fromRules
  cbv
example : compile (fromRules [⟨"a", "b", .zero, .counter, 11⟩,
    ⟨"a", "c", .nonzero, .counter, 13⟩, ⟨"a", "d", .zero, .counter, 17⟩])
    local1 noTail = none := by
  unfold compile plan CheckedProgram.axioms
  unfold fromRules
  cbv
example : compile (fromRules [⟨"a", "a", .zero, .counter, 11⟩,
    ⟨"a", "c", .nonzero, .counter, 13⟩]) local1 noTail = none := by
  unfold compile plan CheckedProgram.axioms
  unfold fromRules
  cbv

example : compile (fromRules [⟨"a", "b", .zero, .counter, 11⟩,
    ⟨"a", "b", .zero, .counter, 11⟩]) local1 noTail = none := by
  unfold compile plan CheckedProgram.axioms
  unfold fromRules
  cbv
example : compile (fromRules [⟨"a", "b", .zero, .counter, 11⟩,
    ⟨"other", "c", .nonzero, .counter, 13⟩]) local1 noTail = none := by
  unfold compile plan CheckedProgram.axioms
  unfold fromRules
  cbv
example : compile (⟨program.declarations.map (fun d => { d with kind := .claim }), []⟩ : CheckedProgram)
    local1 noTail = none := by
  unfold compile plan CheckedProgram.axioms
  cbv

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Compiler.Examples
