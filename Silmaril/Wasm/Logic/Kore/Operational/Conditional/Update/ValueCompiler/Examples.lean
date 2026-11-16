module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.ValueCompiler.Thms
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
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Logic.Kore.Operational.Conditional.WasmBranch
abbrev local0 : LocalIdx := ⟨⟨0, by decide⟩⟩
abbrev local1 : LocalIdx := ⟨⟨1, by decide⟩⟩
def noTail : List String → List Admin := fun _ => []

/-- Authored KORE declarations: zero assigns1; nonzero assigns0. -/
def bytes : String := "  axiom{} \\rewrites{SortGeneratedTopCell{}} (\n      \\and{SortGeneratedTopCell{}} (\n        Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"a\")),Var'Unds'DotVar2:SortK{})),\\and{SortValCell{}}(Lbl'-LT-'val'-GT-'{}(VarX:SortInt{}),Var'Unds'Gen5:SortValCell{})),Var'Unds'DotVar0:SortGeneratedCounterCell{}),\n        \\equals{SortBool{},SortGeneratedTopCell{}}(\n        Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{},\\dv{SortInt{}}(\"0\")),\n        \\dv{SortBool{}}(\"true\"))),\n      \\and{SortGeneratedTopCell{}} (\n      Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"b\")),Var'Unds'DotVar2:SortK{})),Lbl'-LT-'val'-GT-'{}(\\dv{SortInt{}}(\"1\"))),Var'Unds'DotVar0:SortGeneratedCounterCell{}), \\top{SortGeneratedTopCell{}}()))\n  []\n  axiom{} \\rewrites{SortGeneratedTopCell{}} (\n      \\and{SortGeneratedTopCell{}} (\n        Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"a\")),Var'Unds'DotVar2:SortK{})),\\and{SortValCell{}}(Lbl'-LT-'val'-GT-'{}(VarX:SortInt{}),Var'Unds'Gen5:SortValCell{})),Var'Unds'DotVar0:SortGeneratedCounterCell{}),\n        \\equals{SortBool{},SortGeneratedTopCell{}}(\n        LblnotBool'Unds'{}(Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{},\\dv{SortInt{}}(\"0\"))),\n        \\dv{SortBool{}}(\"true\"))),\n      \\and{SortGeneratedTopCell{}} (\n      Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"c\")),Var'Unds'DotVar2:SortK{})),Lbl'-LT-'val'-GT-'{}(\\dv{SortInt{}}(\"0\"))),Var'Unds'DotVar0:SortGeneratedCounterCell{}), \\top{SortGeneratedTopCell{}}()))\n  []\n"

def names : Context := ⟨"Var'Unds'DotVar2", "VarX", "Var'Unds'Gen5", "Var'Unds'DotVar0"⟩
def zeroRule : Rule := ⟨"a", "b", .zero, .val, 1⟩
def nonzeroRule : Rule := ⟨"a", "c", .nonzero, .val, 0⟩
def program : CheckedProgram :=
  ⟨[⟨.ruleAxiom, [], zeroRule.tree names, []⟩,
    ⟨.ruleAxiom, [], nonzeroRule.tree names, []⟩], [(names, zeroRule), (names, nonzeroRule)]⟩

theorem checked_bytes : check bytes = some program := by
  have parsed : ((Text.tokenize bytes).bind fun tokens =>
      Text.declarations (tokens.length + 1) tokens) = some program.declarations := by
    decide +kernel
  have elaborated : program.declarations.mapM elaborate = some program.checked := by cbv
  change ((Text.tokenize bytes).bind fun tokens =>
    (Text.declarations (tokens.length + 1) tokens).bind fun ds =>
      (ds.mapM elaborate).bind fun pairs => some (⟨ds, pairs⟩ : CheckedProgram)) = _
  rw [← Option.bind_assoc, parsed]
  simp only [Option.bind_some, elaborated]

theorem program_axioms : program.axioms = [zeroRule, nonzeroRule] := by cbv

def output : (p : CheckedProgram) × Compiled p local0 noTail :=
  ⟨program, {
    layout := ⟨"a", "b", "c", by decide, by decide, by decide, .empty,
      BodyDraft.assignBody local0 (BitVec.ofInt 32 1),
      BodyDraft.assignBody local0 (BitVec.ofInt 32 0), noTail⟩
    zeroLiteral := 1
    nonzeroLiteral := 0
    zeroBody := rfl
    nonzeroBody := rfl
    blockType := rfl
    tail := rfl
    zeroRange := by decide
    nonzeroRange := by decide
    installed := program_axioms }⟩

theorem compiled_bytes : compileText bytes local0 noTail = some output := by
  unfold compileText
  rw [checked_bytes]
  simp [compile, Compiler.planFor, Compiler.plan, program_axioms, rules, output,
    zeroRule, nonzeroRule]

theorem code_updates_guard : output.2.layout.zeroBody = BodyDraft.assignBody local0 1 ∧
    output.2.layout.nonzeroBody = BodyDraft.assignBody local0 0 := by
  exact ⟨rfl, rfl⟩

/-- The genuine raw-source step is derived from the accepted original bytes. -/
theorem raw_zero (tail : List String) (k : BitVec 32) :
    Source.RawStep program.declarations ⟨"a" :: tail, 0, k.toInt⟩
      ⟨"b" :: tail, 1, k.toInt⟩ := by
  apply (Source.rawStep_iff_step checked_bytes _ _).mpr
  rw [program_axioms]
  exact Step.rule zeroRule (by simp) ⟨tail, 0, 0, k.toInt⟩ rfl
    (by change Guard.Holds .zero 0; simp [Guard.Holds, Guard.eval, intEqual])

theorem raw_nonzero (tail : List String) (q k : BitVec 32) (nonzero : q ≠ 0) :
    Source.RawStep program.declarations ⟨"a" :: tail, q.toInt, k.toInt⟩
      ⟨"c" :: tail, 0, k.toInt⟩ := by
  apply (Source.rawStep_iff_step checked_bytes _ _).mpr
  rw [program_axioms]
  exact Step.rule nonzeroRule (by simp) ⟨tail, q.toInt, q.toInt, k.toInt⟩ rfl
    (by
      change Guard.Holds .nonzero q.toInt
      simpa [Guard.Holds, Guard.eval, intEqual, signed_zero_iff] using nonzero)

/-- Populated initialized native frame; every maximal execution hits the actual
value update even with an arbitrary later continuation. -/
theorem actual_zero_af {H : Type} (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) (s : Store H) (tail : List String) (k : BitVec 32)
    (older : List Val) (rest : List Admin) :
    let f : Frame := { locals := [some (Val.i32 0), some (Val.i32 k)] }
    Silmaril.Logic.CTL.Sat
      (NativeTotal.predicateModel P host (native output.2.layout .entry s f older tail rest local0)
        (postRelated output.2.layout s f older tail rest local0 local1 0 k 1 0
          ⟨"b" :: tail, 1, k.toInt⟩)) NativeTotal.eventuallyTarget := by
  exact compileText_raw_af compiled_bytes P host s _ older tail rest local1 0 k
    (by decide) (by change (0 : Nat) < 2; decide) ⟨rfl, rfl⟩ _ (raw_zero tail k)

theorem actual_nonzero_af {H : Type} (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) (s : Store H) (tail : List String) (q k : BitVec 32)
    (nonzero : q ≠ 0) (older : List Val) (rest : List Admin) :
    let f : Frame := { locals := [some (Val.i32 q), some (Val.i32 k)] }
    Silmaril.Logic.CTL.Sat
      (NativeTotal.predicateModel P host (native output.2.layout .entry s f older tail rest local0)
        (postRelated output.2.layout s f older tail rest local0 local1 q k 1 0
          ⟨"c" :: tail, 0, k.toInt⟩)) NativeTotal.eventuallyTarget := by
  exact compileText_raw_af compiled_bytes P host s _ older tail rest local1 q k
    (by decide) (by change (0 : Nat) < 2; decide) ⟨rfl, rfl⟩ _ (raw_nonzero tail q k nonzero)

/-- The next guard observes the changed local, with the counter intact. -/
theorem zero_becomes_nonzero (f : Frame) (k : BitVec 32)
    (bound : local0.toNat < f.locals.length)
    (agree : LocalsAgree f local0 local1 0 k) :
    LocalsAgree (f.setLocal local0 (Val.i32 1)) local0 local1 1 k ∧
      Guard.Holds .nonzero (1 : BitVec 32).toInt ∧
      ¬ Guard.Holds .zero (1 : BitVec 32).toInt := by
  exact ⟨write_agrees f local0 local1 0 k 1 (by decide) bound agree,
    by change true = true; rfl, by change ¬ (false = true); decide⟩

theorem nonzero_becomes_zero (f : Frame) (q k : BitVec 32)
    (bound : local0.toNat < f.locals.length)
    (agree : LocalsAgree f local0 local1 q k) :
    LocalsAgree (f.setLocal local0 (Val.i32 0)) local0 local1 0 k ∧
      Guard.Holds .zero (0 : BitVec 32).toInt ∧
      ¬ Guard.Holds .nonzero (0 : BitVec 32).toInt := by
  exact ⟨write_agrees f local0 local1 q k 0 (by decide) bound agree,
    by change true = true; rfl, by change ¬ (false = true); decide⟩

/-- A wrong literal cannot describe the accepted raw-source successor. -/
theorem wrong_value (tail : List String) (k : BitVec 32) :
    ¬ Source.RawStep program.declarations ⟨"a" :: tail, 0, k.toInt⟩
      ⟨"b" :: tail, 2, k.toInt⟩ := by
  intro raw
  have step := (Source.rawStep_iff_step checked_bytes _ _).mp raw
  rw [program_axioms] at step
  have h := step_target output.2.layout tail 0 k 1 0 _ step
  have impossible := congrArg Config.val h
  change (2 : Int) = 1 at impossible
  exact (by decide : (2 : Int) ≠ 1) impossible

/-- Writing the counter instead leaves the guard value zero. -/
theorem wrong_native_target (k : BitVec 32) :
    let f : Frame := { locals := [some (Val.i32 0), some (Val.i32 k)] }
    Silmaril.Wasm.Logic.Core.localVal? (f.setLocal local1 (Val.i32 1)) local0 =
      some (Val.i32 0) := by rfl

/-- Counter-cell source rules cannot be installed by the value compiler. -/
theorem wrong_target : compile
    ⟨[⟨.ruleAxiom, [], ({ zeroRule with target := .counter }).tree names, []⟩,
      ⟨.ruleAxiom, [], nonzeroRule.tree names, []⟩], []⟩ local0 noTail = none := by
  cbv

/-- The same two original rule bodies, retained literally with claim headers.
No opaque runtime string-search implementation occurs in the kernel proof. -/
def claimBytes : String := "  claim{} \\rewrites{SortGeneratedTopCell{}} (\n      \\and{SortGeneratedTopCell{}} (\n        Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"a\")),Var'Unds'DotVar2:SortK{})),\\and{SortValCell{}}(Lbl'-LT-'val'-GT-'{}(VarX:SortInt{}),Var'Unds'Gen5:SortValCell{})),Var'Unds'DotVar0:SortGeneratedCounterCell{}),\n        \\equals{SortBool{},SortGeneratedTopCell{}}(\n        Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{},\\dv{SortInt{}}(\"0\")),\n        \\dv{SortBool{}}(\"true\"))),\n      \\and{SortGeneratedTopCell{}} (\n      Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"b\")),Var'Unds'DotVar2:SortK{})),Lbl'-LT-'val'-GT-'{}(\\dv{SortInt{}}(\"1\"))),Var'Unds'DotVar0:SortGeneratedCounterCell{}), \\top{SortGeneratedTopCell{}}()))\n  []\n  claim{} \\rewrites{SortGeneratedTopCell{}} (\n      \\and{SortGeneratedTopCell{}} (\n        Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"a\")),Var'Unds'DotVar2:SortK{})),\\and{SortValCell{}}(Lbl'-LT-'val'-GT-'{}(VarX:SortInt{}),Var'Unds'Gen5:SortValCell{})),Var'Unds'DotVar0:SortGeneratedCounterCell{}),\n        \\equals{SortBool{},SortGeneratedTopCell{}}(\n        LblnotBool'Unds'{}(Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{},\\dv{SortInt{}}(\"0\"))),\n        \\dv{SortBool{}}(\"true\"))),\n      \\and{SortGeneratedTopCell{}} (\n      Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortState{}, SortKItem{}}(\\dv{SortState{}}(\"c\")),Var'Unds'DotVar2:SortK{})),Lbl'-LT-'val'-GT-'{}(\\dv{SortInt{}}(\"0\"))),Var'Unds'DotVar0:SortGeneratedCounterCell{}), \\top{SortGeneratedTopCell{}}()))\n  []\n"

private def claimProgram : CheckedProgram :=
  ⟨[⟨.claim, [], zeroRule.tree names, []⟩,
    ⟨.claim, [], nonzeroRule.tree names, []⟩], [(names, zeroRule), (names, nonzeroRule)]⟩

private theorem checked_claims : check claimBytes = some claimProgram := by
  have parsed : ((Text.tokenize claimBytes).bind fun tokens =>
      Text.declarations (tokens.length + 1) tokens) = some claimProgram.declarations := by
    decide +kernel
  have elaborated : claimProgram.declarations.mapM elaborate = some claimProgram.checked := by cbv
  change ((Text.tokenize claimBytes).bind fun tokens =>
    (Text.declarations (tokens.length + 1) tokens).bind fun ds =>
      (ds.mapM elaborate).bind fun pairs => some (⟨ds, pairs⟩ : CheckedProgram)) = _
  rw [← Option.bind_assoc, parsed]
  simp only [Option.bind_some, elaborated]

theorem claims_rejected : compileText claimBytes local0 noTail = none := by
  unfold compileText
  rw [checked_claims]
  simp [compile, Compiler.planFor, Compiler.plan, CheckedProgram.axioms, claimProgram]

theorem malformed_rejected : compileText (bytes ++ "module EXTRA") local0 noTail = none := by
  cbv

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler.Examples
