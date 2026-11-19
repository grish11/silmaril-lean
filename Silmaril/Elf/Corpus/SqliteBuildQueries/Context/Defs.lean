module
public import Silmaril.Elf.Corpus.SqliteBuildQueries.Source.Elaboration.Thms
public import Silmaril.Elf.Corpus.SqliteBuildQueries.Source.Projection.Thms
public import Silmaril.Elf.Corpus.SqliteBuildQueries.Thms
public import Silmaril.Project.Shapes.Contextual.Defs
public import Silmaril.X86.Open.Thms
/-! Actual canonical build-query procedures. The version and SQLITE_THREADSAFE=1
constants come from the exact recorded preprocessing spans, not a substituted
Core body. No threading, mutex or complete SQLite semantics are certified. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteBuildQueries.Context
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes Silmaril.Project.Shapes.Contextual

def placement (g : Getter) : Silmaril.Project.Shapes.Placement := ⟨g.address, g.code, 0⟩

def prepare (g : Getter) : State :=
  let F := Source.Elaboration.function g
  ⟨.effectExpr F.body ∅, [.procedureReturn F.bodyLabels], {}⟩

abbrev Observation := Option Int × Prop

def context (g : Getter) : Context Unit Observation where
  sourceEntry _ s := s = prepare g
  machineEntry _ m := SysV.CallEntry (placement g) Source.signature 0 .nil m
  related _ _ _ := True
  footprint _ m := SysV.StackBelow m 0
  sourceObservation _ s t v :=
    (match v with | .loaded (.specified (.integer n)) => some n | _ => none,
     t.memory.allocations = s.memory.allocations ∧ t.memory.bytes = s.memory.bytes ∧
       t.memory.dead = s.memory.dead ∧ t.memory.stdout = s.memory.stdout)
  machineObservation _ _ t := (some ((t.core.read .rax).setWidth 32).toInt, True)
  callees := []

/-- Actual source/Core identity and real ELF CodeAt are conjuncts, with full
joint-entry/safety/first-return/ABI/effect obligations. No desired result or
refinement premise appears in the entry relation. This remains unproved. -/
def statement (g : Getter) : Prop :=
  Source.Projection.exact ∧
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F g.address g.code ∧
  C.ElaboratesWith Source.inputs Source.ail g.name (Source.Elaboration.function g) ∧
  Obligation (Source.Elaboration.function g) Silmaril.X86.Open.isa (placement g) (context g)

@[problem "silmaril.corpus.sqlite.libversion_number.contextual"
  (title := "Actual SQLite numeric version build query with signed-int ABI")]
def Task.versionNumber : Prop := statement .versionNumber
@[problem "silmaril.corpus.sqlite.threadsafe.contextual"
  (title := "Actual SQLite THREADSAFE build option query with signed-int ABI")]
def Task.threadsafe : Prop := statement .threadsafe
end Silmaril.Elf.Corpus.SqliteBuildQueries.Context
