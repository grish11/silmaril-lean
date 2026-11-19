module
public import Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Source.Elaboration.Thms
public import Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Source.Projection.Thms
public import Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Thms
public import Silmaril.Project.Shapes.Contextual.Defs
public import Silmaril.X86.Open.Thms
/-! Actual unsigned-char parameter object, promotion/short-circuit Core and O0 ELF.
The byte parameter is passed in DIL; upper register bits are unconstrained. There
are no globals, callees or supplied refinement laws. All semantic obligations
remain unproved. This is a function slice, not whole darkhttpd correctness. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Context
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes Silmaril.Project.Shapes.Contextual

def placement : Silmaril.Project.Shapes.Placement := ⟨address, code, 0⟩
def parameterAddress : Int := 2097152
/-- Initialize the actual one-byte parameter object, then mark it readonly.
The entry relation contains no expected result or source-to-target validity law. -/
def prepare (input : BitVec 8) : Except String State := do
  let F := Source.Elaboration.function
  let [(parameter, type)] := F.params | throw "actual one-parameter procedure required"
  let .mk _ (.basic (.integer (.unsigned .ichar))) := type | throw "actual unsigned-char parameter required"
  let layout ← (Mem.Concrete.typeLayout 64 F.file.tagDefs type).mapError (fun _ => "parameter layout failed")
  unless layout.size == 1 && layout.align == 1 do throw "actual byte layout mismatch"
  let allocation : Mem.Concrete.Allocation := ⟨parameterAddress, 1, false, false, some type, none, .UB064_modifying_const⟩
  let before : Mem.Concrete.State := {nextId := 1, lastAddress := parameterAddress + 1, allocations := Map.ofList [(0, allocation)]}
  let (_, initialized) ← (Mem.Concrete.storeTyped F.file.tagDefs before type
    (.allocated 0 parameterAddress) (.integer (.unsigned .ichar) input.toNat)).mapError (fun _ => "parameter initialization failed")
  let memory := {initialized with allocations := Map.ofList [(0, {allocation with readonly := some .UB064_modifying_const})]}
  let env := extendEnv [(parameter, .object (.pointer (.allocated 0 parameterAddress)))] ∅
  return ⟨.effectExpr F.body env, [.procedureReturn F.bodyLabels], memory⟩

abbrev Observation := Option Int × Prop

def context : Context (BitVec 8) Observation where
  sourceEntry input s := prepare input = .ok s
  machineEntry input m := SysV.CallEntry placement Source.signature 12 (.cons input .nil) m
  related _ _ _ := True
  footprint _ m := SysV.StackBelow m 12
  sourceObservation _ s t v :=
    (match v with | .loaded (.specified (.integer n)) => some n | _ => none,
      -- Diagnostic source locations are not C memory effects. Every other field is observed.
      {t.memory with currentLocation := s.memory.currentLocation} = s.memory)
  machineObservation _ _ t := (some ((t.core.read .rax).setWidth 32).toInt, True)
  callees := []

/-- Nonvacuous safety, first-return ABI and source/target observation obligations
for every unsigned byte. The twelve private stack bytes cover O0's RBP save and
one-byte local at entry RSP-12; all other target memory must be preserved. -/
@[problem "silmaril.corpus.darkhttpd.needs_logencoding.contextual"
  (title := "Actual darkhttpd unsigned-byte log-encoding predicate with source/Core/ELF context")]
def Task.compilesTo : Prop :=
  Source.Projection.exact ∧
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.CorpusVariants.Darkhttpd.N117.Default.X8664.O0.Unstripped.DarkhttpdBinary.F address code ∧
  C.ElaboratesWith Source.inputs Source.ail "needs_logencoding" Source.Elaboration.function ∧
  Obligation Source.Elaboration.function Silmaril.X86.Open.isa placement context
end Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Context
