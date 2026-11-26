module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Provider.Relocation.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.RelocationProofs

open NestedTheta.Liveness (Demand)
open Continuation.Partial (Config)
open Continuation.Partial.Executable (Actions)
open Isomorphism (OutcomesRelated)
open Isomorphism.RecursiveCall (Admitted ClosedFamily)
open Isomorphism.RecursiveCall.Numbered (ExportAdmission ordinaryPorts)
open Isomorphism.RecursiveCall.Numbered.Prefix (AdmittedExport)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {actions : Actions m σ}
variable {ids : GlobalRel} {summary : MemberSummary V S}
variable {left right : Outcome m σ [summary.fn.port]}

private theorem related_of_ports : {ports : Ports (Ty V S)} → (a b : Tuple m.Val ports) →
    (∀ {ty} (p : Port ports ty), ValueRelated m ids (a.get p) (b.get p)) → TupleRelated m ids a b
  | [], .nil, .nil, _ => .nil
  | _ :: _, .cons _ tailA, .cons _ tailB, ports =>
    .cons (ports .head) (related_of_ports tailA tailB (fun p => ports (.tail p)))

theorem substitute_related (a : ExportAnalysis actions summary left left)
    (b : ExportAnalysis actions summary right right)
    (demand : Demand) {argsL argsR replacementsL replacementsR : Tuple m.Val summary.fn.args}
    (args : TupleRelated m ids argsL argsR) (replacements : TupleRelated m ids replacementsL replacementsR) :
    TupleRelated m ids (a.substituteDeadFormals demand argsL replacementsL)
      (b.substituteDeadFormals demand argsR replacementsR) := by
  apply related_of_ports
  intro ty port
  rw [a.substituteDeadFormals_get, b.substituteDeadFormals_get]
  change ValueRelated m ids (if a.liveFormal demand port then argsL.get port else replacementsL.get port)
    (if a.liveFormal demand port then argsR.get port else replacementsR.get port)
  split
  · exact args.get port
  · exact replacements.get port

private theorem linked_store {ports : Ports (Ty V S)} {rename : Nat → Nat}
    {valuesL valuesR : Tuple m.Val ports} {storeL storeR : σ}
    (linked : OutcomesRelated m ids σ rename ports (.linked valuesL storeL) (.linked valuesR storeR)) :
    storeL = storeR := by cases linked; rfl

theorem substituted_starts {importsL importsR : Ports (Ty V S)}
    {sigsL sigsR : List (Ports (Ty V S))} {unitL unitR : Nat}
    {graphL : Omega Op importsL [summary.fn.port] sigsL} {graphR : Omega Op importsR [summary.fn.port] sigsR}
    {inputsL : Tuple m.Val importsL} {inputsR : Tuple m.Val importsR} {initialL initialR : σ}
    {rename : Nat → Nat}
    (a : ExportAnalysis actions summary (Executable.link actions unitL graphL inputsL initialL)
      (Executable.link actions unitL graphL inputsL initialL))
    (b : ExportAnalysis actions summary (Executable.link actions unitR graphR inputsR initialR)
      (Executable.link actions unitR graphR inputsR initialR))
    (linked : OutcomesRelated m ids σ rename [summary.fn.port]
      (Executable.link actions unitL graphL inputsL initialL)
      (Executable.link actions unitR graphR inputsR initialR))
    (admitted : AdmittedExport actions.toPrimitives ids (fn := summary.fn) .head
      (Executable.link actions unitL graphL inputsL initialL)
      (Executable.link actions unitR graphR inputsR initialR))
    (demand : Demand) {argsL argsR replacementsL replacementsR : Tuple m.Val summary.fn.args}
    (args : TupleRelated m ids argsL argsR) (replacements : TupleRelated m ids replacementsL replacementsR)
    (ordinary : ordinaryPorts summary.fn.args = true) :
    ∃ familyL familyR, ∃ startL startR : Config m σ summary.fn.results,
      Executable.start actions unitL graphL inputsL .head (a.substituteDeadFormals demand argsL replacementsL)
        initialL = .ok startL ∧
      Executable.start actions unitR graphR inputsR .head (b.substituteDeadFormals demand argsR replacementsR)
        initialR = .ok startR ∧
      ClosedFamily actions.toPrimitives ids familyL familyR ∧ Admitted m ids familyL familyR startL startR := by
  rw [a.linked.linkedL, b.linked.linkedL] at linked admitted
  have common := linked_store linked
  rw [← common] at linked admitted
  obtain ⟨familyL, familyR, closed, ready⟩ :=
    ExportAdmission.atExport .head linked admitted (substitute_related a b demand args replacements) ordinary
  exact ⟨familyL, familyR, _, _, by simp only [Executable.start, a.linked.linkedL]; rfl,
    by simp only [Executable.start, b.linked.linkedL, ← common]; rfl, closed, ready⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.RelocationProofs
