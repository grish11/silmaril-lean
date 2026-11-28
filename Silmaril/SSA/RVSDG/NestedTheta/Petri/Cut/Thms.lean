module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Cut.Correctness
import Silmaril.SSA.RVSDG.NestedTheta.Thms

/-! An observation cut shares the same legal firings on the prefix and
permits execution of the actual continuation under the marked colours. -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri

open RVSDG.Petri (Tokens read)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args bank outs : Ports (PortType V S)}
variable {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))}
variable {front : Term Op args past frontSigs bank} {whole : Term Op args past wholeSigs outs}
variable {tail : Term Op args (extend past frontSigs) tailSigs outs}
variable (cut : Cut front whole tail) (m : Model.{u, v, w} Op)

theorem Cut.attach_pending :
    cut.attach m (pending m front) (pending m tail) = pending m whole :=
  Cut.Proofs.attach_pending cut m

theorem Cut.observe_attach (prefixMark : Marking m front) (tailMark : Marking m tail) :
    cut.observe m (cut.attach m prefixMark tailMark) = prefixMark :=
  Cut.Proofs.observe_attach cut m prefixMark tailMark

theorem Cut.prefix_reaches (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    {mark : Marking m front} (steps : ReflTransGen (Fire m front entry tokens) (pending m front) mark) :
    ReflTransGen (Fire m whole entry tokens) (pending m whole) (cut.attach m mark (pending m tail)) := by
  rw [← cut.attach_pending m]
  exact steps.lift (fun mark => cut.attach m mark (pending m tail))
    (fun _ _ step => Cut.Proofs.prefix_step cut m entry tokens step (pending m tail))

theorem Cut.tail_reaches (entry : Tuple m.Val args) (tokens : Tokens m.Val past) (mark : Marking m front)
    {a b : Marking m tail} (steps : ReflTransGen (Fire m tail entry (cut.tokens m tokens mark)) a b) :
    ReflTransGen (Fire m whole entry tokens) (cut.attach m mark a) (cut.attach m mark b) :=
  steps.lift (cut.attach m mark) (fun _ _ step => Cut.Proofs.tail_step cut m entry tokens mark step)

theorem Cut.read_after (entry : Tuple m.Val args) (tokens : Tokens m.Val past) (mark : Marking m front)
    (result : Tuple m.Val bank) (done : finished m front entry tokens mark = some result) :
    read cut.wires entry (cut.tokens m tokens mark) = some result :=
  Cut.Proofs.read_after cut m entry tokens mark result done

theorem finishes_term_iff (term : Term Op args [] frontSigs bank)
    (entry : Tuple m.Val args) (output : Tuple m.Val bank) :
    Finishes m term.toGraph entry output ↔
      ∃ mark, ReflTransGen (Fire m term entry PUnit.unit) (pending m term) mark ∧
        finished m term entry PUnit.unit mark = some output := by
  let observes (spine : Term Op args [] frontSigs bank) :=
    ∃ mark, ReflTransGen (Fire m spine entry PUnit.unit) (pending m spine) mark ∧
      finished m spine entry PUnit.unit mark = some output
  change observes term.toGraph.toTerm ↔ observes term
  rw [Term.toTerm_toGraph]

theorem Cut.reads_of_finishes {front : Term Op args [] frontSigs bank} {whole : Term Op args [] wholeSigs outs}
    {tail : Term Op args (extend [] frontSigs) tailSigs outs} (cut : Cut front whole tail)
    (entry : Tuple m.Val args) (output : Tuple m.Val bank)
    (finishedPrefix : Finishes m front.toGraph entry output) : cut.Reads m entry output := by
  obtain ⟨mark, steps, read⟩ := (finishes_term_iff m front entry output).mp finishedPrefix
  exact ⟨cut.attach m mark (pending m tail), cut.prefix_reaches m entry PUnit.unit steps,
    by rw [cut.observe_attach]; exact read⟩

end Silmaril.SSA.RVSDG.NestedTheta.Petri
