module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.PacketCopy

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

variable {V F : Type} [DecidableEq V]

omit [DecidableEq V] in
private theorem term_relabel_comp {K L N : Type} (first : K → L) (second : L → N)
    (term : Term V K F) : (term.relabel first).relabel second = term.relabel (second ∘ first) := by
  induction term <;> simp_all [Term.relabel]

omit [DecidableEq V] in
private theorem body_relabel_comp {K L N : Type} (first : K → L) (second : L → N)
    (body : Body V K F) : (body.relabel first).relabel second = body.relabel (second ∘ first) := by
  induction body <;> simp_all [Body.relabel, term_relabel_comp]

omit [DecidableEq V] in
private theorem block_relabel_comp {K L N : Type} (first : K → L) (second : L → N)
    (block : Block V K F) : (block.relabel first).relabel second = block.relabel (second ∘ first) := by
  simp only [Block.relabel, body_relabel_comp]

/-- Transport a local rule when private block matches and target routes are preserved. -/
private theorem liftMatch {n a b N A B : Nat} {right : Graph V F a b} {linked : Graph V F A B}
    {route : Label n b → Label right.locals b} {source : Block V (Label n b) F}
    {image : Label right.locals b} (matched : BlockMatch right route source image)
    (sourceLabel : Label n b → Label N B) (targetLabel : Label right.locals b → Label linked.locals B)
    (linkedRoute : Label N B → Label linked.locals B)
    (commute : ∀ label, linkedRoute (sourceLabel label) = targetLabel (route label))
    (copied : ∀ i, ∃ j, targetLabel (.inl i) = .inl j ∧ (right.block i).relabel targetLabel = linked.block j) :
    BlockMatch linked linkedRoute (source.relabel sourceLabel) (targetLabel image) := by
  cases matched with
  | copy index address body =>
    obtain ⟨newIndex, newAddress, newBody⟩ := copied index
    refine .copy newIndex (congrArg targetLabel address |>.trans newAddress) ?_
    rw [← newBody, ← body, block_relabel_comp, block_relabel_comp]
    exact congrArg source.relabel (funext commute)
  | forward target body address =>
    refine .forward (sourceLabel target) ?_ ((congrArg targetLabel address).trans (commute target).symm)
    simp [Block.relabel, body, Body.relabel, Term.relabel]
  | forwardCopies target copies address =>
    exact .forwardCopies (sourceLabel target)
      (Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy.relabel copies sourceLabel)
      ((congrArg targetLabel address).trans (commute target).symm)

variable {a b c : Nat}
  {left left' : Graph V F a b} {right right' : Graph V F b c}

private def linkedRoute (first : Simulation left left') (second : Simulation right right') :
    Label (left.linkedCount right) c → Label (left'.linkedCount right') c :=
  Sum.elim (Simulation.linkedAddress first second) Sum.inr

private theorem leftRoute (first : Simulation left left') (second : Simulation right right')
    (label : Label left.locals b) :
    linkedRoute first second (left.leftLabel right label) = left'.leftLabel right' (first.route label) := by
  cases label with
  | inl index =>
    change Simulation.linkedAddress first second ((index.castAdd b).castAdd right.locals) =
      left'.leftLabel right' (first.address index)
    simp [Simulation.linkedAddress]
  | inr port =>
    change Simulation.linkedAddress first second ((port.natAdd left.locals).castAdd right.locals) =
      left'.leftLabel right' (.inr port)
    simp [Simulation.linkedAddress]

private theorem rightRoute (first : Simulation left left') (second : Simulation right right')
    (label : Label right.locals c) :
    linkedRoute first second (left.rightLabel right label) = left'.rightLabel right' (second.route label) := by
  cases label with
  | inl index =>
    change Simulation.linkedAddress first second (index.natAdd (left.locals + b)) =
      left'.rightLabel right' (second.address index)
    simp [Simulation.linkedAddress]
  | inr port => rfl

theorem link_entry [Inhabited V] (first : Simulation left left') (second : Simulation right right')
    (port : Fin a) :
    Sum.elim (first.linkedAddress second) Sum.inr ((left.link right).entry port) =
      (left'.link right').entry port :=
  (leftRoute first second (left.entry port)).trans (congrArg (left'.leftLabel right') (first.entry port))

theorem link_block [Inhabited V] (first : Simulation left left') (second : Simulation right right')
    (index : Fin (left.link right).locals) :
    BlockMatch (left'.link right') (Sum.elim (first.linkedAddress second) Sum.inr)
      ((left.link right).block index) (first.linkedAddress second index) := by
  refine Fin.addCases (fun addrLeft => ?_) (fun addr => ?_) index
  · refine Fin.addCases (fun i => ?_) (fun port => ?_) addrLeft
    · have matched := liftMatch (linked := left'.link right') (first.block i)
        (left.leftLabel right) (left'.leftLabel right')
        (linkedRoute first second) (leftRoute first second) (fun target =>
          ⟨(target.castAdd b).castAdd right'.locals, rfl, by simp [Graph.link, Graph.linkedBlock]⟩)
      simpa only [Graph.link, Graph.linkedBlock, Simulation.linkedAddress, linkedRoute, Fin.addCases_left] using matched
    · refine .copy ((port.natAdd left'.locals).castAdd right'.locals) ?_ ?_
      · simp [Simulation.linkedAddress, Graph.leftLabel]
        rfl
      · simp only [Graph.link, Graph.linkedBlock, Fin.addCases_left, Fin.addCases_right, Graph.handoff,
          Block.relabel, Body.relabel, Term.relabel]
        exact congrArg (fun label => (⟨default, .term (.br label (.var default))⟩ : Block V _ F))
          ((rightRoute first second (right.entry port)).trans (congrArg (left'.rightLabel right') (second.entry port)))
  · have matched := liftMatch (linked := left'.link right') (second.block addr)
      (left.rightLabel right) (left'.rightLabel right')
      (linkedRoute first second) (rightRoute first second) (fun target =>
        ⟨target.natAdd (left'.locals + b), rfl, by simp [Graph.link, Graph.linkedBlock]⟩)
    simpa only [Graph.link, Graph.linkedBlock, Simulation.linkedAddress, linkedRoute, Fin.addCases_right] using matched

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation
