module

public import Silmaril.Semantics.Brookes.TreeSC.Closed.Defs
public import Silmaril.Semantics.Brookes.Thms
public import Silmaril.Semantics.Brookes.TreeSC.Thms
import Silmaril.Proofs.Semantics.Brookes.TreeSC.Closed.Code
import Silmaril.Proofs.Semantics.Brookes.TreeSC.Closed.Trees
import Silmaril.Proofs.Semantics.Brookes.TreeSC.Closed.Completion

public section

namespace Silmaril.Semantics.Brookes.TreeSC

open TrackA.Concurrency
open TrackA.Interaction

variable {R : Type} [DecidableEq R]
variable {B : Signature} {A C X I : Type*}

/-- The tree and SC replay have the same saturated words and results. -/
theorem treeBehavior_eq_machine (code : Code R) :
    treeBehavior WeakITree.unfold code.toTree = machineBehavior code :=
  Proofs.Semantics.Brookes.TreeSC.Closed.treeBehavior_eq_machine code

theorem machineBehavior_eq_denote (code : Code R) : machineBehavior code = code.denote :=
  Proofs.Semantics.Brookes.TreeSC.Closed.machineBehavior_eq_denote code

/-- The closed comparison implements the recursive return, read and write equations. -/
theorem treeBehavior_code (code : Code R) :
    treeBehavior WeakITree.unfold code.toTree = code.denote :=
  (treeBehavior_eq_machine code).trans (machineBehavior_eq_denote code)

/-- Substitution at done agrees with open Brookes sequencing on full words. -/
theorem denote_seq (first second : Code R) :
    (first.seq second).denote = Command.seq first.denote second.denote :=
  Proofs.Semantics.Brookes.TreeSC.Closed.denote_seq first second

theorem treeBehavior_seq (first second : Code R) :
    treeBehavior WeakITree.unfold (first.seq second).toTree =
      Command.seq (treeBehavior WeakITree.unfold first.toTree)
        (treeBehavior WeakITree.unfold second.toTree) := by
  simp only [treeBehavior_code, denote_seq]

/-- A forest's saturated language is the union of the languages at its roots. -/
theorem forestBehavior_eq_union (forest : Forest (signature R) B A I) :
    forestBehavior forest = behaviorUnion (fun i => treeBehavior forest.unfold (forest.root i)) :=
  Proofs.Semantics.Brookes.TreeSC.Closed.forestBehavior_eq_union forest

theorem codeForestBehavior_eq_union (code : I → Code R) :
    forestBehavior (Code.forest code) = behaviorUnion (fun i => (code i).denote) := by
  rw [forestBehavior_eq_union]
  exact congrArg behaviorUnion (funext (fun i => treeBehavior_code (code i)))

/-- Both weak choice kinds hide selection of a single complete alternative. -/
theorem choiceBehavior_eq_union {n : Nat} (kind : ChoiceKind) (code : Fin n → Code R) :
    forestBehavior (choose kind code) = behaviorUnion (fun i => (code i).denote) := by
  rw [Proofs.Semantics.Brookes.TreeSC.Closed.choiceBehavior_eq_union]
  simp only [machineBehavior_eq_denote]

/-- The same union law applies at any branch of an existing coalgebra. -/
theorem treeBehavior_branch {tree : Coalgebra (signature R) B A X} {root : X}
    {kind : ChoiceKind} {shape : B.Request} {next : B.Response shape → X}
    (layer : tree root = .branch kind shape next) :
    treeBehavior tree root = behaviorUnion (fun i => treeBehavior tree (next i)) :=
  Proofs.Semantics.Brookes.TreeSC.Closed.treeBehavior_branch layer

/-- Track A observational refinement implies inclusion after Brookes closure. -/
theorem treeBehavior_refines {D : Signature} {Y : Type*}
    {tree : Coalgebra (signature R) B A X} {other : Coalgebra (signature R) D A Y}
    {root : X} {otherRoot : Y} (refines : Refines (tree.observes root) (other.observes otherRoot))
    {word : Brookes.Trace (Store R)} {result : A} (h : (treeBehavior tree root).accepts word result) :
    (treeBehavior other otherRoot).accepts word result :=
  Proofs.Semantics.Brookes.TreeSC.Closed.treeBehavior_refines refines h

/-- Mapping a terminal value commutes with interpretation for any coalgebra. -/
theorem treeBehavior_map (f : A → C) (tree : Coalgebra (signature R) B A X) (root : X) :
    treeBehavior (mapReturns f tree) root = mapBehavior f (treeBehavior tree root) :=
  Proofs.Semantics.Brookes.TreeSC.Closed.treeBehavior_map f tree root

/-- The singleton projection of the open behavior recovers contiguous
completed paths with the given initial store, final store and result. -/
theorem treeBehavior_completes_iff {tree : Coalgebra (signature R) B A X} {root : X}
    {s t : Store R} {result : A} :
    (treeBehavior tree root).completes s t result ↔
      ∃ frames, Returns tree Eq root s frames result t :=
  Proofs.Semantics.Brookes.TreeSC.Closed.treeBehavior_completes_iff

/-- Completion in the closed singleton SC scheduler, hiding its event word. -/
theorem denote_completes_iff_sc {code : Code R} {s t : Store R} :
    code.denote.completes s t () ↔
      ∃ events, sc.MTr (Config.single (code, Shared.initial s)) events
        (Config.single (.done, Shared.initial t)) := by
  rw [← treeBehavior_code, treeBehavior_completes_iff]
  constructor
  · rintro ⟨frames, h⟩
    exact ⟨frames.map (Frame.event ()), closed_returns_iff_sc.mpr ⟨frames, rfl, h⟩⟩
  · rintro ⟨_, run⟩
    obtain ⟨frames, _, h⟩ := closed_returns_iff_sc.mp run
    exact ⟨frames, h⟩

end Silmaril.Semantics.Brookes.TreeSC
