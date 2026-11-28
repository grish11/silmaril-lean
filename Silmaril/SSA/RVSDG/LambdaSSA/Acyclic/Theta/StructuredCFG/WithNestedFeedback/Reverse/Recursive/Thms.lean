module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Complete

/-! # Completeness of recursive mixed recovery and its denotational agreement -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive

open Sequential
open NestedTheta.ExplicitRuntime (Checked EntryChecked)
open NestedTheta.ExplicitRuntime.Splice (append)
open OrderedRuntime.Structured (Data Threaded runtime)
open TwoBlock.TwoExit (Pure)
open Sequential.Flat.Serial (observe returns)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ] [DecidableEq Φ]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {g : Flat.Serial.Graph Φ A X Z L E D sigs}

omit [DecidableEq τ] [DecidableEq Φ] in
/-- Relocating a checked suffix changes wire origins and leaves the
outer labels and recursively scanned child scopes intact. -/
theorem scan_append {args middle outs : Ports (OrderedRuntime.Structured.Ty τ)}
    {past ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))}
    {a : Data args} {b : Data middle} {c : Data outs}
    {live : Origin (Threaded args) past runtime}
    {p : NestedTheta.Term (Wires.Op Φ) (Threaded args) past ps (Threaded middle)}
    {q : NestedTheta.Term (Wires.Op Φ) (Threaded middle) [] qs (Threaded outs)}
    (first : Checked (Pure τ) (Wires.Effect Φ) a b live p)
    (next : EntryChecked (a := b) (b := c) q) :
    scan (append next first).1 = (do let xs ← scan p; let ys ← scan q; pure (xs ++ ys)) :=
  Proofs.scan_append first next

omit [DecidableEq τ] [DecidableEq Φ] in
theorem weight_append (p q : Layout τ Φ) : weight (p ++ q) = weight p + weight q :=
  Proofs.weight_append p q

omit [DecidableEq τ] [DecidableEq Φ] in
theorem scan_route_free (n : Normal Φ A X Z L E D sigs) {labels : Layout τ Φ}
    (scanned : scan n.toSyntax.code.1 = some labels) (h e m d : τ) :
    Entry.route h e m d ∉ labels :=
  Proofs.scan_route_free n scanned h e m d

omit [DecidableEq Φ] in
theorem scan_parse_generated (n : Normal Φ A X Z L E D sigs) (h : n.Supported) :
    ∃ labels, scan n.toSyntax.code.1 = some labels ∧
      parse (weight labels) A X Z labels = some (pack n) :=
  Proofs.scan_parse_generated n h

omit [DecidableEq Φ] in
theorem candidate_generated (n : Normal Φ A X Z L E D sigs) (h : n.Supported) :
    candidate n.toSyntax.graph = some n := Proofs.candidate_generated n h

theorem reject_wiring (n : Normal Φ A X Z L E D sigs) (parsed : candidate g = some n)
    (different : n.toSyntax.graph ≠ g) : recover g = none := by
  simp [recover, recognize, parsed, certify, different]

/-- For right-associated local bodies, the exact generated flat CFG is recovered. -/
theorem recover_generated (n : Normal Φ A X Z L E D sigs) (h : n.Supported) :
    recover n.toSyntax.graph = some ⟨n.toSyntax.source.region, .generated n.toSyntax⟩ :=
  Proofs.recover_generated n h

/-- Successful recovery characterizes literal numbered emissions of the
canonical grammar. Local instruction sequences may be reassociated. -/
theorem recover_isSome_iff (g : Flat.Serial.Graph Φ A X Z L E D sigs) :
    (recover g).isSome = true ↔ ∃ n : Normal Φ A X Z L E D sigs, n.toSyntax.graph = g :=
  Proofs.recover_isSome_iff g

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Agreement of the full partial observation of the graph and recovered region. -/
theorem recover_observe {w : Fibre g} (_accepted : recover g = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial) :=
  w.2.region_observe coherent env initial

/-- Every successful graph-only recovery agrees with the actual flat region
on the decoded exit, its payload and the exact final token. -/
theorem recover_returns_iff {w : Fibre g} (_accepted : recover g = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (exit : LabelDen [E,D]) (initial final : σ) :
    returns (ε := ε) g env.2 initial exit final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial = Part.some (exit, final) :=
  w.2.region_returns_iff coherent env exit initial final

theorem recover_undefined_iff {w : Fibre g} (_accepted : recover g = some w)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.2.typing env).run initial = Part.none :=
  w.2.region_undefined_iff coherent env initial

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive
