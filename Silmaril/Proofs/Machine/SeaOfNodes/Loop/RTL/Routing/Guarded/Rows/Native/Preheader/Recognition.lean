module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Defs
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Proofs

private theorem decodeInitializer_sound {arity : Nat}
    {flow : Silmaril.SSA.SeaOfNodes.Diamond.Dataflow
      Silmaril.Machine.SeaOfNodes.Diamond.RTL.WordOp (wordPorts arity) [] EntrySigs}
    {init : Initializer arity} (h : decodeInitializer flow = some init) : init.flow = flow := by
  cases flow with
  | cons op operands rest =>
    cases rest
    cases op <;> cases h <;> rfl

theorem withEntry_bodyGraph {arity : Nat}
    {entrySigs sigs : List (List Silmaril.Machine.SeaOfNodes.Diamond.RTL.PortTy)}
    (g : SourceWithEntry arity entrySigs sigs) (column : ArgumentColumn arity arity) :
    withEntry (bodyGraph g column) g.preheader (g.phiInputs .entry) = g := by
  have columns :
      (withEntry (bodyGraph g column) g.preheader (g.phiInputs .entry)).phiInputs = g.phiInputs := by
    funext edge
    cases edge <;> rfl
  cases g with
  | mk pre header _ predicate result =>
    exact congrArg
      (fun edges => Silmaril.SSA.SeaOfNodes.Loop.Graph.mk pre header edges predicate result) columns

theorem recognize_sound {arity : Nat} {sigs : List (List Silmaril.Machine.SeaOfNodes.Diamond.RTL.PortTy)}
    {g : Source arity sigs} {p : Plan arity} (accepted : recognize g = some p) :
    ∃ eq : p.row.sigs = sigs, eq ▸ p.graph = g := by
  unfold recognize at accepted
  cases decoded : decodeInitializer g.preheader with
  | none => simp [decoded] at accepted
  | some init =>
    simp only [decoded, Option.bind_some] at accepted
    split at accepted
    · cases entry : placeholderEntry init (g.phiInputs .entry) with
      | none => simp [entry] at accepted
      | some col =>
        cases body : Native.recognize (bodyGraph g col) with
        | none => simp [entry, body] at accepted
        | some spec =>
          obtain ⟨row, check, eq, reconstructed⟩ := Native.recognize_sound body
          simp only [entry, body, check, Option.bind_some, Option.map_some] at accepted
          cases Option.some.inj accepted
          refine ⟨eq, ?_⟩
          cases eq
          change withEntry row.graph init.flow (g.phiInputs .entry) = g
          have same : row.graph = bodyGraph g col := reconstructed
          calc
            _ = withEntry (bodyGraph g col) init.flow (g.phiInputs .entry) :=
              congrArg (fun graph => withEntry graph init.flow (g.phiInputs .entry)) same
            _ = withEntry (bodyGraph g col) g.preheader (g.phiInputs .entry) :=
              congrArg (fun flow => withEntry (bodyGraph g col) flow (g.phiInputs .entry))
                (decodeInitializer_sound decoded)
            _ = g := withEntry_bodyGraph g col
    · cases accepted

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Proofs
