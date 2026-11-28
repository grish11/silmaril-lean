module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Defs
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Recognition

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs

open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy)

theorem recognize_sound {arity : Nat} {entrySigs sigs : List (List PortTy)}
    {g : SourceWithEntry arity entrySigs sigs} {p : Plan arity entrySigs}
    (accepted : recognize g = some p) : ∃ eq : p.row.sigs = sigs, eq ▸ p.graph = g := by
  unfold recognize at accepted
  dsimp only at accepted
  split at accepted
  · split at accepted
    · generalize hcol : checkColumn _ _ _ = col at accepted
      cases col with
      | none => cases accepted
      | some column =>
        simp only [Option.bind_some] at accepted
        cases body : Native.recognize (bodyGraph g column) with
        | none => simp [body] at accepted
        | some spec =>
          obtain ⟨row, check, eq, reconstructed⟩ := Native.recognize_sound body
          simp only [body, check, Option.bind_some, Option.map_some] at accepted
          cases Option.some.inj accepted
          refine ⟨eq, ?_⟩
          cases eq
          have same : row.graph = bodyGraph g column := reconstructed
          exact (congrArg (fun graph => withEntry graph g.preheader (g.phiInputs .entry)) same).trans
            (Preheader.Proofs.withEntry_bodyGraph g column)
    · cases accepted
  · cases accepted

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs
