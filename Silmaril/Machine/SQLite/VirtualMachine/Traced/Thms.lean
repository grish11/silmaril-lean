module

public import Silmaril.Machine.SQLite.VirtualMachine.Traced.Defs
import Silmaril.Proofs.Machine.SQLite.VirtualMachine.Traced

public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Traced

theorem runWithTrace_result (db : Database) (code : Program) (fuel : Nat) (start : State) :
    (runWithTrace db code fuel start).result = run db code fuel start :=
  Proofs.Machine.SQLite.VirtualMachine.Traced.runWithTrace_result db code fuel start

theorem wp_snapshots {snapshots : Set Database} {code : Program} {fuel : Nat} {start : State}
    {post : Report → Prop} :
    WP (behaviors snapshots code fuel start) post ↔
      snapshots.Nonempty ∧ ∀ db ∈ snapshots,
        (observe (run db code fuel start)).termination = .halted 0 ∧
          post (runWithTrace db code fuel start).report :=
  Proofs.Machine.SQLite.VirtualMachine.Traced.wp_snapshots

theorem wp_weakest {Input : Type} (runs : Input → Set Report) (pre : Input → Prop)
    (post : Report → Prop) :
    (∀ input, pre input → WP (runs input) post) ↔
      (∀ input, pre input → (runs input).Nonempty) ∧
        ∀ input, pre input → ∀ report ∈ runs input,
          report.observation.termination = .halted 0 ∧ post report :=
  Proofs.Machine.SQLite.VirtualMachine.Traced.wp_weakest runs pre post

theorem wp_of_refines {implementation specification : Set Report} {post : Report → Prop}
    (refines : Refines implementation specification) (enabled : implementation.Nonempty)
    (wp : WP specification post) : WP implementation post :=
  ⟨enabled, fun report h => wp.2 report (refines h)⟩

theorem equivalent_symm {left right : Set Report} (h : Equivalent left right) :
    Equivalent right left :=
  ⟨h.2 ▸ h.1, h.2.symm⟩

theorem equivalent_trans {left middle right : Set Report} (h : Equivalent left middle)
    (k : Equivalent middle right) : Equivalent left right :=
  ⟨h.1, h.2.trans k.2⟩

theorem equivalent_self_iff {runs : Set Report} : Equivalent runs runs ↔ Defined runs :=
  ⟨And.left, fun defined => ⟨defined, rfl⟩⟩

end Silmaril.Machine.SQLite.VirtualMachine.Traced
