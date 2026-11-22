module

public import Silmaril.ProofFormats.DaslSyntax.Defs
public import Silmaril.Semantics.Naming.Lift.Thms

public section

namespace Silmaril.Proofs.ProofFormats.DaslSyntax

open Silmaril.ProofFormats.DaslSyntax
open Silmaril.Formats.Dasl
open Silmaril.Logic.Smt (SE)

private theorem read_list (items : List Value) :
    read (Encode.list.encode items) = (items.mapM read).map SE.list := by
  change (List.ofFn (fun index => read (items.get index)) |>.mapM id).map SE.list = _
  change (List.ofFn (read ∘ items.get) |>.mapM id).map SE.list = _
  rw [← List.map_ofFn, List.ofFn_get, List.mapM_map]
  rfl

private theorem read_edge (policy : Placement) (path : Path) (skip index : Nat) (child : Value) :
    read (edge policy path skip index child) = read child := by
  unfold edge
  split <;> rfl

mutual
theorem read_render_at (slots : InlinePrefix) (policy : Placement) (path : Path) (form : SE) :
    read (renderAt slots policy path form) = some form := by
  cases form with
  | atom => rfl
  | list items =>
    rw [renderAt, read_list, read_render_items slots policy path (slots path (headAtom items)) 0 items]
    rfl
termination_by structural form

theorem read_render_items (slots : InlinePrefix) (policy : Placement) (path : Path) (skip index : Nat)
    (items : List SE) : (renderItems slots policy path skip index items).mapM read = some items := by
  cases items with
  | nil => rfl
  | cons item rest =>
    simp only [renderItems, List.mapM_cons, read_edge,
      read_render_at slots policy (index :: path) item, read_render_items slots policy path skip (index + 1) rest]
    rfl
termination_by structural items
end

theorem mem_names_language {Item Name : Type} {grammar : Syntax Item} {store : Store Name}
    {predicate : Item → Prop} {root : Name} : root ∈ grammar.namesWhere store predicate ↔
      ∃ value, ValueNames store root value ∧ value ∈ grammar.language predicate := by
  refine (Semantics.Naming.Lift.mem_where_iff (coord := grammar.named store)
    (input := root) (predicate := predicate)).trans ?_
  exact ⟨fun ⟨item, ⟨value, named, decodes⟩, holds⟩ => ⟨value, named, item, decodes, holds⟩,
    fun ⟨value, named, item, decodes, holds⟩ => ⟨item, ⟨value, named, decodes⟩, holds⟩⟩

end Silmaril.Proofs.ProofFormats.DaslSyntax
