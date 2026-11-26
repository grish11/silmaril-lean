module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Isomorphism.Defs
public import Silmaril.SSA.RVSDG.Isomorphism.Thms
import Mathlib.Data.Fin.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Preorder.Finite

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Isomorphism.Proofs

open OrderedRuntime.Structured (Ty Data Threaded runtime withRuntime nextRuntime newestIndex)

universe u v
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {args outs head : Ports (PortType V S)} {past sigs sigs' : List (Ports (PortType V S))}

private theorem chains_prepend (node : Node Op args past head) (children : Children (Graph Op) node)
    (rest : Graph Op args (past ++ [head]) sigs outs)
    (first : 0 < past.length → ∃ p, Address.output (past.length - 1) p ∈ node.inputs.addresses)
    (child : ∀ j, (children j).ScopeChains) (tail : rest.ScopeChains) :
    (rest.prepend node children).ScopeChains := by
  cases rest with
  | region nodes regions results =>
    obtain ⟨ordered, scopes⟩ := tail
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases first (fun j => ?_) i
      have rank : past.length + j.succ.val = (past ++ [head]).length + j.val := by
        simp only [Fin.val_succ, List.length_append, List.length_cons, List.length_nil]
        omega
      change (0 < past.length + j.succ.val → ∃ p,
        Address.output (past.length + j.succ.val - 1) p ∈ (nodes j).inputs.addresses)
      rw [rank]
      exact ordered j
    · intro i
      exact Fin.cases child (fun j => scopes j) i

section Checked

variable {P E : Dialect.{u,v} V PUnit.{u + 1}}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

private theorem runtime_mem (live : Origin args past runtime) (wires : Wires args past outs) :
    live.address ∈ Wires.addresses (withRuntime live wires) := by
  induction wires with
  | nil => simp [withRuntime, Wires.addresses]
  | cons origin rest ih => exact List.mem_cons_of_mem _ ih

private theorem newest_val (past : List (Ports (Ty V))) (out : Ports (Ty V)) :
    (newestIndex out past).val = past.length := by
  induction past with
  | nil => rfl
  | cons hd tl ih => simp [newestIndex, ih]

private theorem successor_address (past : List (Ports (Ty V))) (out : Ports (Ty V)) :
    ∃ p, (nextRuntime (args := args) past out).address =
      .output ((past ++ [Threaded out]).length - 1) p := by
  simp [nextRuntime, Origin.address, newest_val]

private theorem predecessor_mem {addrs : List Address} {live : Origin args past runtime}
    (member : live.address ∈ addrs)
    (aligned : 0 < past.length → ∃ p, live.address = .output (past.length - 1) p) :
    0 < past.length → ∃ p, Address.output (past.length - 1) p ∈ addrs := by
  intro nonempty
  obtain ⟨p, address⟩ := aligned nonempty
  exact ⟨p, address ▸ member⟩

private theorem chains {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : Term (OrderedRuntime.Structured.Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked P E a b live t) :
    (0 < past.length → ∃ p, live.address = .output (past.length - 1) p) → t.toGraph.ScopeChains := by
  induction checked with
  | ret => intro _; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | primitive live i o op wires rest ih =>
    intro aligned
    exact chains_prepend _ _ _ (predecessor_mem (runtime_mem live wires) aligned)
      (fun j => j.elim0) (ih (fun _ => successor_address _ _))
  | gamma extra choice live i o wires _ arms rest ihArms ihRest =>
    intro aligned
    exact chains_prepend _ _ _
      (predecessor_mem (List.mem_cons_of_mem choice.address (runtime_mem live wires)) aligned)
      (fun j => ihArms j (by simp)) (ihRest (fun _ => successor_address _ _))
  | theta live i wires _ body rest ihBody ihRest =>
    intro aligned
    exact chains_prepend _ _ _ (predecessor_mem (runtime_mem live wires) aligned)
      (fun j => ihBody j (by simp)) (ihRest (fun _ => successor_address _ _))

theorem scopeChains {a : Data args} {b : Data outs}
    {t : Term (OrderedRuntime.Structured.Opcode P E) (Threaded args) [] sigs (Threaded outs)}
    (checked : EntryChecked (a := a) (b := b) t) : t.toGraph.ScopeChains :=
  chains checked (by simp)

end Checked

variable {left : Graph Op args [] sigs outs} {right : Graph Op args [] sigs' outs}

private theorem identity_of_adjacent {n : Nat} (f : Fin n → Fin n)
    (lt : ∀ {i j}, j.val = i.val + 1 → f i < f j) : f = id := by
  cases n with
  | zero => funext i; exact i.elim0
  | succ n =>
    exact (Fin.strictMono_iff_lt_succ.mpr (fun i => lt (i := i.castSucc) (j := i.succ) rfl)).eq_id

/-- Pull a predecessor edge back through the supplied bijection. Its producer
must precede its consumer even in the actual numbered graph. -/
private theorem preimage_before (ids : Fin sigs.length ≃ Fin sigs'.length)
    (inputs : ∀ i, (left.nodes i).inputs.addresses.map (Address.rename (renameVertex ids)) =
      (right.nodes (ids i)).inputs.addresses)
    {i j : Fin sigs'.length} {port : Nat}
    (edge : Address.output i.val port ∈ (right.nodes j).inputs.addresses) :
    (ids.symm i).val < (ids.symm j).val := by
  have mapped : Address.output i.val port ∈
      (left.nodes (ids.symm j)).inputs.addresses.map (Address.rename (renameVertex ids)) := by
    rwa [inputs, Equiv.apply_symm_apply]
  obtain ⟨address, before, mappedAddress⟩ := List.mem_map.mp mapped
  cases address with
  | arg p => cases mappedAddress
  | output vertex p =>
    have earlier : vertex < (ids.symm j).val := by
      simpa only [site_prefix_length, List.length_nil, Nat.zero_add] using
        (left.nodes (ids.symm j)).inputs.output_before before
    have valid : vertex < sigs.length := Nat.lt_trans earlier (ids.symm j).isLt
    have same : ids ⟨vertex,valid⟩ = i := Fin.ext (by
      simpa only [Address.rename, renameVertex, dite_eq_left valid] using
        (Address.output.inj mappedAddress).1)
    have preimage : ids.symm i = ⟨vertex,valid⟩ := (ids.symm_apply_eq).2 same.symm
    simpa only [preimage] using earlier

theorem numbering_fixed (ids : Fin sigs.length ≃ Fin sigs'.length)
    (inputs : ∀ i, (left.nodes i).inputs.addresses.map (Address.rename (renameVertex ids)) =
      (right.nodes (ids i)).inputs.addresses)
    (chain : right.PredecessorChain) (i : Fin sigs.length) : (ids i).val = i.val := by
  have count : sigs.length = sigs'.length := Fin.equiv_iff_eq.mp ⟨ids⟩
  let f : Fin sigs'.length → Fin sigs'.length := fun j => Fin.cast count (ids.symm j)
  have fixed : f = id := identity_of_adjacent f (fun {i j} adjacent => by
    obtain ⟨port, edge⟩ := chain j (by simp [adjacent])
    have previous : j.val - 1 = i.val := by omega
    have edge' : Address.output i.val port ∈ (right.nodes j).inputs.addresses := by
      simpa only [List.length_nil, Nat.zero_add, previous] using edge
    exact preimage_before ids inputs edge')
  have atImage := congrArg Fin.val (congrFun fixed (ids i))
  simpa only [f, Fin.val_cast, Equiv.symm_apply_apply, id_eq] using atImage.symm

theorem addresses_at (iso : Graph.Isomorphic Op left right) (chain : right.PredecessorChain)
    (i : Fin sigs.length) (j : Fin sigs'.length) (rank : i.val = j.val) :
    (left.nodes i).inputs.addresses = (right.nodes j).inputs.addresses := by
  cases iso with
  | intro entry exit ids labels inputs results children =>
    have eq : ids i = j := Fin.ext ((numbering_fixed ids inputs chain i).trans rank)
    have noRename : Address.rename (renameVertex ids) = id := by
      funext address
      cases address with
      | arg port => rfl
      | output vertex port =>
        change Address.output (renameVertex ids vertex) port = Address.output vertex port
        unfold renameVertex
        split
        · rename_i valid
          rw [numbering_fixed ids inputs chain ⟨vertex,valid⟩]
        · rfl
    have atImage : (left.nodes i).inputs.addresses = (right.nodes (ids i)).inputs.addresses := by
      simpa only [noRename, List.map_id] using inputs i
    exact atImage.trans (congrArg (fun k => (right.nodes k).inputs.addresses) eq)

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Isomorphism.Proofs
