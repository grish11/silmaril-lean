module

public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Defs
public import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule.Proofs

open RVSDG (Port Tuple)
open While.Siblings (push)

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results args outs : List (Ty Data)} {n l : Nat} {t : Ty Data}
variable {g : Graph P params results n l}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params} {values : g.Valuation m}

theorem embedIndex_key {k : Nat} {keys : Fin k → Fin l} (inj : Function.Injective keys)
    (base : Index l) (i : Index k) (key : Fin k) : embedIndex keys base i (keys key) = i key := by
  have h : ∃ k, keys k = keys key := ⟨key, rfl⟩
  rw [embedIndex, dite_eq_left h, inj (Classical.choose_spec h)]

theorem embedIndex_set {k : Nat} {keys : Fin k → Fin l} (inj : Function.Injective keys)
    (base : Index l) (i : Index k) (key : Fin k) (j : Nat) :
    (embedIndex keys base i).set (keys key) j = embedIndex keys base (i.set key j) := by
  funext atKey
  by_cases eq : atKey = keys key
  · subst atKey
    rw [embedIndex_key inj]
    simp [Index.set]
  · rw [Index.set, ite_eq_right eq]
    unfold embedIndex
    split
    · rename_i found
      have ne : Classical.choose found ≠ key := by
        intro same
        exact eq ((Classical.choose_spec found).symm.trans (congrArg keys same))
      simp [Index.set, ne]
    · rfl

theorem embedIndex_base {k : Nat} (keys : Fin k → Fin l) (base : Index l) :
    embedIndex keys base (fun k => base (keys k)) = base := by
  funext j
  unfold embedIndex
  split
  · rename_i found
    exact congrArg base (Classical.choose_spec found)
  · rfl

variable (s : Stage g args outs)

theorem read_pull (base : Index l) (r : Ref s.graph.sort t) (idx : Index s.loops) :
    Rules.readRef (s.pull m values base) r idx =
      Rules.readRef values (push s.addresses r) (embedIndex s.keys base idx) := by
  obtain ⟨row, typed⟩ := r
  cases typed
  rfl

theorem read_node (solves : g.Solves m env values) (r : Ref g.sort t) (idx : Index l) :
    let row := nodeAt g r
    Rules.readRef values r idx = row.label.interpret m env idx
      (fun slot j _ => Rules.readRef values (row.arg slot) j) := by
  obtain ⟨row, typed⟩ := r
  cases typed
  exact solves (row, idx)

private theorem interpret_internal (inj : Function.Injective s.keys)
    (base : Index l) (i : Index s.loops) (input : Tuple m.Value args)
    (src : Node P args (Fin s.loops) s.graph.sort t) (dst : Node P params (Fin l) g.sort t)
    (mapped : expected s.keys s.addresses src = .inr dst) :
    dst.label.interpret m env (embedIndex s.keys base i)
        (fun slot j _ => Rules.readRef values (dst.arg slot) j) =
      src.label.interpret m input i
        (fun slot j _ => Rules.readRef (s.pull m values base) (src.arg slot) j) := by
  obtain ⟨arity, label, refs⟩ := src
  cases label with
  | param _ => cases mapped
  | op _ | phi =>
    cases Sum.inr.inj mapped
    simp only [Label.interpret, Node.ofLabel, Node.arg, Simple.get_map, read_pull]
  | theta key =>
    cases Sum.inr.inj mapped
    simp only [Label.interpret, Node.ofLabel, Node.arg, Simple.get_map, read_pull, embedIndex_set inj]
    have same := embedIndex_key inj base i key
    split <;> split <;> simp_all
  | pass _ | eval _ =>
    cases Sum.inr.inj mapped
    simp only [Label.interpret, Node.ofLabel, Node.arg, Simple.get_map, read_pull, embedIndex_set inj]

private theorem interpret_param (base : Index l) (i : Index s.loops) (input : Tuple m.Value args)
    (src : Node P args (Fin s.loops) s.graph.sort t)
    (p : Port args t) (mapped : expected s.keys s.addresses src = .inl p) :
    src.label.interpret m input i
        (fun slot j _ => Rules.readRef (s.pull m values base) (src.arg slot) j) = some (input.get p) := by
  obtain ⟨arity, label, refs⟩ := src
  cases label <;> cases mapped
  rfl

theorem pull_solves {bindings : Tuple (Ref g.sort) args} {input : Tuple m.Value args}
    (valid : s.Valid bindings) (solves : g.Solves m env values)
    (supplied : Realizes m values bindings input) (base : Index l) :
    s.graph.Solves m input (s.pull m values base) := by
  rintro ⟨row, i⟩
  let src := s.graph.node row
  let original := embedIndex s.keys base i
  change Rules.readRef values (s.addresses row) original =
    src.label.interpret m input i
      (fun slot j _ => Rules.readRef (s.pull m values base) (src.arg slot) j)
  have matchRow := valid.rows row
  cases tag : expected s.keys s.addresses src with
  | inl p =>
    have edge : s.addresses row = bindings.get p := by simpa only [Stage.Matches, src, tag] using matchRow
    rw [edge, supplied]
    exact (interpret_param s (values := values) base i input src p tag).symm
  | inr dst =>
    have rowEq : nodeAt g (s.addresses row) = dst := by simpa only [Stage.Matches, src, tag] using matchRow
    have equation := read_node solves (s.addresses row) original
    change Rules.readRef values (s.addresses row) original =
      (nodeAt g (s.addresses row)).label.interpret m env original
        (fun slot j _ => Rules.readRef values ((nodeAt g (s.addresses row)).arg slot) j) at equation
    rw [rowEq] at equation
    exact equation.trans (interpret_internal s valid.injective base i input src dst tag)

end Silmaril.SSA.PEG.Simple.Revert.Schedule.Proofs
