module

public import Silmaril.SSA.PEG.Simple.Revert.While.Siblings.Defs
public import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Siblings.Proofs

open RVSDG (Port Tuple)

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params args results ts ins : List (Ty Data)} {n n₁ : Nat} {t : Ty Data}
variable {g : Graph P params results n 2} {stage : Graph P args ts n₁ 1}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params}
variable {input : Tuple m.Value args} {values : g.Valuation m}

def atStage (base : Index 2) (key : Fin 2) (i : Index 1) : Index 2 :=
  base.set key (i 0)

def pull (addresses : Addresses stage.sort g.sort) (values : g.Valuation m)
    (base : Index 2) (key : Fin 2) : stage.Valuation m :=
  fun q => Rules.readRef values (addresses q.1) (atStage base key q.2)

@[simp] theorem read_pull (addresses : Addresses stage.sort g.sort)
    (base : Index 2) (key : Fin 2) (ref : Ref stage.sort t) (i : Index 1) :
    Rules.readRef (pull addresses values base key) ref i =
      Rules.readRef values (push addresses ref) (atStage base key i) := by
  obtain ⟨row, typed⟩ := ref
  cases typed
  rfl

private theorem atStage_key (base : Index 2) (key : Fin 2) (i : Index 1) (localKey : Fin 1) :
    atStage base key i key = i localKey := by
  have eq : localKey = 0 := Subsingleton.elim _ _
  subst localKey
  simp [atStage, Index.set]

private theorem atStage_set (base : Index 2) (key : Fin 2) (i : Index 1) (localKey : Fin 1) (k : Nat) :
    (atStage base key i).set key k = atStage base key (i.set localKey k) := by
  have eq : localKey = 0 := Subsingleton.elim _ _
  subst localKey
  funext coordinate
  by_cases same : coordinate = key <;> simp [atStage, Index.set, same]

theorem atStage_current (base : Index 2) (key : Fin 2) :
    atStage base key (fun _ => base key) = base := by
  funext coordinate
  by_cases same : coordinate = key <;> simp [atStage, Index.set, same]

private theorem read_node (solves : g.Solves m env values) (r : Ref g.sort t) (idx : Index 2) :
    let row := nodeAt g r
    Rules.readRef values r idx = row.label.interpret m env idx
      (fun slot j _ => Rules.readRef values (row.arg slot) j) := by
  obtain ⟨row, typed⟩ := r
  cases typed
  exact solves (row, idx)

private theorem interpret_internal (addresses : Addresses stage.sort g.sort)
    (base : Index 2) (key : Fin 2) (i : Index 1)
    (src : Node P args (Fin 1) stage.sort t) (dst : Node P params (Fin 2) g.sort t)
    (mapped : expected key addresses src = some (.inr dst)) :
    dst.label.interpret m env (atStage base key i)
        (fun slot j _ => Rules.readRef values (dst.arg slot) j) =
      src.label.interpret m input i
        (fun slot j _ => Rules.readRef (pull addresses values base key) (src.arg slot) j) := by
  obtain ⟨arity, label, refs⟩ := src
  cases label with
  | param _ => cases mapped
  | phi => cases mapped
  | op _ =>
    cases Sum.inr.inj (Option.some.inj mapped)
    simp only [Label.interpret, Node.ofLabel, Node.arg, Simple.get_map, read_pull]
  | theta localKey =>
    cases Sum.inr.inj (Option.some.inj mapped)
    simp only [Label.interpret, Node.ofLabel, Node.arg, Simple.get_map, read_pull,
      atStage_set base key i localKey]
    have same := atStage_key base key i localKey
    split <;> split <;> simp_all
  | pass localKey =>
    cases Sum.inr.inj (Option.some.inj mapped)
    simp only [Label.interpret, Node.ofLabel, Node.arg, Simple.get_map, read_pull,
      atStage_set base key i localKey]
  | eval localKey =>
    cases Sum.inr.inj (Option.some.inj mapped)
    simp only [Label.interpret, Node.ofLabel, Node.arg, Simple.get_map, read_pull,
      atStage_set base key i localKey]

private theorem interpret_param (addresses : Addresses stage.sort g.sort)
    (base : Index 2) (key : Fin 2) (i : Index 1) (src : Node P args (Fin 1) stage.sort t)
    (p : Port args t) (mapped : expected (params := params) key addresses src = some (.inl p)) :
    src.label.interpret m input i
        (fun slot j _ => Rules.readRef (pull addresses values base key) (src.arg slot) j) =
      some (input.get p) := by
  obtain ⟨arity, label, refs⟩ := src
  cases label <;> cases mapped
  rfl

/-- A cut valuation satisfies the stage equations when each boundary
reference is defined with its assigned input at every original index. -/
theorem pull_solves (addresses : Addresses stage.sort g.sort) (bindings : Tuple (Ref g.sort) args)
    (base : Index 2) (key : Fin 2)
    (matched : ∀ i, Matches g stage key addresses bindings i)
    (solves : g.Solves m env values)
    (supplied : ∀ (i : Index 2) t (p : Port args t),
      Rules.readRef values (bindings.get p) i = some (input.get p)) :
    stage.Solves m input (pull addresses values base key) := by
  rintro ⟨row, i⟩
  let src := stage.node row
  let original := atStage base key i
  change Rules.readRef values (addresses row) original =
    src.label.interpret m input i
      (fun slot j _ => Rules.readRef (pull addresses values base key) (src.arg slot) j)
  have valid := matched row
  cases tag : expected (params := params) key addresses src with
  | none =>
    simp only [Matches, src, tag] at valid
  | some action =>
    cases action with
    | inl p =>
      have edge : addresses row = bindings.get p := by simpa only [Matches, src, tag] using valid
      rw [edge, supplied]
      exact (interpret_param (g := g) (values := values) addresses base key i src p tag).symm
    | inr dst =>
      have rowEq : nodeAt g (addresses row) = dst := by simpa only [Matches, src, tag] using valid
      have equation := read_node solves (addresses row) original
      change Rules.readRef values (addresses row) original =
        (nodeAt g (addresses row)).label.interpret m env original
          (fun slot j _ => Rules.readRef values ((nodeAt g (addresses row)).arg slot) j) at equation
      rw [rowEq] at equation
      exact equation.trans (interpret_internal addresses base key i src dst tag)

theorem denote_pull (addresses : Addresses stage.sort g.sort) (bindings : Tuple (Ref g.sort) args)
    (base : Index 2) (key : Fin 2)
    (matched : ∀ i, Matches g stage key addresses bindings i)
    (solves : g.Solves m env values)
    (supplied : ∀ (i : Index 2) t (p : Port args t),
      Rules.readRef values (bindings.get p) i = some (input.get p))
    (wf : WellFounded stage.Demand) :
    stage.denote m input wf = pull addresses values base key :=
  stage.solves_unique m input wf (stage.denote_solves m input wf)
    (pull_solves addresses bindings base key matched solves supplied)

private theorem observe_refs_pull (addresses : Addresses stage.sort g.sort) (base : Index 2)
    (key : Fin 2) (i : Index 1) {outs : List (Ty Data)} (roots : Tuple (Ref stage.sort) outs) :
    roots.map (fun _ r => Rules.readRef (pull addresses values base key) r i) =
      observeRefs m g values (atStage base key i) (roots.map fun _ => push addresses) := by
  induction roots with
  | nil => rfl
  | cons ref rest ih => exact congrArg₂ Tuple.cons (read_pull addresses base key ref i) ih

theorem observe_pull (addresses : Addresses stage.sort g.sort) (base : Index 2)
    (key : Fin 2) (i : Index 1) :
    stage.observe m (pull addresses values base key) i =
      observeRefs m g values (atStage base key i) (stage.roots.map fun _ => push addresses) :=
  observe_refs_pull addresses base key i stage.roots

end Silmaril.SSA.PEG.Simple.Revert.While.Siblings.Proofs
