module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Visibility
public import Silmaril.SSA.PEG.Figure19.Defs

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs.Figure19

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open PEG.Figure19 (Derives FitsForest Assumptions)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params all outs before mid after vars inside ins : List (Ty Data)} {t : Ty Data}

@[expose] def table (rows : Rows P params all all) (roots : Tuple (Port all) outs) :
    Graph P params outs all.length all.length where
  forest := ⟨fun i => (rows (portAt all i)).parent⟩
  sort := fun i => all[i]
  node i := let row := rows (portAt all i)
            .ofLabel row.label (row.refs.map fun _ r => numberPort r)
  roots := roots.map fun _ r => numberPort r

variable {rows : Rows P params all all} {roots : Tuple (Port all) outs}
variable {depth : Fin all.length → Nat} {level : Nat} {ctx : Assumptions all.length}

theorem table_node (r : Port all t) :
    PEG.Figure19.nodeAt (table rows roots) (numberPort r) =
      .ofLabel (rows r).label ((rows r).refs.map fun _ p => numberPort p) := by
  apply WhileProofs.portForall all (fun t (r : Port all t) => _) _ t r
  intro i
  have same : numberPort (portAt all i) = Ref.ofId (table rows roots).sort i := by
    have idEq := Simple.Proofs.number_portAt all i
    generalize numberPort (portAt all i) = ref at idEq ⊢
    cases ref with
    | mk id typed =>
      change id = i at idEq
      subst id
      rfl
  rw [same]
  rfl

abbrev Typed (g : Graph P params outs all.length all.length) (depth : Fin all.length → Nat)
    (level : Nat) (ctx : Assumptions all.length) (r : Port all t) :=
  Derives g depth .inward level ctx (numberPort r).id

variable {g : Graph P params outs all.length all.length}
variable {r : Ref g.sort t}

theorem paramAt {slot : Port params t}
    (row : PEG.Figure19.nodeAt g r = .ofLabel (.param slot) .nil) :
    Derives g depth .inward level ctx r.id := by
  cases r with
  | mk id sort => cases sort; exact .param row

theorem opAt {opcode : P ins t} {args : Tuple (Ref g.sort) ins}
    (row : PEG.Figure19.nodeAt g r = .ofLabel (.op opcode) args)
    (children : ∀ s : Fin ins.length,
      Derives g depth .inward level ctx (args.get (portAt ins s)).id) :
    Derives g depth .inward level ctx r.id := by
  cases r with
  | mk id sort => cases sort; exact .op row children

theorem phiAt {c : Ref g.sort .bool} {a b : Ref g.sort t}
    (row : PEG.Figure19.nodeAt g r = .ofLabel .phi (.cons c (.cons a (.cons b .nil))))
    (cond : Derives g depth .inward level ctx c.id)
    (yes : Derives g depth .inward level ctx a.id) (no : Derives g depth .inward level ctx b.id) :
    Derives g depth .inward level ctx r.id := by
  cases r with
  | mk id sort => cases sort; exact .phi row cond yes no

theorem thetaAt {key : Fin all.length} {a b : Ref g.sort t}
    (row : PEG.Figure19.nodeAt g r = .ofLabel (.theta key) (.cons a (.cons b .nil)))
    (succ : depth key = level + 1)
    (init : Derives g depth .inward level ctx a.id)
    (step : Derives g depth .inward (depth key) ((depth key, r.id) :: ctx) b.id) :
    Derives g depth .inward (depth key) ctx r.id := by
  cases r with
  | mk id sort => cases sort; exact .theta row succ init step

theorem assumeAt {key : Fin all.length} {a b : Ref g.sort t}
    (row : PEG.Figure19.nodeAt g r = .ofLabel (.theta key) (.cons a (.cons b .nil)))
    (h : (depth key, r.id) ∈ ctx) : Derives g depth .inward (depth key) ctx r.id := by
  cases r with
  | mk id sort => cases sort; exact .assume row h

theorem evalAt {key : Fin all.length} {a : Ref g.sort t} {c : Ref g.sort .count} {b : Ref g.sort .bool}
    (row : PEG.Figure19.nodeAt g r = .ofLabel (.eval key) (.cons a (.cons c .nil)))
    (pass : PEG.Figure19.nodeAt g c = .ofLabel (.pass key) (.cons b .nil))
    (succ : depth key = level + 1) (older : ∀ h ∈ ctx, h.1 < depth key)
    (val : Derives g depth .inward (depth key) ctx a.id)
    (test : Derives g depth .inward (depth key) ctx b.id) :
    Derives g depth .inward level ctx r.id := by
  cases r with
  | mk id sort => cases sort; exact .evalPass row pass succ older val test

/-- Interpret a fragment's typed ports in the final table. The view
retains the actual rows after embedding and the containing pass key. -/
structure View (rows : Rows P params all all) (parent : Option (Fin all.length))
    (code : Code P params before after) where
  holes : Rows P params before all
  embed : Embed after all
  eqs : ∀ t (r : Port after t), rows (embed r) = code.rows holes embed parent r

variable {parent : Option (Fin all.length)}

@[expose] def View.left {a : Code P params before mid} {b : Code P params mid after}
    (v : View rows parent (.seq a b)) : View rows parent a where
  holes := v.holes
  embed := fun r => v.embed (b.lift r)
  eqs := by
    intro t r
    have h := v.eqs t (b.lift r)
    change rows (v.embed (b.lift r)) =
      b.rows (a.rows v.holes (fun r => v.embed (b.lift r)) parent) v.embed parent (b.lift r) at h
    rw [rows_lift] at h
    exact h

@[expose] def View.right {a : Code P params before mid} {b : Code P params mid after}
    (v : View rows parent (.seq a b)) : View rows parent b :=
  ⟨a.rows v.holes (fun r => v.embed (b.lift r)) parent, v.embed, v.eqs⟩

variable {init : Tuple (Port before) vars} {body : Code P params (vars ++ before) inside}
variable {guard : Port inside .bool} {next : Tuple (Port inside) vars} {neg : P [.bool] .bool}

@[expose] def View.key (v : View rows parent (.loop init body guard next neg)) : Fin all.length :=
  (numberPort (v.embed (passRef vars))).id

@[expose] def View.inner (v : View rows parent (.loop init body guard next neg)) : View rows (some v.key) body where
  holes := loopHoles body init next v.holes v.embed
  embed := fun r => v.embed (insideRef vars r)
  eqs := by
    intro t r
    have h := v.eqs t (insideRef vars r)
    change _ = loopRows body guard neg parent v.embed
      (body.rows (loopHoles body init next v.holes v.embed) (fun r => v.embed (insideRef vars r))
        (some v.key)) (insideRef vars r) at h
    rw [loopRows_inside] at h
    exact h

theorem View.node {code : Code P params before after} (v : View rows parent code) (r : Port after t) :
    PEG.Figure19.nodeAt (table rows roots) (numberPort (v.embed r)) =
      let row := code.rows v.holes v.embed parent r
      .ofLabel row.label (row.refs.map fun _ p => numberPort p) := by
  rw [table_node, v.eqs]

theorem View.keyDepth (v : View rows parent (.loop init body guard next neg))
    (fits : FitsForest (table rows roots).forest depth) :
    depth v.key = (parent.map depth).getD 0 + 1 := by
  have row := v.eqs .count (passRef vars)
  change _ = loopRows body guard neg parent v.embed _ (passRef vars) at row
  rw [loopRows_pass] at row
  have eq := portLookup (fun r => (rows r).parent) (v.embed (passRef vars))
  have actual : (table rows roots).forest.parent v.key = parent :=
    eq.trans (congrArg Row.parent row)
  simpa only [actual] using fits v.key

/-- A straight fragment types each available output. The operand
availability proof follows the existing expression and φ builders. -/
theorem straight (code : Simple.Code P params before after)
    (holes : Rows P params before all) (embed : Embed after all)
    (eqs : ∀ t (r : Port after t), rows (embed r) = straightRows holes code embed r)
    (allow : PortsPred before) (ok : checks allow code)
    (entry : ∀ t (r : Port before t), allow r →
      Typed (table rows roots) depth level ctx (embed (code.lift r))) :
    ∀ t (r : Port after t), available allow code r →
      Typed (table rows roots) depth level ctx (embed r) := by
  induction code with
  | empty => exact entry
  | emit prior label args ih =>
    have old := ih (fun r => embed (.tail r)) (fun t r => eqs t (.tail r)) ok.1 entry
    intro t r hr
    cases r with
    | tail r => exact old _ r hr
    | head =>
      have emitted := table_node (rows := rows) (roots := roots) (embed .head)
      rw [eqs] at emitted
      change PEG.Figure19.nodeAt (table rows roots) (numberPort (embed .head)) =
        .ofLabel (label.map (fun op => op) Fin.elim0)
          ((args.map (fun _ r => embed (.tail r))).map fun _ p => numberPort p) at emitted
      cases label with
      | param slot =>
        cases args
        exact paramAt emitted
      | op opcode =>
        apply opAt emitted
        intro s
        rw [Simple.Proofs.get_map, Simple.Proofs.get_map]
        exact old _ _ (ok.2 _ _)
      | phi =>
        cases args with
        | cons flag tail =>
          cases tail with
          | cons yes tail =>
            cases tail with
            | cons no tail =>
              cases tail
              exact phiAt emitted (old _ flag (ok.2 _ .head))
                (old _ yes (ok.2 _ (.tail .head))) (old _ no (ok.2 _ (.tail (.tail .head))))
      | theta impossible | eval impossible | pass impossible => exact impossible.elim0

end Silmaril.SSA.PEG.Simple.Structured.Proofs.Figure19
