module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Recursive.Statement

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Recursive.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open Structured.Proofs
open Token.Proofs
open Simple.Proofs (get_map)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params vars outs before all : List (Ty Data)}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params}
variable {read : Reads (model m) all} {active : List (Fin all.length)}

theorem branchFacts (guard : Expr P vars .bool) (sYes sNo : Stmt P true vars outs)
    (ctx : Tuple (Port before) (.bool :: vars))
    (yes : Build (Opcode P) params ((expr guard).lower (params := params) (tail ctx)).nodes (.bool :: outs))
    (no : Build (Opcode P) params yes.nodes (.bool :: outs))
    (v : View (model m) env read active
      (joinBranch ((expr guard).lower (tail ctx)) yes no).code)
    (fy : StatementFacts sYes (((expr guard).lower (tail ctx)).code.liftRefs ctx) yes v.right.left)
    (fn : StatementFacts sNo (yes.code.liftRefs (((expr guard).lower (tail ctx)).code.liftRefs ctx))
      no v.right.right.left) :
    StatementFacts (.branch guard sYes sNo) ctx (joinBranch ((expr guard).lower (tail ctx)) yes no) v := by
  let test := (expr guard).lower (params := params) (tail ctx)
  let shared := test.code.liftRefs ctx
  let skipped := yes.code.liftRefs shared
  let flag := no.code.lift (yes.code.lift (test.refs.get .head))
  let joined := phiNodes (P := Opcode P) (params := params) flag (no.code.liftRefs yes.refs) no.refs
  let tv := v.left
  let yv := v.right.left
  let nv := v.right.right.left
  let jv := v.right.right.right
  let whole := joinBranch test yes no
  have yesEntry {ty} (slot : Port (.bool :: vars) ty) :
      yv.embed (yes.code.lift (shared.get slot)) = v.embed (whole.code.lift (ctx.get slot)) := by
    simp only [shared, Simple.Code.liftRefs, get_map]
    rfl
  have noEntry {ty} (slot : Port (.bool :: vars) ty) :
      nv.embed (no.code.lift (skipped.get slot)) = v.embed (whole.code.lift (ctx.get slot)) := by
    simp only [skipped, shared, Code.liftRefs, Simple.Code.liftRefs, get_map]
    rfl
  have enterYes {i : Index all.length} {store : Tuple m.Value vars}
      (entry : RealizesOn read (fun r => v.embed (whole.code.lift r)) ctx (pack m store) active i) :
      RealizesOn read (fun r => yv.embed (yes.code.lift r)) shared (pack m store) active i :=
    fun j agree ty slot =>
      (congrArg (fun r : Port all ty => read r j) (yesEntry slot)).trans (entry j agree ty slot)
  have enterNo {i : Index all.length} {store : Tuple m.Value vars}
      (entry : RealizesOn read (fun r => v.embed (whole.code.lift r)) ctx (pack m store) active i) :
      RealizesOn read (fun r => nv.embed (no.code.lift r)) skipped (pack m store) active i :=
    fun j agree ty slot =>
      (congrArg (fun r : Port all ty => read r j) (noEntry slot)).trans (entry j agree ty slot)
  have atJoin (j) {ty} (slot : Port (.bool :: outs) ty) :
      read (v.embed (joined.refs.get slot)) j =
        (read (v.embed (joined.code.lift flag)) j).elim none (fun b =>
          if b.down then read (yv.embed (yes.refs.get slot)) j else read (nv.embed (no.refs.get slot)) j) := by
    have h := phiViewRead flag (no.code.liftRefs yes.refs) no.refs jv j slot
    change read (v.embed (joined.refs.get slot)) j =
      (read (v.embed (joined.code.lift flag)) j).elim none (fun b =>
        if b.down then read (v.embed (joined.code.lift ((no.code.liftRefs yes.refs).get slot))) j
        else read (v.embed (joined.code.lift (no.refs.get slot))) j) at h
    have lifted : (no.code.liftRefs yes.refs).get slot = no.code.lift (yes.refs.get slot) := by
      simp only [Code.liftRefs, get_map]
    rw [lifted] at h
    exact h
  have decision {i : Index all.length} {store : Tuple m.Value vars}
      (entry : RealizesOn read (fun r => v.embed (whole.code.lift r)) ctx (pack m store) active i)
      (j) (agree : Agrees active i j) :
      read (v.embed (joined.code.lift flag)) j = guard.eval m store := by
    have data : RealizesAt read (fun r => tv.embed (test.code.lift r)) (tail ctx) store j := by
      intro ty slot
      cases ctx with
      | cons _ _ => exact entry j agree ty (.tail slot)
    exact (tv.straightRead j (test.refs.get .head)).trans
      (exprExact m env guard (tail ctx) (tv.seed j) store (tv.seedRealizes data))
  have takeYes {i : Index all.length} {store : Tuple m.Value vars} {next}
      (entry : RealizesOn read (fun r => v.embed (whole.code.lift r)) ctx (pack m store) active i)
      (pick : guard.eval m store = some ⟨true⟩)
      (data : RealizesOn read yv.embed yes.refs (pack m next) active i) :
      RealizesOn read v.embed joined.refs (pack m next) active i := by
    intro j agree ty slot
    change read (v.embed (joined.refs.get slot)) j = some ((pack m next).get slot)
    rw [atJoin j slot, decision entry j agree, pick]
    exact data j agree ty slot
  have takeNo {i : Index all.length} {store : Tuple m.Value vars} {next}
      (entry : RealizesOn read (fun r => v.embed (whole.code.lift r)) ctx (pack m store) active i)
      (pick : guard.eval m store = some ⟨false⟩)
      (data : RealizesOn read nv.embed no.refs (pack m next) active i) :
      RealizesOn read v.embed joined.refs (pack m next) active i := by
    intro j agree ty slot
    change read (v.embed (joined.refs.get slot)) j = some ((pack m next).get slot)
    rw [atJoin j slot, decision entry j agree, pick]
    exact data j agree ty slot
  constructor
  · intro i missing
    have yesBottom : BottomOn read active i (yv.embed (yes.code.lift (shared.get .head))) := by
      rw [yesEntry]
      exact missing
    have noBottom : BottomOn read active i (nv.embed (no.code.lift (skipped.get .head))) := by
      rw [noEntry]
      exact missing
    have afterYes := fy.bottom yesBottom
    have afterNo := fn.bottom noBottom
    intro j agree
    change read (v.embed (joined.refs.get .head)) j = none
    rw [atJoin j .head]
    cases read (v.embed (joined.code.lift flag)) j with
    | none => rfl
    | some b =>
      obtain ⟨b⟩ := b
      cases b with
      | false => exact afterNo j agree
      | true => exact afterYes j agree
  · intro i store final entry ran
    cases ran with
    | branchTrue pick step =>
      exact takeYes entry pick (fy.ofReturns (enterYes entry) step)
    | branchFalse pick step =>
      exact takeNo entry pick (fn.ofReturns (enterNo entry) step)
  · intro i store entry done
    change (read (v.embed (joined.refs.get .head)) i).isSome at done
    rw [atJoin i .head, decision entry i (agrees_self active i)] at done
    cases pick : guard.eval m store with
    | none =>
      rw [pick] at done
      cases done
    | some bit =>
      rw [pick] at done
      obtain ⟨bit⟩ := bit
      cases bit with
      | false =>
        obtain ⟨final, ran, data⟩ := fn.ofToken (enterNo entry) done
        exact ⟨final, .branchFalse pick ran, takeNo entry pick data⟩
      | true =>
        obtain ⟨final, ran, data⟩ := fy.ofToken (enterYes entry) done
        exact ⟨final, .branchTrue pick ran, takeYes entry pick data⟩

end Silmaril.SSA.PEG.Simple.Structured.Token.Recursive.Proofs
