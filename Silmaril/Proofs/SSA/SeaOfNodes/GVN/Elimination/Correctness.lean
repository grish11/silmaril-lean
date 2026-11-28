module

public import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Silmaril.SSA.SeaOfNodes.GVN.Elimination
open Diamond (Dataflow Model Signature Ty Val ValueSort)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires extend)

universe u v w

private theorem read_splitOutput {T : Type u} {F : T → Type w} {head : List T} {t : T}
    (next : Tuple F head) :
    (scope : List (List T)) → (i : Fin (scope ++ [head]).length) →
    (p : Port (scope ++ [head])[i] t) → (locals : Locals F scope) →
    (match splitOutput head scope i p with
      | .inl ⟨j, q⟩ => (locals.get j).get q
      | .inr q => next.get q) = ((locals.snoc next).get i).get p
  | [], i => by
    have first : i = (0 : Fin 1) := @Subsingleton.elim (Fin 1) _ i 0
    subst i
    intro p locals
    rfl
  | first :: tail, i => by
    refine Fin.cases ?_ ?_ i
    · intro p locals
      rfl
    · intro j port locals
      have same := read_splitOutput next tail j port locals.2
      change _ = ((locals.2.snoc next).get j).get port
      simp only [splitOutput, Fin.cases_succ]
      cases split : splitOutput head tail j port with
      | inl earlier =>
        obtain ⟨k, q⟩ := earlier
        rw [split] at same
        exact same
      | inr q =>
        rw [split] at same
        exact same

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args targetArgs : List (Ty Data)} {past sigs target : List (List (Ty Data))}
variable {out : ValueSort Data}
variable (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args)

theorem read_splitOrigin {head : List (Ty Data)} {t : Ty Data}
    (wire : Origin args (past ++ [head]) t) (locals : Locals (Val m.value) past)
    (next : Tuple (Val m.value) head) :
    (match splitOrigin head wire with
      | .inl prior => Diamond.read m prior entry locals
      | .inr port => next.get port) = Diamond.read m wire entry (locals.snoc next) := by
  cases wire with
  | arg => rfl
  | output i port =>
    have same := read_splitOutput next past i port locals
    simp only [splitOrigin]
    cases split : splitOutput head past i port with
    | inl earlier =>
      obtain ⟨j, q⟩ := earlier
      rw [split] at same
      exact same
    | inr q =>
      rw [split] at same
      exact same

theorem wires_read {route : Routing args past target targetArgs}
    {entry' : Tuple (Val m.value) targetArgs}
    {old : Locals (Val m.value) past} {new : Locals (Val m.value) target}
    (agree : route.AgreesBetween m entry entry' old new) {ports : List (Ty Data)}
    (wires : Wires args past ports) :
    wires.read entry old = (route.wires wires).read entry' new := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    simp only [Routing.wires, Wires.read, Tuple.map] at ih ⊢
    congr 1
    exact agree _ wire

theorem push_agrees {route : Routing args past target targetArgs}
    {entry' : Tuple (Val m.value) targetArgs}
    {old : Locals (Val m.value) past} {new : Locals (Val m.value) target}
    (agree : route.AgreesBetween m entry entry' old new) {head : List (Ty Data)}
    (next : Tuple (Val m.value) head) :
    Routing.AgreesBetween (route.push head) m entry entry' (old.snoc next) (new.snoc next) := by
  intro t wire
  have splitRead := read_splitOrigin m entry wire old next
  cases split : splitOrigin head wire with
  | inl prior =>
    have same := agree _ prior
    simp only [split] at splitRead
    rw [← splitRead, same]
    simp only [Routing.push, split, read_weaken]
  | inr port =>
    simp only [split] at splitRead
    rw [← splitRead]
    simp only [Routing.push, split, read_newest]

theorem routeSuffix_agrees (flow : Dataflow Op args past sigs)
    (route : Routing args past target targetArgs) {entry' : Tuple (Val m.value) targetArgs}
    (old : Locals (Val m.value) past) (new : Locals (Val m.value) target)
    (agree : route.AgreesBetween m entry entry' old new) :
    let result := routeSuffix flow route
    Routing.AgreesBetween result.2 m entry entry' (flow.eval m entry old) (result.1.eval m entry' new) := by
  induction flow generalizing target with
  | nil => exact agree
  | @cons past sigs ins out op operands rest ih =>
    let next : Tuple (Val m.value) [.value out] := .cons (m.run op (operands.read entry old)) .nil
    have equalInputs := wires_read m entry agree operands
    have sameNext : Tuple.cons (F := Val m.value) (t := .value out) (m.run op ((route.wires operands).read entry' new)) .nil = next :=
      congrArg (fun values => Tuple.cons (F := Val m.value) (t := .value out) (m.run op values) .nil) equalInputs.symm
    dsimp only [routeSuffix, Dataflow.eval]
    erw [sameNext]
    exact ih (route.push [.value out]) (old.snoc next) (new.snoc next) (push_agrees m entry agree next)

private theorem input_read {ports : List (Ty Data)} {t : Ty Data}
    (inputs : Wires args past ports) (port : Port ports t) (locals : Locals (Val m.value) past) :
    (inputs.read entry locals).get port = Diamond.read m (inputs.get port) entry locals := by
  induction port with
  | head => cases inputs; rfl
  | tail port ih => cases inputs with | cons _ rest => exact ih rest

theorem plug_read {ports : List (Ty Data)} (flow : Dataflow Op targetArgs [] sigs)
    (outputs : Wires targetArgs (extend [] sigs) ports) (inputs : Wires args past targetArgs)
    (locals : Locals (Val m.value) past) :
    let bound := plug flow outputs inputs
    bound.2.read entry (bound.1.eval m entry locals) =
      outputs.read (inputs.read entry locals) (flow.eval m (inputs.read entry locals) PUnit.unit) := by
  let bank := inputs.read entry locals
  have agrees : Routing.AgreesBetween (Routing.ofWires inputs) m bank entry PUnit.unit locals := by
    intro t origin
    cases origin with
    | arg port => exact input_read m entry inputs port locals
    | output i _ => exact i.elim0
  exact (wires_read m bank (routeSuffix_agrees m bank flow _ PUnit.unit locals agrees) outputs).symm

theorem drop_agrees (replacement : Origin args past (.value out))
    (locals : Locals (Val m.value) past) (next : Tuple (Val m.value) [.value out])
    (same : next.get .head = Diamond.read m replacement entry locals) :
    Routing.Agrees (dropNewest replacement) m entry (locals.snoc next) locals := by
  intro t wire
  have splitRead := read_splitOrigin m entry wire locals next
  cases split : splitOrigin (T := Ty Data) [.value out] wire with
  | inl prior =>
    simp only [split] at splitRead
    simpa only [dropNewest, split] using splitRead.symm
  | inr port =>
    cases port with
    | head =>
      simp only [split] at splitRead
      simpa only [dropNewest, split] using splitRead.symm.trans same
    | tail empty => nomatch empty

theorem erase_agrees {flow : Dataflow Op args past sigs} (candidate : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out)) (locals : Locals (Val m.value) past)
    (equal : Diamond.read m candidate.origin entry (flow.eval m entry locals) =
      Diamond.read m (inFinal candidate replacement) entry (flow.eval m entry locals)) :
    let result := erase candidate replacement
    Routing.Agrees result.route m entry (flow.eval m entry locals) (result.flow.eval m entry locals) := by
  induction candidate with
  | @here past sigs ins out op inputs rest =>
    let next : Tuple (Val m.value) [.value out] := .cons (m.run op (inputs.read entry locals)) .nil
    let prior : Origin args past (.value out) := replacement
    have original := read_keepOrigin rest (newest (past := past) (.head : Port (Ty := Ty Data) [.value out] (.value out)))
      m entry (locals.snoc next)
    have replaced := read_keepOrigin rest (weaken [.value out] prior) m entry (locals.snoc next)
    have localRead : next.get .head = Diamond.read m prior entry locals :=
      (read_newest .head m entry locals next).symm.trans
        (original.symm.trans (equal.trans (replaced.trans (read_weaken prior m entry locals next))))
    exact routeSuffix_agrees m entry rest (dropNewest prior) (locals.snoc next) locals
      (drop_agrees m entry prior locals next localRead)
  | later _ ih => exact ih replacement _ equal

theorem erase_size {flow : Dataflow Op args past sigs} (candidate : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out)) :
    (erase candidate replacement).sigs'.length + 1 = sigs.length := by
  induction candidate with
  | here => rfl
  | later _ ih => exact congrArg Nat.succ (ih replacement)

private theorem origin_eq_of_address {t : Ty Data} (left right : Origin args past t)
    (same : left.address = right.address) : left = right := by
  let x : Wires args past [t] := .cons left .nil
  let y : Wires args past [t] := .cons right .nil
  have equalWires := Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective x y
    (congrArg (fun a => [a]) same)
  exact congrArg (fun xs : Wires args past [t] => xs.get .head) equalWires

variable {flow : Dataflow Op args past sigs}
variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

private theorem admitted (candidate representative : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out)) {result : Rewrite Op args past sigs}
    (accepted : eliminate? candidate representative replacement = some result) :
    checkRepresentative candidate representative = true ∧
      inFinal candidate replacement = representative.origin ∧ erase candidate replacement = result := by
  unfold eliminate? at accepted
  split at accepted
  · rename_i guard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    exact ⟨guard.1, origin_eq_of_address _ _ guard.2, Option.some.inj accepted⟩
  · cases accepted

theorem eliminate_sound (candidate representative : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out))
    (locals : Locals (Val m.value) past) {result : Rewrite Op args past sigs}
    (accepted : eliminate? candidate representative replacement = some result) :
    Routing.Agrees result.route m entry (flow.eval m entry locals) (result.flow.eval m entry locals) := by
  obtain ⟨keys, wire, rewrite⟩ := admitted candidate representative replacement accepted
  rw [← rewrite]
  apply erase_agrees
  rw [wire]
  exact checkRepresentative_sound candidate representative m entry locals keys

theorem eliminate_size (candidate representative : Producer flow out)
    (replacement : Origin args (operandScope candidate) (.value out)) {result : Rewrite Op args past sigs}
    (accepted : eliminate? candidate representative replacement = some result) :
    result.sigs'.length + 1 = sigs.length := by
  rw [← (admitted candidate representative replacement accepted).2.2]
  exact erase_size candidate replacement

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Elimination
