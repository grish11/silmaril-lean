module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Defs
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine
open RightSpine (Addends Prefix WordWire)
open Diamond (Ty Val ValueSort dataPorts)
open GVN (newest olderIndex olderPort read_newest read_weaken weaken)
open GVN.Elimination (Rewrite Routing)
open SubZero (model wordPort)
open Silmaril.SSA.RVSDG (Address Locals Port Tuple)

variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}
variable {ids : SourceIds} {known : Prefix args past} {lhs rhs : WordWire args past}
variable {entry : Tuple (Val model.value) args} {locals : Locals (Val model.value) past}

private theorem older_address {T : Type} {t : T} (head : List T) :
    (scope : List (List T)) → (i : Fin scope.length) → (p : Port scope[i] t) →
      Address.output (olderIndex head scope i).val (olderPort head scope i p).index =
        Address.output i.val p.index
  | [], i => i.elim0
  | first :: tail, i => Fin.cases
      (motive := fun j => (p : Port (first :: tail)[j] t) →
        Address.output (olderIndex head (first :: tail) j).val (olderPort head (first :: tail) j p).index =
          Address.output j.val p.index)
      (fun _ => rfl)
      (fun j p => congrArg (Address.rename Nat.succ) (older_address head tail j p)) i

theorem atWire_weaken (ids : SourceIds) (head : List (Ty Unit)) (wire : WordWire args past) :
    ids.atWire (weaken head wire) = ids.atWire wire := by
  cases wire with
  | arg => rfl
  | output i p => exact congrArg ids.lookup (older_address head past i p)

theorem match_exact {edit : AddRewrite.Splice args past} (accepted : matchAdd? ids known lhs rhs = some edit) :
    (known.literals lhs).isNone = true ∧ (known.literals rhs).isNone = true ∧
      lhs.address ≠ rhs.address ∧ (known.addends rhs).isNone = true ∧
      ∃ left, known.addends lhs = some left ∧ compare? ids known.literals left.right rhs = some true ∧
        edit = permute left rhs := by
  unfold matchAdd? at accepted
  split at accepted
  · rename_i guard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    obtain ⟨left, leftFound, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    split at accepted
    · rename_i order
      exact ⟨guard.1.1.1, guard.1.1.2, guard.1.2, guard.2, left, leftFound, order,
        (Option.some.inj accepted).symm⟩
    · cases accepted
  · cases accepted

private abbrev readWord (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past)
    (wire : WordWire args past) : BitVec 64 :=
  Diamond.read model wire entry locals

private theorem permute_eval (left : Addends args past) (right : WordWire args past) :
    (permute left right).eval entry locals =
      (readWord entry locals left.left + readWord entry locals right) + readWord entry locals left.right := by
  let value := readWord entry locals left.left + readWord entry locals right
  let fresh : Tuple (Val model.value) [wordPort] := .cons value .nil
  change readWord entry (locals.snoc fresh) (newest .head) +
    readWord entry (locals.snoc fresh) (weaken [wordPort] left.right) = _
  simp only [readWord, read_newest, read_weaken]
  rfl

private def sound (ids : SourceIds) (entry : Tuple (Val model.value) args) : AddRewrite.Sound (rules ids) entry where
  Agrees known locals := known.Agrees entry locals
  record op operands agree := Prefix.record_agrees agree op operands
  replaceAdd := by
    intro past facts locals lhs rhs edit agree accepted
    obtain ⟨_, _, _, _, left, leftFound, _, rfl⟩ := match_exact accepted
    have readLeft : readWord entry locals lhs = left.eval entry locals := agree.2 lhs left leftFound
    change readWord entry locals lhs + readWord entry locals rhs = _
    rw [readLeft, permute_eval]
    let x := readWord entry locals left.left
    let y := readWord entry locals left.right
    let z := readWord entry locals rhs
    change (x + y) + z = (x + z) + y
    calc
      (x + y) + z = x + (y + z) := BitVec.add_assoc _ _ _
      _ = x + (z + y) := congrArg (x + ·) (BitVec.add_comm _ _)
      _ = (x + z) + y := (BitVec.add_assoc _ _ _).symm

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program : Program SubZero.Opcode inputs out}
variable {rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs}

theorem step_agrees (accepted : step? ids program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (rewrite.flow.eval model entry PUnit.unit) :=
  AddRewrite.scan_agrees (sound ids entry) program.dataflow (Prefix.empty_agrees entry) accepted

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine
