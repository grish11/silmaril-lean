module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Thms
import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.Thms
import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (Program)
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned
open Silmaril.SSA.SeaOfNodes.GVN.WordNumber (Key entryKeys)
open Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern (Agrees Decodes Id IdVal Table entryIds readId)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (word wordPort)
open Silmaril.SSA.RVSDG (Port Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Program inputs sigs [word]}

private theorem arm_spec (entry : Tuple IdVal (dataPorts inputs))
    (shared : SharedIds sigs) (table : Table)
    (agrees : Agrees table entry shared (entryKeys inputs) (ValueNumbers.sharedKeys p)) (slot : Slot) :
    let result := numberArm p entry shared table slot
    table <+: result.1 ∧ (table.Nodup → result.1.Nodup) ∧
      Decodes result.1 result.2 (ValueNumbers.phiKey p (ValueNumbers.sharedKeys p) slot) :=
  let arm := p.diamond.arms slot
  let ⟨extendsTable, unique, final⟩ := Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.eval_spec arm.dataflow agrees
  ⟨extendsTable, unique, final (arm.outputs.get .head)⟩

theorem cuts_agree (p : Program inputs sigs [word]) :
    let cuts := numberCuts p
    cuts.table.Nodup ∧
      (∀ port : Port (dataPorts inputs) wordPort, Decodes cuts.table (cuts.entry.get port) (.argument port)) ∧
      (∀ wire : SharedWord inputs sigs, Decodes cuts.table (readId cuts.entry cuts.shared wire)
        (ValueNumbers.operandKey (ValueNumbers.sharedKeys p) wire)) ∧
      ∀ slot, Decodes cuts.table (cuts.phi slot) (ValueNumbers.phiKey p (ValueNumbers.sharedKeys p) slot) := by
  let entry := entryIds inputs
  let shared := Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.eval entry.2 p.diamond.shared entry.1 PUnit.unit
  let first := numberArm p entry.2 shared.2 shared.1 .first
  obtain ⟨entryUnique, entryAgrees⟩ := Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.entry_spec inputs
  obtain ⟨entryExtends, sharedUnique, sharedAgrees⟩ :=
    Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.eval_spec p.diamond.shared entryAgrees
  obtain ⟨firstExtends, firstUnique, firstDecodes⟩ := arm_spec (p := p) entry.2 shared.2 shared.1 sharedAgrees .first
  obtain ⟨secondExtends, secondUnique, secondDecodes⟩ :=
    arm_spec (p := p) entry.2 shared.2 first.1 (fun wire => (sharedAgrees wire).mono firstExtends) .second
  have sharedExtends := firstExtends.trans secondExtends
  refine ⟨secondUnique (firstUnique (sharedUnique entryUnique)), ?_, ?_, ?_⟩
  · intro port
    exact (Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.entry_argument port).mono (entryExtends.trans sharedExtends)
  · exact fun wire => (sharedAgrees wire).mono sharedExtends
  · intro slot
    cases slot
    · exact firstDecodes.mono secondExtends
    · exact secondDecodes

private theorem matches_self {args : List (Ty Unit)} (key : Key args) : key.matches key = true := by
  induction key <;> simp [Key.matches, *]

private theorem id_check_eq {table : Table} (unique : table.Nodup) {lhs rhs : Id}
    {leftKey rightKey : Key (dataPorts inputs)}
    (left : Decodes table lhs leftKey) (right : Decodes table rhs rightKey) :
    decide (lhs = rhs) = leftKey.matches rightKey := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, Decodes.id_eq_iff unique left right]
  exact ⟨fun same => same ▸ matches_self _, Key.eq_of_matches⟩

theorem check_eq_structural (p : Program inputs sigs [word]) (rep : EntryAdd p) :
    Interned.check p rep = ValueNumbers.check p rep := by
  obtain ⟨unique, arguments, shared, arms⟩ := cuts_agree p
  cases found : addOperands? rep.key with
  | none => simp [Interned.check, ValueNumbers.check, found]
  | some key =>
    obtain ⟨⟨lhs, rhs⟩, exactKey⟩ := key
    simp only [Interned.check, ValueNumbers.check, found]
    rw [id_check_eq unique (shared lhs) (arguments p.residual),
      id_check_eq unique (shared rhs) (arms .first), id_check_eq unique (shared rhs) (arms .second)]

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned
