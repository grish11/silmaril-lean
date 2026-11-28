module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Proofs

open CategoryTheory
open RVSDG (Port Tuple)
open Memory.Diamond.Institution (pullInput pullInput_get reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature} {cells : Nat}
variable {args : List ValueSort} {sort : ValueSort}

theorem slot_eq_iff {left right : Port args sort} : Quads.slot left = Quads.slot right ↔ left = right := by
  refine ⟨?_, congrArg Quads.slot⟩
  induction left with
  | head =>
    cases right <;> simp [Quads.slot]
  | tail left ih =>
    cases right with
    | head => simp [Quads.slot]
    | tail right =>
      intro equal
      exact congrArg Port.tail (ih (Nat.succ.inj equal))

theorem portsOf_complete (port : Port args sort) : port ∈ portsOf sort args := by
  induction port with
  | @head kind rest =>
    cases kind <;> exact List.Mem.head _
  | @tail kind other rest port ih =>
    have tailMem : Port.tail (s := other) port ∈ (portsOf kind rest).map Port.tail :=
      List.mem_map_of_mem ih
    cases kind <;> cases other
    · exact List.Mem.tail _ tailMem
    · exact tailMem
    · exact tailMem
    · exact List.Mem.tail _ tailMem

theorem admitsInput_iff (cells : Nat) (args : List ValueSort) :
    admitsInput cells args = true ↔ Nonempty (Tuple (Val cells) args) := by
  constructor
  · intro admitted
    obtain ⟨input, _⟩ := Option.isSome_iff_exists.mp admitted
    exact ⟨input⟩
  · rintro ⟨input⟩
    induction input with
    | nil => rfl
    | @cons sort rest value tail ih =>
      cases sort with
      | word => simpa [admitsInput, defaultInput?] using ih
      | address =>
        have positive : 0 < cells := Nat.zero_lt_of_lt (show (value : Address cells).val < cells from value.isLt)
        simpa [admitsInput, defaultInput?, positive] using ih

theorem checkNoIdentification_iff (h : P ⟶ Q) (sort : ValueSort) :
    checkNoIdentification h sort = true ↔ Function.Injective (fun port : Port P.args sort => h.port port) := by
  simp only [checkNoIdentification, List.all_eq_true, decide_eq_true_eq, slot_eq_iff]
  exact ⟨fun all _ _ equal => all _ (portsOf_complete _) _ (portsOf_complete _) equal,
    fun injective _ _ _ _ equal => injective equal⟩

private theorem checkFibresOf_iff (h : P ⟶ Q) (input : Tuple (Val cells) P.args) (sort : ValueSort) :
    checkFibresOf h input sort = true ↔
      ∀ (left right : Port P.args sort), h.port left = h.port right → input.get left = input.get right := by
  simp only [checkFibresOf, List.all_eq_true, decide_eq_true_eq, slot_eq_iff]
  exact ⟨fun all _ _ => all _ (portsOf_complete _) _ (portsOf_complete _), fun all _ _ _ _ => all _ _⟩

theorem checkFibres_iff (h : P ⟶ Q) (input : Tuple (Val cells) P.args) :
    checkFibres h input = true ↔ FibreConsistent h input := by
  simp only [checkFibres, Bool.and_eq_true, checkFibresOf_iff]
  exact ⟨fun ⟨words, addresses⟩ sort => by cases sort <;> assumption, fun all => ⟨all, all⟩⟩

private theorem input_eq_of_get (left right : Tuple (Val cells) args)
    (equal : ∀ {sort} (port : Port args sort), left.get port = right.get port) : left = right := by
  rw [← Quads.tabulate_get_eq left, ← Quads.tabulate_get_eq right]
  exact congrArg (Quads.tabulate args) (funext fun _ => funext fun port => equal port)

private theorem pull_filled (h : P ⟶ Q) (input : Tuple (Val cells) P.args) (fallback : Tuple (Val cells) Q.args)
    (consistent : FibreConsistent h input) : pullInput h.port (fill h input fallback) = input := by
  apply input_eq_of_get
  intro sort port
  rw [pullInput_get, fill, Quads.get_tabulate]
  split
  · rename_i source found
    have matched : (Quads.slot (h.port source) == Quads.slot (h.port port)) = true :=
      List.find?_some (p := fun p => Quads.slot (h.port p) == Quads.slot (h.port port)) found
    exact consistent source port (slot_eq_iff.mp (Nat.eq_of_beq_eq_true matched))
  · rename_i missing
    have rejected := (List.find?_eq_none.mp missing) port (portsOf_complete port)
    simp at rejected

theorem inReductImage_iff (h : P ⟶ Q) (input : Tuple (Val cells) P.args) :
    InReductImage h input ↔ Nonempty (Tuple (Val cells) Q.args) ∧ FibreConsistent h input := by
  constructor
  · rintro ⟨target, equal⟩
    have pulled : pullInput h.port target = input := by
      change (⟨cells, pullInput h.port target⟩ : EntryModel P) = ⟨cells, input⟩ at equal
      simpa only [EntryModel.mk.injEq, heq_eq_eq, true_and] using equal
    refine ⟨⟨target⟩, fun left right same => ?_⟩
    rw [← pulled, pullInput_get, pullInput_get, same]
  · rintro ⟨⟨fallback⟩, consistent⟩
    exact ⟨fill h input fallback, congrArg (EntryModel.mk cells) (pull_filled h input fallback consistent)⟩

theorem liftInput?_sound (h : P ⟶ Q) {input : Tuple (Val cells) P.args} {target : Tuple (Val cells) Q.args}
    (lifted : liftInput? h input = some target) : reduct h ⟨cells, target⟩ = ⟨cells, input⟩ := by
  cases fallback : defaultInput? cells Q.args with
  | none => simp [liftInput?, fallback] at lifted
  | some initial =>
    by_cases agrees : checkFibres h input = true
    · have filled : fill h input initial = target := by simpa [liftInput?, fallback, agrees] using lifted
      subst target
      exact congrArg (EntryModel.mk cells) (pull_filled h input initial ((checkFibres_iff h input).mp agrees))
    · simp [liftInput?, fallback, agrees] at lifted

theorem liftInput?_isSome_iff (h : P ⟶ Q) (input : Tuple (Val cells) P.args) :
    (liftInput? h input).isSome = true ↔ InReductImage h input := by
  constructor
  · intro yes
    obtain ⟨target, lifted⟩ := Option.isSome_iff_exists.mp yes
    exact ⟨target, liftInput?_sound h lifted⟩
  · intro image
    obtain ⟨nonempty, agrees⟩ := (inReductImage_iff h input).mp image
    obtain ⟨initial, fallback⟩ := Option.isSome_iff_exists.mp ((admitsInput_iff cells Q.args).mpr nonempty)
    simp [liftInput?, fallback, (checkFibres_iff h input).mpr agrees]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Proofs
