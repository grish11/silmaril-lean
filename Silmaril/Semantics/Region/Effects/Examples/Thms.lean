module

public import Silmaril.Semantics.Region.Effects.Examples.Defs
public import Silmaril.Semantics.Region.Effects.Thms

@[expose] public section
namespace Silmaril.Semantics.Region.Effects.Examples

theorem mixed_payloads : load ∈ ({load, store} : Set (Atom Payload)) ∧
    store ∈ ({load, store} : Set (Atom Payload)) := by simp

theorem ub_is_observed : ub ∈ ({ub} : Set (Atom Payload)) ∧
    ({ub} : Set (Atom Payload)) ≠ ∅ := by simp

theorem direct_does_not_include_callee : syscall ∉ directCall ∧ syscall ∈ calleeSummary := by
  constructor
  · intro h; cases congrArg Sigma.fst h
  · exact Or.inl rfl

theorem direct_roundtrip (a : Atom Payload) : projectDirect (embedDirect.atom a) = some a := by
  cases a; rfl

theorem embedDirect_injective : Function.Injective embedDirect.atom := by
  intro a b h
  exact Option.some.inj (by simpa only [direct_roundtrip] using congrArg projectDirect h)

theorem direct_embedding (effects : Set (Atom Payload)) (a : Atom Payload) :
    embedDirect.atom a ∈ embedDirect.map effects ↔ a ∈ effects :=
  ⟨fun ⟨_, h, eq⟩ => embedDirect_injective eq ▸ h, fun h => ⟨a, h, rfl⟩⟩

def certified : CertifiedBlock contract where
  block := block
  interior := by simp [block, contract]
  direct := by intros; rfl
  control := rfl

theorem final_controls : certified.effects.control = {.next 8, .next 12} := rfl

theorem earlier_definition_kills_use : certified.effects.useDef.uses = ∅ := by
  simp [certified, CertifiedBlock.effects, Block.effects, block, contract, analyze,
    InstructionSummary.prepend, UseDef.sequence]

theorem order_matters :
    (UseDef.sequence (analyze .define).useDef (analyze .use).useDef).uses = ∅ ∧
    (UseDef.sequence (analyze .use).useDef (analyze .define).useDef).uses = {0} := by
  simp [analyze, UseDef.sequence]

theorem selection_keeps_only_definite :
    (UseDef.selection (analyze .define).useDef (analyze .use).useDef).definiteDefs = ∅ := by
  simp [analyze, UseDef.selection]

/-- Normal-exit-only checking would vacuously accept the empty bound here. -/
theorem fault_not_empty_control : ¬ ControlBound faulting (fun _ => True) (fun _ => True) ∅ := by
  intro h
  exact h.2 () [] () "fault" trivial (.refl trivial) rfl

theorem fault_is_observed : MayObservation faulting (fun _ => True) (fun _ => True) (.inr "fault") :=
  ⟨(), [], (), trivial, .refl trivial, rfl⟩

/-- Even a halt without a direct emitted event contributes to the envelope. -/
theorem fault_envelope_nonempty :
    outcomeEnvelope faulting (fun _ => True) (fun _ => True) (fun o => ({o} : Set _)) ≠ ∅ := by
  intro h
  exact ((outcomeEnvelope_le_iff _ _ _ _ _).mp (le_of_eq h))
    (.inr "fault") fault_is_observed rfl

end Silmaril.Semantics.Region.Effects.Examples
