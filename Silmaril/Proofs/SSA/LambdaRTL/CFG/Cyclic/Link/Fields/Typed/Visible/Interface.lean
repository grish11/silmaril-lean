module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

private theorem mem_enumerate (ty : PacketType) (packet : Denote ty) :
    packet ∈ ty.enumerate := by
  induction ty with
  | base x => exact x.elim
  | empty => exact packet.elim
  | unit => cases packet; exact List.mem_cons_self
  | product x y ihX ihY =>
    obtain ⟨left, right⟩ := packet
    exact List.mem_product.mpr ⟨ihX left, ihY right⟩
  | coprod x y ihX ihY =>
    cases packet with
    | inl left => exact List.mem_append_left _ (List.mem_map_of_mem (ihX left))
    | inr right => exact List.mem_append_right _ (List.mem_map_of_mem (ihY right))

variable {F : Type} [DecidableEq F] {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  {left right : Program signature inputs outputs}

theorem mismatch_none : left.firstMismatch? right = none ↔
    ∀ input packet, left.weakEqAt? right input packet = true := by
  rw [Program.firstMismatch?, List.find?_eq_none]
  constructor
  · intro passed input packet
    have mem : (⟨input, packet⟩ : PacketAt inputs) ∈
        (List.finRange a).sigma (fun i => (inputs i).enumerate) :=
      List.mem_sigma.mpr ⟨List.mem_finRange input, mem_enumerate (inputs input) packet⟩
    simpa using passed ⟨input, packet⟩ mem
  · rintro passed ⟨input, packet⟩ _
    simp [passed input packet]

theorem mismatch_some {p : PacketAt inputs} (found : left.firstMismatch? right = some p) :
    ¬ left.weakEqAt? right p.1 p.2 = true := by
  unfold Program.firstMismatch? at found
  simpa using List.find?_some found

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
