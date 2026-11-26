module

public import Silmaril.SSA.PEG.Bridge.RVSDG.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.RVSDG.Correctness

public section

namespace Silmaril.SSA.PEG.Bridge

open RVSDG (Tuple)

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params results ins : List (Ty Data)} {n : Nat} {out : Ty Data}

theorem from_toPorts {F : ValuePort Data → Type} {ts : List (Ty Data)}
    (xs : Tuple (fun t => F (.value t)) ts) :
    fromPorts ts (toPorts (F := F) xs) = xs :=
  Proofs.from_toPorts xs

theorem to_fromPorts {F : ValuePort Data → Type} {ts : List (Ty Data)}
    (xs : Tuple F (valuePorts ts)) : toPorts (fromPorts ts xs) = xs :=
  Proofs.to_fromPorts xs

/-- A Figure 11 primitive returns bottom if any input slot is bottom, even
if the interpretation would ignore that operand on defined tuples. -/
theorem interpret_op_eq_none (m : Interpretation P) (env : Tuple m.Value params)
    (idx : Index 0) (op : P ins out)
    (read : ∀ (s : Fin ins.length) (j : Index 0),
      ((Label.op op : Label P params (Fin 0) ins out).kind s).Changes idx j →
        Option (m.Value ins[s]))
    (slot : Fin ins.length) (bottom : read slot idx rfl = none) :
    (Label.op op : Label P params (Fin 0) ins out).interpret m env idx read = none :=
  congrArg (fun input : Option (Tuple m.Value ins) => input.elim none (m.run op))
    (Proofs.collect_none ins (fun s => read s idx rfl) slot bottom)

/-- The ordered RVSDG results recover every Figure 11 root, in its declared
position, with some marking definedness. The demand witness is immaterial. -/
theorem observe_translate (g : Graph P params results n 0) (ordered : Ordered g)
    (m : TotalModel P) (env : Tuple m.toPEG.Value params) (idx : Index 0)
    (wf : WellFounded g.Demand) :
    g.observe m.toPEG (g.denote m.toPEG env wf) idx =
      (fromPorts results ((translate g ordered).2.run m.toRVSDG (toPorts env))).map (fun _ => some) :=
  Proofs.translate_correct m env idx g ordered wf

end Silmaril.SSA.PEG.Bridge
