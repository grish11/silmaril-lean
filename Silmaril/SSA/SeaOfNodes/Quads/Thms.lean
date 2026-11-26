module

public import Silmaril.SSA.SeaOfNodes.Quads.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Correctness

/-! # Reaching definitions and exact returned-value agreement for ordered quads -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads

open RVSDG (Port PortType Tuple Origin Wires Locals)
open Diamond (Ty ValueSort Signature Model Val dataPorts)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out result : ValueSort Data}
variable {args : List (Ty Data)} {past : List (List (Ty Data))}

/-- A pointwise map commutes with writing one typed slot. -/
theorem map_write {T : Type u} {F : T → Type v} {G : T → Type w}
    {ts : List T} {t : T} (f : ∀ t, F t → G t) (dest : Port ts t)
    (value : F t) (bank : Tuple F ts) :
    (write dest value bank).map f = write dest (f t value) (bank.map f) :=
  Proofs.map_write f dest value bank

/-- Before any assignment, a use names the corresponding input. -/
theorem initial_get {t : Ty Data} (port : Port (dataPorts regs) t) :
    (initial regs).get port = .arg port :=
  Proofs.initial_get port

/-- Appending a producer does not renumber any earlier producer. -/
theorem keep_producer {added : List (Ty Data)} {t : Ty Data} (origin : Origin args past t) :
    (keep (added := added) origin).producer = origin.producer := by
  cases origin <;> rfl

/-- A write makes this instruction's result the reaching definition of its destination. -/
theorem rebind_same (current : Wires args past (dataPorts regs))
    (dest : Port (dataPorts regs) (.value result)) :
    (rebind current dest).get dest = .output (Diamond.lastIndex [.value result] past)
      (Diamond.lastPort .head past) :=
  Proofs.rebind_same current dest

/-- Overwriting one register preserves the reaching definition of every other register. -/
theorem rebind_other (current : Wires args past (dataPorts regs))
    (dest : Port (dataPorts regs) (.value result)) {t : Ty Data}
    (source : Port (dataPorts regs) t) (different : slot source ≠ slot dest) :
    (rebind current dest).get source = keep (current.get source) :=
  Proofs.rebind_other current dest source different

/-- Wire reading commutes with selecting a typed port. -/
theorem read_get (m : Model.{u, v, w} Op) {ports : List (Ty Data)} {t : Ty Data}
    (current : Wires args past ports) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) (port : Port ports t) :
    (current.read entry locals).get port = Diamond.read m (current.get port) entry locals :=
  Proofs.get_read m current entry locals port

/-- Reading a table of port wires reads each entry in order. -/
theorem read_tabulate (m : Model.{u, v, w} Op) (ports : List (Ty Data))
    (wires : ∀ {t}, Port ports t → Origin args past t)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    Wires.read (tabulate ports wires) entry locals =
      tabulate ports (fun p => Diamond.read m (wires p) entry locals) :=
  Proofs.read_tabulate m ports wires entry locals

theorem get_tabulate {T : Type u} {F : T → Type w} {ts : List T} {t : T}
    (f : ∀ {s}, Port ts s → F s) (port : Port ts t) :
    (tabulate ts f).get port = f port :=
  Proofs.get_tabulate f port

theorem tabulate_get_eq {T : Type u} {F : T → Type w} {ts : List T} (tuple : Tuple F ts) :
    tabulate ts (fun p => tuple.get p) = tuple :=
  Proofs.tabulate_get_eq tuple

/-- Reading the initial version map recovers the supplied register bank. -/
theorem read_initial (m : Model.{u, v, w} Op) (entry : Tuple (Val m.value) (dataPorts regs)) :
    (initial regs).read entry PUnit.unit = entry :=
  Proofs.read_initial m entry

/-- Reading the updated map after one producer agrees with the source write. -/
theorem Quad.step_read (quad : Quad Op regs) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) :
    (rebind current quad.dest).read entry
      (locals.snoc (.cons (m.run quad.op ((quad.inputWires current).read entry locals)) .nil)) =
      quad.eval m (current.read entry locals) :=
  Proofs.quad_step_read quad m entry locals current

/-- Running the lowered graph returns exactly the value of ordered register execution. -/
theorem Code.lower_run (code : Code Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) :
    code.lower.run m.toRVSDG entry = .cons (code.eval m entry) .nil :=
  Proofs.lower_run code m entry

/-- The straight-line evaluator also agrees under a typed map into an open graph prefix. -/
theorem Code.lowerFrom_eval (code : Code Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) :
    (code.lowerFrom current).eval m.toRVSDG entry locals =
      .cons (code.eval m (current.read entry locals)) .nil :=
  Proofs.lowerFrom_eval code m entry locals current

end Silmaril.SSA.SeaOfNodes.Quads
