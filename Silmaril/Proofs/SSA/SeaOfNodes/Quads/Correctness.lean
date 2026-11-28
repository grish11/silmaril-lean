module

public import Silmaril.SSA.SeaOfNodes.Quads.Defs
import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Proofs

open RVSDG (PortType Port Tuple Origin Wires Locals)
open Diamond (Ty ValueSort Signature Model Val dataPorts sortValue)

universe u v w

theorem get_write_same {T : Type u} {F : T → Type w} {ts : List T} {t : T}
    (dest : Port ts t) (value : F t) (bank : Tuple F ts) :
    (write dest value bank).get dest = value := by
  induction dest with
  | head => cases bank; rfl
  | tail _ ih => cases bank; exact ih value _

theorem get_write_other {T : Type u} {F : T → Type w} {ts : List T} {t s : T}
    (dest : Port ts t) (source : Port ts s) (value : F t) (bank : Tuple F ts)
    (different : slot source ≠ slot dest) :
    (write dest value bank).get source = bank.get source := by
  induction dest with
  | head =>
    cases bank
    cases source with
    | head => exact (different rfl).elim
    | tail => rfl
  | tail dest ih =>
    cases bank
    cases source with
    | head => rfl
    | tail source => exact ih source value _ (fun eq => different (congrArg (· + 1) eq))

private theorem get_map {T : Type u} {F : T → Type v} {G : T → Type w}
    {ts : List T} {t : T} (f : ∀ t, F t → G t) (bank : Tuple F ts) (port : Port ts t) :
    (bank.map f).get port = f t (bank.get port) := by
  induction port with
  | head => cases bank; rfl
  | tail _ ih => cases bank; exact ih _

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out result : ValueSort Data}
variable {args extra : List (Ty Data)} {past : List (List (Ty Data))}

theorem rebind_same (current : Wires args past (dataPorts regs))
    (dest : Port (dataPorts regs) (.value result)) :
    (rebind current dest).get dest = .output (Diamond.lastIndex [.value result] past)
      (Diamond.lastPort .head past) :=
  get_write_same dest _ _

theorem rebind_other (current : Wires args past (dataPorts regs))
    (dest : Port (dataPorts regs) (.value result)) {t : Ty Data}
    (source : Port (dataPorts regs) t) (different : slot source ≠ slot dest) :
    (rebind current dest).get source = keep (current.get source) :=
  (get_write_other dest source _ _ different).trans (get_map _ current source)

theorem map_write {T : Type u} {F : T → Type v} {G : T → Type w}
    {ts : List T} {t : T} (f : ∀ t, F t → G t) (dest : Port ts t)
    (value : F t) (bank : Tuple F ts) :
    (write dest value bank).map f = write dest (f t value) (bank.map f) := by
  induction dest with
  | head => cases bank; rfl
  | tail _ ih =>
    cases bank with
    | cons head tail => exact congrArg (Tuple.cons (f _ head)) (ih value tail)

private theorem cons_eq {T : Type u} {F : T → Type w} {t : T} {ts : List T}
    {a b : F t} {xs ys : Tuple F ts} (head : a = b) (tail : xs = ys) :
    Tuple.cons a xs = .cons b ys := by
  cases head
  cases tail
  rfl

private def readOrigin {F : Ty Data → Type w} {t : Ty Data}
    (origin : Origin args past t) (entry : Tuple F args) (locals : Locals F past) : F t :=
  (Wires.read (.cons origin .nil) entry locals).get .head

private theorem read_keep {F : Ty Data → Type w} {t : Ty Data}
    (origin : Origin args past t) (entry : Tuple F args)
    (locals : Locals F past) (value : Tuple F extra) :
    readOrigin (keep origin) entry (locals.snoc value) = readOrigin origin entry locals := by
  cases origin with
  | arg => rfl
  | output index port =>
    induction past with
    | nil => exact index.elim0
    | cons head tail ih =>
      revert port
      refine Fin.cases ?_ (fun i p => ?_) index
      · intro p
        rfl
      · exact ih locals.2 i p

private theorem read_latest {F : Ty Data → Type w}
    (entry : Tuple F args) (locals : Locals F past)
    (value : F (.value result)) :
    readOrigin (.output (Diamond.lastIndex [.value result] past) (Diamond.lastPort .head past))
      entry (locals.snoc (Tuple.cons (F := F) (t := PortType.value result) value .nil)) = value := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact ih locals.2

private theorem read_kept {F : Ty Data → Type w} {ports : List (Ty Data)}
    (wires : Wires args past ports) (entry : Tuple F args)
    (locals : Locals F past) (value : Tuple F extra) :
    Wires.read (wires.map (fun _ origin => keep (added := extra) origin)) entry (locals.snoc value) =
      wires.read entry locals := by
  induction wires with
  | nil => rfl
  | cons origin _ ih => exact cons_eq (read_keep origin entry locals value) ih

theorem read_rebind {F : Ty Data → Type w}
    (entry : Tuple F args) (locals : Locals F past)
    (current : Wires args past (dataPorts regs))
    (dest : Port (dataPorts regs) (.value result)) (value : F (.value result)) :
    (rebind current dest).read entry
      (locals.snoc (Tuple.cons (t := PortType.value result) value .nil)) =
      write dest value (current.read entry locals) := by
  change (rebind current dest).map (fun _ origin =>
    readOrigin origin entry
      (locals.snoc (Tuple.cons (t := PortType.value result) value .nil))) = _
  rw [rebind, map_write, read_latest]
  exact congrArg (write dest value)
    (read_kept current entry locals (Tuple.cons (t := PortType.value result) value .nil))

theorem get_read (m : Model.{u, v, w} Op) {ports : List (Ty Data)} {t : Ty Data}
    (current : Wires args past ports) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) (src : Port ports t) :
    (current.read entry locals).get src = Diamond.read m (current.get src) entry locals :=
  get_map (fun _ origin => Diamond.read m origin entry locals) current src

theorem read_operands {F : Ty Data → Type w} {ports : List (Ty Data)}
    (operands : Tuple (Port (dataPorts regs)) ports)
    (entry : Tuple F args) (locals : Locals F past)
    (current : Wires args past (dataPorts regs)) :
    Wires.read (operands.map (fun _ src => current.get src)) entry locals =
      operands.map (fun _ src => (current.read entry locals).get src) := by
  induction operands with
  | nil => rfl
  | cons src _ ih => exact cons_eq (get_map (fun _ wire => readOrigin wire entry locals) current src).symm ih

theorem quad_step_read (quad : Quad Op regs) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) :
    (rebind current quad.dest).read entry
      (locals.snoc (.cons (m.run quad.op ((quad.inputWires current).read entry locals)) .nil)) =
      quad.eval m (current.read entry locals) := by
  refine (read_rebind entry locals current quad.dest _).trans ?_
  simp only [Quad.inputWires, Quad.eval, read_operands]

theorem get_tabulate {T : Type u} {F : T → Type w} {ts : List T} {t : T}
    (f : ∀ {s}, Port ts s → F s) (port : Port ts t) :
    (tabulate ts f).get port = f port := by
  induction port with
  | head => rfl
  | tail _ ih => exact ih _

theorem initial_get {t : Ty Data} (port : Port (dataPorts regs) t) :
    (initial regs).get port = .arg port :=
  get_tabulate _ port

theorem tabulate_get_eq {T : Type u} {F : T → Type w} {ts : List T} (tuple : Tuple F ts) :
    tabulate ts (fun p => tuple.get p) = tuple := by
  induction tuple with
  | nil => rfl
  | cons head tail ih => exact congrArg (Tuple.cons head) ih

theorem read_tabulate {F : Ty Data → Type w} (ports : List (Ty Data))
    (wires : ∀ {t}, Port ports t → Origin args past t)
    (entry : Tuple F args) (locals : Locals F past) :
    Wires.read (tabulate ports wires) entry locals =
      tabulate ports (fun p => (Wires.read (.cons (wires p) .nil) entry locals).get .head) := by
  induction ports with
  | nil => rfl
  | cons _ _ ih =>
    exact congrArg (Tuple.cons (readOrigin (wires .head) entry locals)) (ih (fun p => wires (.tail p)))

theorem read_initial {F : Ty Data → Type w}
    (entry : Tuple F (dataPorts regs)) :
    (initial regs).read entry PUnit.unit = entry :=
  (read_tabulate (past := []) _ (fun port => .arg port) entry PUnit.unit).trans (tabulate_get_eq entry)

theorem lowerFrom_eval (code : Code Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) :
    (code.lowerFrom current).eval m.toRVSDG entry locals =
      .cons (code.eval m (current.read entry locals)) .nil := by
  induction code generalizing past with
  | ret source =>
    change Tuple.cons (t := .value out) (Diamond.read m (current.get source) entry locals) .nil =
      .cons ((current.read entry locals).get source) .nil
    exact cons_eq (get_read m current entry locals source).symm rfl
  | assign dest op operands next ih =>
    simp only [Code.lowerFrom, RVSDG.Term.eval, Quad.node, RVSDG.Shape.eval, Diamond.Model.toRVSDG]
    rw [ih]
    exact congrArg (fun bank => Tuple.cons (F := Val m.value) (t := PortType.value out) (next.eval m bank) .nil)
      (quad_step_read (Quad.mk _ _ dest op operands) m entry locals current)

theorem lower_run (code : Code Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) :
    code.lower.run m.toRVSDG entry = .cons (code.eval m entry) .nil := by
  calc
    _ = (code.lowerFrom (initial regs)).run m.toRVSDG entry :=
      RVSDG.Term.run_toGraph _ _ _
    _ = _ := (lowerFrom_eval (past := []) code m entry PUnit.unit (initial regs)).trans
      (congrArg (fun bank => Tuple.cons (F := Val m.value) (t := PortType.value out) (code.eval m bank) .nil)
        (read_initial entry))

end Silmaril.SSA.SeaOfNodes.Quads.Proofs
