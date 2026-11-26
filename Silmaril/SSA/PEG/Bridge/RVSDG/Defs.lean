module

public import Silmaril.SSA.PEG.Semantics.Defs

/-! # Loop-free, topologically numbered PEGs as ordered RVSDG value regions -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge

open RVSDG (Port Tuple Origin Wires)

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params results : List (Ty Data)} {n : Nat}

/-- Figure 11 may demand any operand, including either arm of φ.
Every such reference must go to an earlier vertex. -/
def Ordered (g : Graph P params results n 0) : Prop :=
  ∀ (i : Fin n) (s : Fin (g.node i).inputs.length), ((g.node i).arg s).id.val < i.val

instance (g : Graph P params results n 0) : Decidable (Ordered g) :=
  inferInstanceAs (Decidable (∀ (i : Fin n) (s : Fin (g.node i).inputs.length),
    ((g.node i).arg s).id.val < i.val))

/-- Vertex number decreases along every Figure 11 demand. -/
theorem Ordered.demandWellFounded {g : Graph P params results n 0} (ordered : Ordered g) :
    WellFounded g.Demand :=
  Subrelation.wf (fun {a b} ⟨_, ⟨slot, _, edge⟩, _⟩ =>
    show a.1.val < b.1.val from edge ▸ ordered b.1 slot) (measure (fun q : Request n 0 => q.1.val)).wf

/-- A total pure model of the PEG instruction alphabet. Bool and count retain
their Figure 11 carriers. -/
structure TotalModel (P : InstructionSet.{0,0} Data) where
  carrier : Data → Type
  run {ins out} : P ins out → Tuple (Ty.Value carrier) ins → Ty.Value carrier out

abbrev TotalModel.toPEG (m : TotalModel P) : Interpretation P :=
  ⟨m.carrier, fun op args => some (m.run op args)⟩

/-- The target instruction profiles. Copies represent parameter vertices and
selects represent φ vertices. Both have one value result. -/
inductive Operation (P : InstructionSet.{0,0} Data) : List (Ty Data) → Ty Data → Type
  | copy {out} : Operation P [out] out
  | primitive {ins out} : P ins out → Operation P ins out
  | select {out} : Operation P [.bool, out, out] out

def Operation.eval (m : TotalModel P) {ins out} :
    Operation P ins out → Tuple m.toPEG.Value ins → m.toPEG.Value out
  | .copy, .cons x .nil => x
  | .primitive op, xs => m.run op xs
  | .select, .cons b (.cons x (.cons y .nil)) => if b.down then x else y

abbrev ValuePort (Data : Type) := RVSDG.PortType (Ty Data) PUnit

abbrev valuePorts (ts : List (Ty Data)) : List (ValuePort Data) :=
  ts.map RVSDG.PortType.value

inductive Opcode (P : InstructionSet.{0,0} Data) : RVSDG.Dialect (Ty Data) PUnit
  | apply {ins out} (op : Operation P ins out) : Opcode P (valuePorts ins) (valuePorts [out])

/-- Move a tuple from the PEG sort indices to the corresponding value ports. -/
def toPorts {F : ValuePort Data → Type} :
    {ts : List (Ty Data)} → Tuple (fun t => F (.value t)) ts → Tuple F (valuePorts ts)
  | _, .nil => .nil
  | _, .cons x xs => .cons x (toPorts (F := F) xs)

def fromPorts {F : ValuePort Data → Type} :
    (ts : List (Ty Data)) → Tuple F (valuePorts ts) → Tuple (fun t => F (.value t)) ts
  | [], .nil => .nil
  | _ :: ts, .cons x xs => .cons x (fromPorts ts xs)

abbrev TotalModel.toRVSDG (m : TotalModel P) : RVSDG.Model (Opcode P) where
  value := m.toPEG.Value
  state _ := PEmpty
  run
    | .apply op, input => .cons (op.eval m (fromPorts _ input)) .nil

def portToValue {t : Ty Data} :
    {ts : List (Ty Data)} → Port ts t → Port (valuePorts ts) (.value t)
  | _, .head => .head
  | _, .tail p => .tail (portToValue p)

namespace Compiler

variable {past : List (List (ValuePort Data))}
variable {t : ValuePort Data}

/-- Keep an old output's number and type when extending the available prefix. -/
def weaken {entry : List (ValuePort Data)} (head : List (ValuePort Data)) :
    Origin entry past t → Origin entry (past ++ [head]) t
  | .arg p => .arg p
  | .output i p =>
    .output ⟨i.val, by simp; omega⟩
      ((List.getElem_append_left i.isLt).symm ▸ p)

/-- The first port of the smallest prefix containing a newly emitted vertex. -/
def newest {entry : List (ValuePort Data)} (past : List (List (ValuePort Data)))
    (out : Ty Data) : Origin entry (past ++ [valuePorts [out]]) (.value out) :=
  .output ⟨past.length, by simp⟩ (by
    simpa using (Port.head : Port (valuePorts [out]) (.value out)))

variable {g : Graph P params results n 0} {k : Nat}

/-- Wires for the emitted vertices, indexed in the original PEG table. -/
abbrev Scope (g : Graph P params results n 0) (k : Nat)
    (past : List (List (ValuePort Data))) :=
  (j : Fin n) → j.val < k → Origin (valuePorts params) past (.value (g.sort j))

def Scope.push (scope : Scope g k past) (i : Fin n) (atCursor : i.val = k) :
    Scope g (k + 1) (past ++ [valuePorts [g.sort i]]) := fun j hj =>
  if old : j.val < k then weaken _ (scope j old)
  else
    have same : i = j := Fin.ext (by omega)
    same ▸ newest past (g.sort i)

def resolve (scope : Scope g k past) {t : Ty Data} (r : Ref g.sort t)
    (bound : r.id.val < k) : Origin (valuePorts params) past (.value t) :=
  r.typed ▸ scope r.id bound

def wireRefs (scope : Scope g k past) :
    {ts : List (Ty Data)} → (rs : Tuple (Ref g.sort) ts) →
    (∀ s : Fin ts.length, (rs.get (portAt ts s)).id.val < k) →
    Wires (valuePorts params) past (valuePorts ts)
  | _, .nil, _ => .nil
  | _, .cons r rs, bound =>
    .cons (resolve scope r (bound 0)) (wireRefs scope rs (fun s => bound s.succ))

def primitive {ins : List (Ty Data)} {out : Ty Data} (op : Operation P ins out)
    (wires : Wires (valuePorts params) past (valuePorts ins)) :
    RVSDG.Node (Opcode P) (valuePorts params) past (valuePorts [out]) :=
  ⟨_, .simple (.apply op), wires, fun j => j.elim0⟩

def lowerLabel {ins : List (Ty Data)} {out : Ty Data} :
    Label P params (Fin 0) ins out → Wires (valuePorts params) past (valuePorts ins) →
      Σ ts, Operation P ts out × Wires (valuePorts params) past (valuePorts ts)
  | .param slot, _ => ⟨_, .copy, .cons (.arg (portToValue slot)) .nil⟩
  | .op op, wires => ⟨_, .primitive op, wires⟩
  | .phi, wires => ⟨_, .select, wires⟩
  | .theta l, _ | .eval l, _ | .pass l, _ => l.elim0

/-- Emit the next PEG vertex, then translate the suffix in the extended scope. -/
def compileFrom (g : Graph P params results n 0) (ordered : Ordered g) :
    (remaining k : Nat) → k + remaining = n → {past : List (List (ValuePort Data))} →
    Scope g k past →
    Σ sigs, RVSDG.Term (Opcode P) (valuePorts params) past sigs (valuePorts results)
  | 0, k, size, _, scope =>
    ⟨[], .ret (wireRefs scope g.roots (fun s => by
      have bound := (g.roots.get (portAt results s)).id.isLt
      omega))⟩
  | remaining + 1, k, size, past, scope =>
    let i : Fin n := ⟨k, by omega⟩
    let source := g.node i
    let op := lowerLabel source.label (wireRefs scope source.args (ordered i))
    let rest := compileFrom g ordered remaining (k + 1) (by omega) (scope.push i rfl)
    ⟨_ :: rest.1, .bind (primitive op.2.1 op.2.2) (fun j => j.elim0) rest.2⟩

end Compiler

/-- Convert the emitted bindings into the existing numbered RVSDG table. -/
def translate (g : Graph P params results n 0) (ordered : Ordered g) :
    Σ sigs, RVSDG.Graph (Opcode P) (valuePorts params) [] sigs (valuePorts results) :=
  let code := Compiler.compileFrom g ordered n 0 (Nat.zero_add _) (fun _ h => by omega)
  ⟨code.1, code.2.toGraph⟩

end Silmaril.SSA.PEG.Bridge
