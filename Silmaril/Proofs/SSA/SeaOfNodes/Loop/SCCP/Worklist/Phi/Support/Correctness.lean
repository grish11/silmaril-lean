module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Proofs

open Diamond (Dataflow Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact evalFacts gather readLocal)
open RVSDG (Locals Origin Port Tuple Wires extend)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data} {m : Model.{u, v, w} Op}
variable {value : Data → Type w} {n : Nat} {ports args : List (Ty Data)} {past sigs : List (List (Ty Data))}

private def Agrees (known : Finset (Fin n)) (supports : Tuple (Ports n) ports)
    (left right : Tuple (Fact value) ports) : Prop :=
  ∀ {t} (port : Port ports t), supports.get port ⊆ known → left.get port = right.get port

private def LocalsAgree (known : Finset (Fin n)) (supports : Locals (Ports n) past)
    (left right : Locals (Fact value) past) : Prop :=
  ∀ node, Agrees known (supports.get node) (left.get node) (right.get node)

private theorem snoc_agrees {known : Finset (Fin n)} {supports : Locals (Ports n) past}
    {left right : Locals (Fact value) past} {support : Tuple (Ports n) ports}
    {x y : Tuple (Fact value) ports} (old : LocalsAgree known supports left right)
    (new : Agrees known support x y) :
    LocalsAgree known (supports.snoc support) (left.snoc x) (right.snoc y) := by
  induction past with
  | nil =>
    exact fun i => Fin.cases (motive := fun j =>
      Agrees known ((supports.snoc support).get j) ((left.snoc x).get j) ((right.snoc y).get j))
      new (fun j => j.elim0) i
  | cons head tail ih =>
    exact fun i => Fin.cases (motive := fun j =>
      Agrees known ((supports.snoc support).get j) ((left.snoc x).get j) ((right.snoc y).get j))
      (old 0) (fun j => ih (fun k => old k.succ) j) i

private theorem read_agrees {known : Finset (Fin n)} {t : Ty Data}
    (origin : Origin args past t) {argsSupport : Tuple (Ports n) args} {leftArgs rightArgs : Tuple (Fact value) args}
    {supports : Locals (Ports n) past} {left right : Locals (Fact value) past}
    (sameArgs : Agrees known argsSupport leftArgs rightArgs)
    (sameLocals : LocalsAgree known supports left right)
    (subset : read argsSupport supports origin ⊆ known) :
    readLocal leftArgs left origin = readLocal rightArgs right origin := by
  cases origin with
  | arg p => exact sameArgs p subset
  | output i p => exact sameLocals i p subset

private theorem wires_agree {known : Finset (Fin n)}
    (wires : Wires args past ports) {argsSupport : Tuple (Ports n) args} {leftArgs rightArgs : Tuple (Fact value) args}
    {supports : Locals (Ports n) past} {left right : Locals (Fact value) past}
    (sameArgs : Agrees known argsSupport leftArgs rightArgs)
    (sameLocals : LocalsAgree known supports left right)
    (subset : unions (wires.read argsSupport supports) ⊆ known) :
    wires.read leftArgs left = wires.read rightArgs right := by
  induction wires with
  | nil => rfl
  | cons origin rest ih =>
    have parts : read argsSupport supports origin ∪ unions (Wires.read rest argsSupport supports) ⊆ known := by
      cases origin <;> exact subset
    obtain ⟨head, tail⟩ := Finset.union_subset_iff.mp parts
    have same := congrArg₂ Tuple.cons (read_agrees origin sameArgs sameLocals head) (ih tail)
    cases origin <;> exact same

private theorem table_agrees {known : Finset (Fin n)} (flow : Dataflow Op args past sigs)
    {argsSupport : Tuple (Ports n) args} {leftArgs rightArgs : Tuple (Fact m.value) args}
    {supports : Locals (Ports n) past} {left right : Locals (Fact m.value) past}
    (sameArgs : Agrees known argsSupport leftArgs rightArgs)
    (sameLocals : LocalsAgree known supports left right) :
    LocalsAgree known (table argsSupport flow supports)
      (evalFacts m leftArgs flow left) (evalFacts m rightArgs flow right) := by
  induction flow with
  | nil => exact sameLocals
  | cons op wires rest ih =>
    apply ih
    apply snoc_agrees sameLocals
    intro t port supported
    cases port with
    | head =>
      exact congrArg (fun operands => Flat.map (m.run op) (gather operands))
        (wires_agree wires sameArgs sameLocals supported)
    | tail p => cases p

private theorem append_agrees {known : Finset (Fin n)} {tail : List (Ty Data)}
    {support : Tuple (Ports n) ports} {left right : Tuple (Fact value) ports}
    {tailSupport : Tuple (Ports n) tail} {leftTail rightTail : Tuple (Fact value) tail}
    (first : Agrees known support left right) (last : Agrees known tailSupport leftTail rightTail) :
    Agrees known (appendTuple tailSupport support) (appendTuple leftTail left) (appendTuple rightTail right) := by
  induction support with
  | nil => cases left; cases right; exact last
  | cons head rest ih =>
    cases left with
    | cons x xs =>
      cases right with
      | cons y ys =>
        intro t port
        cases port with
        | head => exact first .head
        | tail p => exact ih (fun q => first (.tail q)) p

private theorem numbered_agrees {known : Finset (Fin n)} {ports : List (Ty Data)}
    (number : Fin ports.length → Fin n) {left right : BankFacts value ports}
    (same : ∀ i, number i ∈ known → left i = right i) :
    Agrees known (numberedPorts ports number) (bankTuple left) (bankTuple right) := by
  induction ports with
  | nil => intro t port; cases port
  | cons head rest ih =>
    intro t port subset
    cases port with
    | head => exact same 0 (subset (Finset.mem_singleton_self _))
    | tail p => exact ih (fun i => number i.succ) (fun i => same i.succ) p subset

variable {inputs carried : List (ValueSort Data)} {t : Ty Data}

theorem wire_agrees (flow : Dataflow Op (Loop.headerPorts inputs carried) [] sigs)
    (origin : Origin (Loop.headerPorts inputs carried) (extend [] sigs) t)
    (input : Tuple (Fact m.value) (dataPorts inputs))
    {left right : BankFacts m.value (dataPorts carried)}
    (same : ∀ i ∈ wire (inputs := inputs) (carried := carried) flow origin, left i = right i) :
    let leftArgs := appendTuple (bankTuple left) input
    let rightArgs := appendTuple (bankTuple right) input
    readLocal leftArgs (evalFacts m leftArgs flow PUnit.unit) origin =
      readLocal rightArgs (evalFacts m rightArgs flow PUnit.unit) origin := by
  let supports := headerPorts inputs carried
  let known := wire (inputs := inputs) (carried := carried) flow origin
  have hArgs : Agrees known supports (appendTuple (bankTuple left) input) (appendTuple (bankTuple right) input) :=
    append_agrees (fun _ _ => rfl) (numbered_agrees id same)
  have hLocals := table_agrees (m := m) flow hArgs (supports := PUnit.unit) (left := PUnit.unit)
    (right := PUnit.unit) (fun i => i.elim0)
  exact read_agrees origin hArgs hLocals Finset.Subset.rfl

theorem restrictBank_eq_iff (support : Finset (Fin ports.length)) {left right : BankFacts value ports} :
    restrictBank support left = restrictBank support right ↔ ∀ i ∈ support, left i = right i := by
  constructor
  · intro same i member
    simpa [restrictBank, member] using congrFun same i
  · intro same
    funext i
    by_cases member : i ∈ support <;> simp [restrictBank, member, same]

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Proofs
