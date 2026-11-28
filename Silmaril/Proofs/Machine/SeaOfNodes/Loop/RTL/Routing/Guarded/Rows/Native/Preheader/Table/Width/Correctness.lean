module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Prog)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp model word)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires)
open Silmaril.SSA.SeaOfNodes
open Diamond (Dataflow Model Val)
open Diamond.LambdaSSA (Atom encodeTuple inputEnv instruction instruction_deterministic)
open Loop (appendTuple)
open Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Config Diverges DivergenceStep)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

universe w

variable {old new bank : Nat} {entrySigs sigs rightEntry rightSigs : List (List PortTy)}

private theorem mapPrefix_bank {source target bank : List PortTy} {t : PortTy}
    (mapping : ∀ {t}, Port source t → Port target t) (p : Port bank t) :
    mapPrefix (fun p => mapping p) (suffixPort source p) = suffixPort target p := by
  induction source with
  | nil => rfl
  | cons _ _ ih => exact ih (fun p => mapping (.tail p))

theorem headerPort_bank (mapping : InputMap old new) {t : PortTy} (p : Port (wordPorts bank) t) :
    headerPort mapping (suffixPort (wordPorts old) p) = suffixPort (wordPorts new) p :=
  mapPrefix_bank (fun p => mapping.port p) p

private theorem prefix_get {F : PortTy → Type w} {source bank : List PortTy}
    (captures : Tuple F source) (carried : Tuple F bank) {t : PortTy} (p : Port source t) :
    (appendTuple carried captures).get (prefixPort p) = captures.get p := by
  induction p with
  | head => cases captures; rfl
  | tail p ih => cases captures with | cons _ rest => exact ih rest

private theorem mapPrefix_get {F : PortTy → Type w} {source target bank : List PortTy}
    (mapping : ∀ {t}, Port source t → Port target t)
    (captures : Tuple F target) (carried : Tuple F bank) {t : PortTy} (p : Port (source ++ bank) t) :
    (appendTuple carried captures).get (mapPrefix (fun p => mapping p) p) =
      (appendTuple carried (InputPermutation.pullTuple (fun p => mapping p) captures)).get p := by
  induction source with
  | nil => exact suffix_get captures carried p
  | cons head tail ih =>
    cases p with
    | head => exact prefix_get captures carried (mapping .head)
    | tail p => exact ih (fun p => mapping (.tail p)) p

private theorem pull_header {F : PortTy → Type w} {source target bank : List PortTy}
    (mapping : ∀ {t}, Port source t → Port target t) (captures : Tuple F target) (carried : Tuple F bank) :
    InputPermutation.pullTuple (fun p => mapPrefix (fun p => mapping p) p) (appendTuple carried captures) =
      appendTuple carried (InputPermutation.pullTuple (fun p => mapping p) captures) := by
  have ext {ports : List PortTy} (first second : Tuple F ports)
      (agree : ∀ {t} (p : Port ports t), first.get p = second.get p) : first = second := by
    induction first with
    | nil => cases second; rfl
    | cons v rest ih =>
      cases second with
      | cons u tail => exact congrArg₂ Tuple.cons (agree .head) (ih tail (fun p => agree (.tail p)))
  apply ext
  intro _ p
  exact (InputPermutation.get_pullTuple (fun p => mapPrefix (fun p => mapping p) p)
    (appendTuple carried captures) p).trans (mapPrefix_get (fun p => mapping p) captures carried p)

private theorem eval_mapFlow {source target : List PortTy} {past sigs : List (List PortTy)}
    (mapping : ∀ {t}, Port source t → Port target t) (m : Model.{0, 0, w} WordOp)
    (flow : Dataflow WordOp source past sigs) (input : Tuple (Val m.value) target)
    (locals : Locals (Val m.value) past) :
    (mapFlow (fun p => mapping p) flow).eval m input locals =
      flow.eval m (InputPermutation.pullTuple (fun p => mapping p) input) locals := by
  induction flow with
  | nil => rfl
  | cons op args rest ih =>
    simp only [mapFlow, Dataflow.eval, read_mapColumn]
    exact ih _

private theorem read_mapOrigin {source target : List PortTy} {past : List (List PortTy)} {t : PortTy}
    (mapping : ∀ {t}, Port source t → Port target t) (m : Model.{0, 0, w} WordOp)
    (wire : Origin source past t) (input : Tuple (Val m.value) target) (locals : Locals (Val m.value) past) :
    Diamond.read m (mapOrigin (fun p => mapping p) wire) input locals =
      Diamond.read m wire (InputPermutation.pullTuple (fun p => mapping p) input) locals := by
  cases wire with
  | arg p => exact (InputPermutation.get_pullTuple (fun p => mapping p) input p).symm
  | output _ _ => rfl

variable (mapping : InputMap old new) (g : Source old bank entrySigs sigs)
variable (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts new))

theorem initial_mapCaptures :
    (mapCaptures mapping g).initial m input = g.initial m (mapping.pull input) := by
  let column : Wires (wordPorts old) _ (wordPorts bank) := g.phiInputs .entry
  exact (congrArg (fun locals => (mapping.column column).read input locals)
    (eval_mapFlow (fun p => mapping.port p) m g.preheader input PUnit.unit)).trans
    (mapping.read_column input column (g.preheader.eval m (mapping.pull input) PUnit.unit))

theorem header_read_mapCaptures (carried : Tuple (Val m.value) (wordPorts bank))
    {t : PortTy} (wire : Origin (wordPorts old ++ wordPorts bank) (Silmaril.SSA.RVSDG.extend [] sigs) t) :
    Diamond.read m (mapOrigin (fun p => headerPort mapping p) wire) (appendTuple carried input)
      ((mapCaptures mapping g).header.eval m (appendTuple carried input) PUnit.unit) =
    Diamond.read m wire (appendTuple carried (mapping.pull input))
      (g.header.eval m (appendTuple carried (mapping.pull input)) PUnit.unit) := by
  let portMap := fun {t} (p : Port (wordPorts old ++ wordPorts bank) t) => headerPort mapping p
  let newArgs := appendTuple carried input
  let oldArgs := appendTuple carried (mapping.pull input)
  have pulled : InputPermutation.pullTuple portMap newArgs = oldArgs :=
    pull_header (fun p => mapping.port p) input carried
  let locals := g.header.eval m oldArgs PUnit.unit
  have eval : (mapFlow portMap g.header).eval m newArgs PUnit.unit = locals :=
    (eval_mapFlow (fun p => portMap p) m g.header newArgs PUnit.unit).trans
      (congrArg (fun args => g.header.eval m args PUnit.unit) pulled)
  exact (congrArg (Diamond.read m (mapOrigin portMap wire) newArgs) eval).trans
    ((read_mapOrigin portMap m wire newArgs locals).trans
      (congrArg (fun args => Diamond.read m wire args locals) pulled))

theorem step_mapCaptures (carried : Tuple (Val m.value) (wordPorts bank)) :
    (mapCaptures mapping g).step m input carried = g.step m (mapping.pull input) carried := by
  let portMap := fun {t} (p : Port (wordPorts old ++ wordPorts bank) t) => headerPort mapping p
  let newArgs := appendTuple carried input
  let oldArgs := appendTuple carried (mapping.pull input)
  let code : Dataflow WordOp (wordPorts old ++ wordPorts bank) [] sigs := g.header
  let branch : Origin (wordPorts old ++ wordPorts bank) _ (.value .predicate) := g.predicate
  let result : Origin (wordPorts old ++ wordPorts bank) _ wordPort := g.result
  let feedback : Wires (wordPorts old ++ wordPorts bank) _ (wordPorts bank) := g.phiInputs .backedge
  have pulled : InputPermutation.pullTuple portMap newArgs = oldArgs :=
    pull_header (fun p => mapping.port p) input carried
  let locals := code.eval m oldArgs PUnit.unit
  have eval : (mapFlow portMap code).eval m newArgs PUnit.unit = locals :=
    (eval_mapFlow portMap m code newArgs PUnit.unit).trans (congrArg (fun args => code.eval m args PUnit.unit) pulled)
  have predicate := (read_mapOrigin portMap m branch newArgs locals).trans
    (congrArg (fun args => Diamond.read m branch args locals) pulled)
  have output := (read_mapOrigin portMap m result newArgs locals).trans
    (congrArg (fun args => Diamond.read m result args locals) pulled)
  have next := (read_mapColumn portMap newArgs feedback locals).trans
    (congrArg (fun args => feedback.read args locals) pulled)
  change (let values := (mapFlow portMap code).eval m newArgs PUnit.unit
          if (Diamond.read m (mapOrigin portMap branch) newArgs values).down then
            Sum.inr ((mapColumn portMap feedback).read newArgs values)
          else Sum.inl (Diamond.read m (mapOrigin portMap result) newArgs values)) =
    (if (Diamond.read m branch oldArgs locals).down then Sum.inr (feedback.read oldArgs locals)
      else Sum.inl (Diamond.read m result oldArgs locals))
  dsimp only
  rw [eval, predicate, output, next]

theorem denote_mapCaptures :
    (mapCaptures mapping g).denote m input = g.denote m (mapping.pull input) := by
  simp only [Loop.Graph.denote, initial_mapCaptures, step_mapCaptures]

theorem equation_on_image (right : Source old bank rightEntry rightSigs) :
    (∀ input : WordTuple new,
      (mapCaptures mapping g).denote model input = (mapCaptures mapping right).denote model input) ↔
    ∀ oldInput ∈ Set.range (fun input : WordTuple new => mapping.pull input),
      g.denote model oldInput = right.denote model oldInput := by
  constructor
  · rintro equal _ ⟨input, rfl⟩
    exact (denote_mapCaptures mapping g model input).symm.trans
      ((equal input).trans (denote_mapCaptures mapping right model input))
  · intro equal input
    exact (denote_mapCaptures mapping g model input).trans
      ((equal _ ⟨input, rfl⟩).trans (denote_mapCaptures mapping right model input).symm)

-- A bank from which no counted return is possible must take a backedge.
-- The emitted header executes that backedge and the next bank has the same property.
theorem lower_diverges_of_absent (g : Source new bank entrySigs sigs)
    (input : WordTuple new) (initial : Memory) (absent : g.denote model input = Part.none) :
    Diverges (instruction model) (.region (inputEnv model input) (Generic.lower g) initial) := by
  let env := inputEnv model input
  have follows (old : WordTuple bank) (noReturn : ∀ count value, ¬ g.ReturnsAfter model input count old value) :
      Diverges (instruction model) (.follow env (Generic.blocks g) 0 (encodeTuple model old) initial) := by
    let R := fun (config : Config (Atom model) _ Memory) => ∃ carried : WordTuple bank,
      config = .follow env (Generic.blocks g) 0 (encodeTuple model carried) initial ∧
        ∀ count value, ¬ g.ReturnsAfter model input count carried value
    apply Diverges.coinduct R _ ⟨old, rfl, noReturn⟩
    rintro _ ⟨carried, rfl, absentFromBank⟩
    have packet := Generic.header_eval g model input carried initial
    cases taken : g.step model input carried with
    | inl value => exact (absentFromBank 0 value (.exit taken)).elim
    | inr next =>
      rw [taken] at packet
      exact .follow_next (by decide : 0 < 1) packet
        ⟨next, rfl, fun count value run => absentFromBank (count + 1) value (.backedge taken run)⟩
  apply Diverges.fold (.cfg_follow (Generic.entry_eval g model input initial) ?_)
  apply follows
  intro count value run
  exact (Part.eq_none_iff'.mp absent) (Part.dom_iff_mem.mpr
    ⟨value, (g.returns_iff_mem_denote model input value).mp ⟨count, run⟩⟩)

variable {mapping : InputMap old new} {g : SourceWithEntry old entrySigs sigs} {targets : Checked.Phi.Targets}

theorem lowerChecked_sound (accepted : lowerChecked mapping g = some targets) :
    (∃ before, Table.lowerChecked g = some before) ∧ (lowerFunc (mapCaptures mapping g)).WellFormed ∧
    targets = (⟨[lowerFunc (mapCaptures mapping g)]⟩, Generic.lower (mapCaptures mapping g)) := by
  obtain ⟨before, checked, result⟩ := Option.bind_eq_some_iff.mp accepted
  dsimp only at result
  split at result
  · rename_i wf
    exact ⟨⟨before, checked⟩, wf, (Option.some.inj result).symm⟩
  · cases result

theorem lowerChecked_typed (accepted : lowerChecked mapping g = some targets) :
    targets.1.WellFormed ∧ targets.2.HasType (Generic.inputContext (wordSorts new))
      [Generic.packed [.value word]] := by
  obtain ⟨_, wf, rfl⟩ := lowerChecked_sound accepted
  exact ⟨by simpa [Prog.WellFormed] using wf, Generic.lower_hasType _⟩

theorem lambda_return_iff (accepted : lowerChecked mapping g = some targets) (input : WordTuple new)
    (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model input) targets.2 initial label payload final ↔
      ∃ value : Word, value ∈ g.denote model (mapping.pull input) ∧ label = 0 ∧
        payload = Generic.packResult model (out := word) value ∧ final = initial := by
  obtain ⟨_, _, rfl⟩ := lowerChecked_sound accepted
  refine (Generic.lower_eval_iff (mapCaptures mapping g) model input initial final label payload).trans ?_
  exact exists_congr fun value => and_congr
    (((mapCaptures mapping g).returns_iff_mem_denote model input value).trans
      (Iff.of_eq (congrArg (fun p => value ∈ p) (denote_mapCaptures mapping g model input)))) Iff.rfl

theorem lambda_diverges_iff (accepted : lowerChecked mapping g = some targets) (input : WordTuple new)
    (initial : Memory) :
    Diverges (instruction model) (.region (inputEnv model input) targets.2 initial) ↔
      g.denote model (mapping.pull input) = Part.none := by
  constructor
  · intro infinite
    apply Part.eq_none_iff'.mpr
    intro defined
    obtain ⟨value, present⟩ := Part.dom_iff_mem.mp defined
    have finite := (lambda_return_iff accepted input initial initial 0
      (Generic.packResult model (out := word) value)).mpr ⟨value, present, rfl, rfl, rfl⟩
    exact finite.not_diverges (instruction_deterministic model) infinite
  · intro absent
    obtain ⟨_, _, rfl⟩ := lowerChecked_sound accepted
    exact lower_diverges_of_absent (mapCaptures mapping g) input initial
      ((denote_mapCaptures mapping g model input).trans absent)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Proofs
