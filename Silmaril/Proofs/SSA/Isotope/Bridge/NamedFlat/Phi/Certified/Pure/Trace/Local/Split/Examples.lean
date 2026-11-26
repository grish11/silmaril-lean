module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Comparison.Thms

/-! A visible loop swaps two live values on the split edge. The admitted
entry fixtures also exercise a second split after extending the record. -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split.Examples

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block Pending assign br ret)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan Checked)
open Silmaril.Elgot.ITree (Tree Trace TraceLE HasTrace vis vis_bind resume resume_body
  hasTrace_vis_exchange_iff hasTrace_vis_request)
open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive Transfer region)
open Silmaril.Isotope.Semantics (encodeValue)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree Compatible)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open CategoryTheory (Discrete)
open NamedFlat.Entry.Record (Input reindex reindex_comp)

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private abbrev Reg := ULift.{1} Nat
private abbrev Key := ULift.{1} Nat
private abbrev Atom := ULift.{1} Nat
private abbrev SortName := ULift.{1} Unit
private instance : AtomValues SortName := ⟨fun _ => Atom⟩
private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))
private abbrev Store := Reg → Value Runtime

private inductive Opcode
  | tick
  deriving DecidableEq

private inductive Event : Type → Type
  | tick (left right : Nat) : Event (Nat ⊕ Unit)

private def atom (n : Nat) : Value Runtime := .atom ⟨⟨()⟩, ⟨n⟩⟩
private abbrev num : Ty SortName := .base ⟨()⟩

private instance : HasTy Opcode (Ty SortName) where
  src _ := .product num num
  trg _ := .coprod num .unit

private def instr : Primitive Event Opcode Runtime
  | .tick, .pair (.atom left) (.atom right) => vis (.tick left.2.down right.2.down) fun
      | .inl result => pure (.inl (atom result))
      | .inr _ => pure (.inr .unit)
  | _, _ => Silmaril.Elgot.ITree.diverge

private def seedX : Reg := ⟨0⟩
private def seedY : Reg := ⟨1⟩
private def x : Reg := ⟨2⟩
private def y : Reg := ⟨3⟩
private def doneName : Reg := ⟨4⟩
private def backName : Reg := ⟨5⟩
private def header : Key := ⟨17⟩

private def tickBody (next : Key) : CFG.Body Reg (Option Key) Opcode :=
  .term (.case (.app .tick (.pair (.var x) (.var y)))
    doneName (ret (.var doneName)) backName (br next))

private def headerBlock : Block Reg Key Opcode :=
  ⟨[⟨x, [(none, .var seedX), (some header, .var y)]⟩,
    ⟨y, [(none, .var seedY), (some header, .var x)]⟩], tickBody header⟩

private def source : Graph Reg Key Opcode := ⟨.term (br header), [(header, headerBlock)]⟩

private def plan : Plan Reg Reg Key (Option Key) where
  register := ((Equiv.swap seedX ⟨8⟩).trans (Equiv.swap seedY ⟨9⟩)).trans
    ((Equiv.swap x ⟨6⟩).trans (Equiv.swap y ⟨7⟩))
  label := ⟨some, fun _ _ h => Option.some.inj h⟩
  header := header
  forward := none
  fresh := fun _ => Option.some_ne_none _

private def target : Graph Reg (Option Key) Opcode := plan.rewrite source

private theorem checked : Checked plan source target := plan.check_sound (by decide)

-- Reusing the pre-split key at the header is rejected.
private def stale : Graph Reg (Option Key) Opcode :=
  ⟨target.entry, target.blocks.map fun (key, block) =>
    (key, ⟨block.rows.map fun row => ⟨row.dst,
      row.incoming.map fun (pred, value) =>
        (if pred = some plan.forward then some (plan.label header) else pred, value)⟩, block.body⟩)⟩

example : plan.check source stale = false := by decide

private def captures (i : Fin 4) : Option Reg := some ⟨i.val⟩
private def profile : BoundCtx (Ty SortName) 4 := .snoc (.snoc (.snoc (.snoc .nil num) num) num) num
private def exits : Fin 1 → Ty SortName := fun _ => num
private def pairPacket : Ty SortName := .product num (.product num .unit)
private def originalProfile (_ : Fin (blockCount source)) : Ty SortName :=
  .product pairPacket pairPacket

private abbrev State := Pending Reg Key (Value Runtime)

private def entryCaptures : Captures Reg profile where
  names := captures
  distinct _ _ eq := Fin.ext (congrArg (fun name : Option Reg => (name.getD ⟨0⟩).down) eq)
  privateUnit i eq := by nomatch eq

private def supplied : Ty.denote (AtomValues.carrier (κ := SortName))
    (Region.packedInputType profile.toList) :=
  ((((PUnit.unit, ⟨0⟩), ⟨0⟩), ⟨5⟩), ⟨2⟩)

private def originalStore : Store := entryCaptures.store supplied

private def writePair (store : Store) (a b : Nat) : Store := upd (upd store x (atom a)) y (atom b)

private def response (next : Key) (store : Store) : Nat ⊕ Unit → State
  | .inl result => (.returned (atom result), upd store doneName (atom result))
  | .inr _ => (.jump (some header) next, upd store backName .unit)

private theorem tick_step_of (graph : Graph Reg Key Opcode) (next : Key)
    (pred : Option Key) (store : Store) (a b : Nat) {block : Block Reg Key Opcode}
    (found : graph.blocks.lookup header = some block) (body : block.body = tickBody next)
    (assigned : assign (treeModel instr) pred store block.rows store = writePair store a b) :
    stepTree instr graph (.jump pred header, store) =
      vis (.tick a b) (fun reply => pure (.inr (response next (writePair store a b) reply))) := by
  rw [step_jump _ _ _ _ _ found, assigned, body]
  simp [CFG.Cyclic.Phi.execute, tickBody, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
    treeModel, instr, writePair, upd, x, y, atom, ← bind_pure_comp, bind_assoc, vis_bind]
  funext reply
  cases reply <;> simp [response, br, ret, CFG.Term.exec, Val.eval, upd, atom]

private theorem tick_step (pred : Option Key) (store : Store) (a b : Nat)
    (assigned : assign (treeModel instr) pred store headerBlock.rows store = writePair store a b) :
    stepTree instr source (.jump pred header, store) =
      vis (.tick a b) (fun reply => pure (.inr (response header (writePair store a b) reply))) :=
  tick_step_of source header pred store a b rfl rfl assigned

private theorem resume_transfer {source : Graph Reg Key Opcode} (p : State) :
    resume (stepTree instr source) (pure (.inr p)) =
      resume (stepTree instr source) (stepTree instr source p) := by
  rw [resume_body]
  simp [resume]

private def swappedTrace : Trace Event (Transfer Runtime) :=
  .exchange (.tick 2 5) (.inr ()) (.request (.tick 5 2))

private theorem source_swap :
    HasTrace (sourceObservation instr source originalStore) swappedTrace := by
  have entry : entryTree instr source originalStore =
      pure (.inr (.jump none header, originalStore)) := by
    simp [entryTree, source, CFG.Cyclic.Phi.execute, CFG.Body.exec, CFG.Term.exec, br]
  rw [sourceObservation_eq_resume, entry, resume_transfer, tick_step none originalStore 2 5 rfl,
    swappedTrace]
  simp only [resume, vis_bind, hasTrace_vis_exchange_iff, pure_bind, Sum.elim_inr]
  rw [← resume_body]
  change HasTrace (resume (stepTree instr source)
    (stepTree instr source (.jump (some header) header,
      upd (writePair originalStore 2 5) backName .unit))) _
  rw [tick_step (some header) _ 5 2 rfl]
  simp only [resume, vis_bind]
  exact hasTrace_vis_request _ _

private def init : Key := ⟨16⟩
private def latch : Key := ⟨18⟩

private def jumpBlock (target : Key) : Block Reg Key Opcode := ⟨[], .term (br target)⟩

private def distinctHeader : Block Reg Key Opcode :=
  ⟨[⟨x, [(some latch, .var y), (some init, .var seedX)]⟩,
    ⟨y, [(some latch, .var x), (some init, .var seedY)]⟩], tickBody latch⟩

-- The latch precedes the unaffected predecessor in table order, so the
-- split must keep its original position in each incoming row.
private def distinctSource : Graph Reg Key Opcode :=
  ⟨.term (br init), [(latch, jumpBlock header), (header, distinctHeader), (init, jumpBlock header)]⟩

private def distinctPlan : Plan Reg Reg Key (Option Key) := { plan with predecessor := some latch }
private def distinctTarget : Graph Reg (Option Key) Opcode := distinctPlan.rewrite distinctSource
private theorem distinctChecked : Checked distinctPlan distinctSource distinctTarget :=
  distinctPlan.check_sound (by decide)

example : distinctTarget.predecessors (plan.label header) =
    [some plan.forward, some (plan.label init)] := by decide

example :
    (distinctTarget.blocks.lookup (plan.label header)).map (fun block =>
      CFG.Cyclic.Phi.arguments (some (plan.label init)) block.rows) =
      some [.var (plan.register seedX), .var (plan.register seedY)] := by decide

private def parallel : Graph Reg Key Opcode :=
  { distinctSource with blocks :=
      [(latch, ⟨[], .term (.case (.app .tick (.pair (.var x) (.var y)))
        ⟨20⟩ (br header) ⟨21⟩ (br header))⟩), (header, distinctHeader), (init, jumpBlock header)] }

example : distinctPlan.hasEdge parallel = true ∧
    distinctPlan.check parallel (distinctPlan.rewrite parallel) = false := by decide

-- The unnamed entry can also be split, including its incoming φ column.
private def entryPlan : Plan Reg Reg Key (Option Key) := { plan with predecessor := none }

example : sourceObservation instr source originalStore =
    sourceObservation instr (entryPlan.rewrite source) (entryPlan.renameStore originalStore) :=
  source_eq (entryPlan.check_sound (by decide)) instr originalStore

private def blockProfile (headerIndex : Nat) (index : Nat) : Ty SortName :=
  .product (if index = headerIndex then pairPacket else .unit) (.product num (.product num pairPacket))

private def distinctArrivals : CFG.Cyclic.Phi.GlobalSSA.Certificate Reg Key :=
  [(latch, [x, y]), (header, []), (init, [seedX, seedY])]

private def distinctAdmittedLeft := (Certified.admit distinctSource [seedX, seedY]
  distinctArrivals captures profile (fun i => blockProfile 1 i.val) exits).get (by decide)

private def distinctClosedLeft := (close distinctAdmittedLeft).get (by decide)

private theorem straight_step (pred : Option Key) (target next : Key) (store : Store)
    (found : distinctSource.blocks.lookup target = some (jumpBlock next)) :
    stepTree instr distinctSource (.jump pred target, store) =
      pure (.inr (.jump (some target) next, store)) := by
  rw [step_jump _ _ _ _ _ found]
  simp [jumpBlock, assign, CFG.Cyclic.Phi.execute, CFG.Body.exec, CFG.Term.exec, br]

private theorem distinct_source_swap :
    HasTrace (sourceObservation instr distinctSource originalStore) swappedTrace := by
  have entry : entryTree instr distinctSource originalStore =
      pure (.inr (.jump none init, originalStore)) := by
    simp [entryTree, distinctSource, CFG.Cyclic.Phi.execute, CFG.Body.exec, CFG.Term.exec, br]
  rw [sourceObservation_eq_resume, entry, resume_transfer, straight_step none init header _ rfl,
    resume_transfer, tick_step_of distinctSource latch (some init) originalStore 2 5
      (block := distinctHeader) rfl rfl rfl, swappedTrace]
  simp only [resume, vis_bind, hasTrace_vis_exchange_iff, pure_bind, Sum.elim_inr]
  rw [← resume_body]
  change HasTrace (resume (stepTree instr distinctSource)
    (stepTree instr distinctSource (.jump (some header) latch,
      upd (writePair originalStore 2 5) backName .unit))) _
  rw [straight_step (some header) latch header _ rfl, resume_transfer,
    tick_step_of distinctSource latch (some latch) _ 5 2 (block := distinctHeader) rfl rfl rfl]
  simp only [resume, vis_bind]
  exact hasTrace_vis_request _ _

private def seedCaptures (i : Fin 2) : Option Reg := some ⟨i.val⟩
private def seedTypes : BoundCtx (Ty SortName) 2 := .snoc (.snoc .nil num) num
private def arrivals : CFG.Cyclic.Phi.GlobalSSA.Certificate Reg Key := [(header, [])]

private def seedAdmission := (Certified.admit source [seedX, seedY] arrivals
  seedCaptures seedTypes originalProfile exits).get (by decide)

private def seedClosed := (close seedAdmission).get (by decide)

-- Plain renaming cannot supply the version-zero copies of x and y now read
-- by the generated lexical entry's packet construction.
example : (NamedFlat.compile (CFG.Cyclic.Phi.lower target) [none]
    (fun i : Fin 2 => (seedCaptures i).map plan.register)).isNone := by decide

-- The forwarding block also needs a certified arrival claim for those reads.
example : CFG.Cyclic.Phi.GlobalSSA.check target ([seedX, seedY].map plan.register)
    [(plan.label header, [])] = false := by decide

private def seedCandidate := (profileCandidate plan source seedCaptures originalProfile).get (by decide)

private theorem seedGeneration : (generate plan seedAdmission arrivals).isSome := by
  rw [generate_eq_of_profile seedAdmission (candidate := seedCandidate)
    (by decide) (by decide) (by decide) rfl]
  decide

private def generated := (generate plan seedAdmission arrivals).get seedGeneration

example : generated.extra =
    [(some (plan.register y), num), (some (plan.register x), num)] := by decide

private theorem generated_packed_swap :
    HasTrace (packedObservation generated.closed instr (plan.renameStore originalStore)) swappedTrace := by
  rw [← generated.packed_eq seedClosed instr originalStore, packedObservation_eq_sourceObservation]
  exact source_swap

-- The distinct latch already exposes both variables in the old support.
private def distinctCandidate := (profileCandidate distinctPlan distinctSource captures
  (fun i => blockProfile 1 i.val)).get (by decide)

private theorem distinctGeneration : (generate distinctPlan distinctAdmittedLeft distinctArrivals).isSome := by
  rw [generate_eq_of_profile distinctAdmittedLeft (candidate := distinctCandidate)
    (by decide) (by decide) (by decide) rfl]
  decide

private def distinctGenerated := (generate distinctPlan distinctAdmittedLeft distinctArrivals).get distinctGeneration

example : distinctGenerated.extra = [] := by decide

private theorem distinct_packed_swap :
    HasTrace (packedObservation distinctGenerated.closed instr (distinctPlan.renameStore originalStore)) swappedTrace := by
  rw [← distinctGenerated.packed_eq distinctClosedLeft instr originalStore, packedObservation_eq_sourceObservation]
  exact distinct_source_swap

private instance : HasEff Opcode Bool := ⟨fun _ => true⟩

private def typed : Silmaril.Isotope.Semantics.InstructionModel
    (Ty.denote (AtomValues.carrier (κ := SortName))) Opcode (ModelTree Event) where
  eval
    | .tick, (left, right) => vis (.tick left.down right.down) fun
      | .inl result => pure (.inl ⟨result⟩)
      | .inr _ => pure (.inr PUnit.unit)

private theorem compatible : Compatible (κ' := SortName) typed instr := by
  intro op arg
  cases op
  obtain ⟨left, right⟩ := arg
  change instr .tick (.pair (atom left.down) (atom right.down)) =
    (typed.eval .tick (left, right) >>= fun reply =>
      pure (Silmaril.Isotope.Semantics.encodeValue _ (.coprod num .unit) reply))
  simp only [instr, atom, typed, vis_bind]
  congr 1
  funext reply
  cases reply <;> erw [pure_bind] <;> rfl

private def signature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Opcode

private def model : Model (κ := SortName) Event signature.Instr where
  instructions :=
    { denote := typed.eval
      denotePure := fun _ hf => Bool.noConfusion hf
      denote_pure := fun _ hf => Bool.noConfusion hf }
  raw := instr
  compatible := compatible

private def entryOriginal : Admitted signature entryCaptures Key exits :=
  .ofAdmission distinctAdmittedLeft

private def entrySplit : Admitted signature (entryCaptures.rename distinctPlan.register) (Option Key) exits :=
  .ofGenerated distinctPlan distinctGenerated (by decide)

-- The translated table observes the same reply-driven swap at the same
-- supplied record, even after the register and block relabeling.
theorem supplied_split_swap : HasTrace (entrySplit.toSSA.observe model supplied) swappedTrace := by
  rw [entrySplit.observe_toSSA,
    ← split_observe_eq distinctPlan entryOriginal entrySplit distinctGenerated.checked model supplied]
  exact distinct_source_swap

theorem supplied_split_packed_swap (ambient : Env Runtime) :
    HasTrace (region model.raw (extend ambient (encodeValue _ _ supplied))
      (EntryInstitution.packSentence (toFlat (entryOriginal, entrySplit))).right.code) swappedTrace := by
  change HasTrace (region model.raw (extend ambient (encodeValue _ _ supplied))
    (Program.ofCFGEntry entrySplit.toSSA.table.typed).code) _
  rw [← entrySplit.observe_toFlat model supplied ambient, ← entrySplit.observe_toSSA]
  exact supplied_split_swap

private theorem entryComparisons :
    EntryInstitution.Satisfies Event model (toFlat (entryOriginal, entrySplit)) ∧
      EntryInstitution.Satisfies Event model (toFlat (entrySplit, entryOriginal)) :=
  split_satisfies distinctPlan entryOriginal entrySplit distinctGenerated.checked model

theorem supplied_split_packing :
    (PackedInstitution.room Event signature (Region.packedInputType profile.toList)).Sat
      (Discrete.mk model) (EntryInstitution.packSentence (toFlat (entryOriginal, entrySplit))) ∧
    (PackedInstitution.room Event signature (Region.packedInputType profile.toList)).Sat
      (Discrete.mk model) (EntryInstitution.packSentence (toFlat (entrySplit, entryOriginal))) :=
  ⟨(EntryInstitution.packing_satisfaction Event model _).mpr entryComparisons.1,
    (EntryInstitution.packing_satisfaction Event model _).mpr entryComparisons.2⟩

private def seedLayout : Captures Reg seedTypes where
  names := seedCaptures
  distinct _ _ eq := Fin.ext (congrArg (fun name : Option Reg => (name.getD ⟨0⟩).down) eq)
  privateUnit _ eq := by nomatch eq

private def seedOriginal : Admitted signature seedLayout Key exits :=
  .ofAdmission seedAdmission

private theorem extendedLayout : ExtendedLayout plan seedLayout generated.extra := by decide

private def seedSplit : Admitted signature extendedLayout.captures (Option Key) exits :=
  seedOriginal.ofExtended plan generated extendedLayout

private def seedRecord : Input seedTypes := ((PUnit.unit, ⟨5⟩), ⟨2⟩)

-- The old record has only 2 and 5. The extra fields are supplied
-- independently, at values different from either seed or swapped operand.
private def extendedRecord : Input (extendedTypes seedTypes generated.extra) :=
  ((((PUnit.unit, ⟨89⟩), ⟨97⟩), ⟨5⟩), ⟨2⟩)

private theorem extended_retains_seed :
    retainedRecord seedTypes generated.extra extendedRecord = seedRecord := rfl

theorem appended_split_satisfies (ambient : Env Runtime) :
    (TraceLE (seedOriginal.toSSA.observe model seedRecord) (seedSplit.toSSA.observe model extendedRecord) ∧
      TraceLE (seedSplit.toSSA.observe model extendedRecord) (seedOriginal.toSSA.observe model seedRecord)) ∧
    (TraceLE (seedOriginal.observePacked model seedRecord ambient) (seedSplit.observePacked model extendedRecord ambient) ∧
      TraceLE (seedSplit.observePacked model extendedRecord ambient) (seedOriginal.observePacked model seedRecord ambient)) :=
  split_related_satisfies seedOriginal plan generated extendedLayout model
    seedRecord extendedRecord extended_retains_seed ambient

private theorem seed_packed_swap (ambient : Env Runtime) :
    HasTrace (seedOriginal.observePacked model seedRecord ambient) swappedTrace := by
  have shared := seedOriginal.observe_toFlat_of_capture model seedRecord ambient originalStore
    (fun i => Fin.cases rfl (Fin.cases rfl (fun j => j.elim0)) i)
  change HasTrace (region model.raw (extend ambient (encodeValue _ _ seedRecord))
    (Program.ofCFGEntry seedOriginal.toSSA.table.typed).code) _
  rw [← shared]
  exact source_swap

theorem appended_split_swap (ambient : Env Runtime) :
    HasTrace (seedSplit.observePacked model extendedRecord ambient) swappedTrace := by
  unfold seedSplit
  rw [← split_packed_reindex seedOriginal plan generated extendedLayout model extendedRecord ambient,
    extended_retains_seed]
  exact seed_packed_swap ambient

/-! ## The generated backedge split followed by an entry-edge split -/

private def secondPlan : Plan Reg Reg (Option Key) (Option (Option Key)) where
  register := Equiv.refl _
  label := ⟨some, fun _ _ h => Option.some.inj h⟩
  header := plan.label header
  predecessor := none
  forward := none
  fresh := fun _ => Option.some_ne_none _

private def transportedArrivals := splitCertificate plan source arrivals

private theorem transportedArrivals_check :
    CFG.Cyclic.Phi.GlobalSSA.check seedSplit.source seedSplit.inputs transportedArrivals = true :=
  splitCertificate_check (plan := plan) (certificate := arrivals)
    (by decide) generated.checked.edge generated.checked.targetNormalized

private def secondCandidate :=
  (profileCandidate secondPlan seedSplit.source extendedLayout.captures.names seedSplit.internal).get
    (by decide)

private theorem secondGeneration :
    (generate secondPlan seedSplit.admission transportedArrivals).isSome := by
  rw [generate_eq_of_profile seedSplit.admission (candidate := secondCandidate)
    transportedArrivals_check (by decide) (by decide) rfl]
  decide

private def generatedSecond := (generate secondPlan seedSplit.admission transportedArrivals).get secondGeneration

private theorem secondLayout : ExtendedLayout secondPlan extendedLayout.captures generatedSecond.extra := by decide

private def finalSplit : Admitted signature secondLayout.captures (Option (Option Key)) exits :=
  seedSplit.ofExtended secondPlan generatedSecond secondLayout

-- The first split adds two fields. The second keeps all four fields and
-- checks the new entry forwarder at that context.
example : generatedSecond.extra = [] := by decide

private def finalRecord : Input (extendedTypes (extendedTypes seedTypes generated.extra) generatedSecond.extra) :=
  extendedRecord

private def firstComparison : EntryComparison Event seedOriginal seedSplit :=
  .ofSplit seedOriginal plan generated extendedLayout

private def secondComparison : EntryComparison Event seedSplit finalSplit :=
  .ofSplit seedSplit secondPlan generatedSecond secondLayout

private def composedComparison : EntryComparison Event seedOriginal finalSplit :=
  firstComparison.comp secondComparison

private theorem composed_retains_seed : reindex composedComparison.slots finalRecord = seedRecord :=
  (reindex_comp firstComparison.slots secondComparison.slots finalRecord).trans extended_retains_seed

theorem two_splits_visible_order (ambient : Env Runtime) :
    HasTrace (finalSplit.toSSA.observe model finalRecord) swappedTrace ∧
    HasTrace (finalSplit.observePacked model finalRecord ambient) swappedTrace := by
  apply (composedComparison.satisfies_iff model finalRecord ambient
    (fun tree => HasTrace tree swappedTrace) (fun tree => HasTrace tree swappedTrace)).mpr
  rw [composed_retains_seed]
  exact ⟨(NamedFlat.Entry.SSA.observe_tree model seedOriginal.toSSA seedRecord (fun _ => .unit)).symm ▸
    seed_packed_swap (fun _ => .unit), seed_packed_swap ambient⟩

theorem two_splits_trace_order (ambient : Env Runtime) :
    let beforeNamed := seedOriginal.toSSA.observe model seedRecord
    let afterNamed := finalSplit.toSSA.observe model finalRecord
    let beforePacked := seedOriginal.observePacked model seedRecord ambient
    let afterPacked := finalSplit.observePacked model finalRecord ambient
    (TraceLE beforeNamed afterNamed ∧ TraceLE beforePacked afterPacked) ∧
      (TraceLE afterNamed beforeNamed ∧ TraceLE afterPacked beforePacked) := by
  dsimp only
  constructor
  · apply (composedComparison.satisfies_iff model finalRecord ambient
      (TraceLE (seedOriginal.toSSA.observe model seedRecord))
      (TraceLE (seedOriginal.observePacked model seedRecord ambient))).mpr
    rw [composed_retains_seed]
    exact ⟨TraceLE.refl _, TraceLE.refl _⟩
  · apply (composedComparison.satisfies_iff model finalRecord ambient
      (fun t => TraceLE t (seedOriginal.toSSA.observe model seedRecord))
      (fun t => TraceLE t (seedOriginal.observePacked model seedRecord ambient))).mpr
    rw [composed_retains_seed]
    exact ⟨TraceLE.refl _, TraceLE.refl _⟩

private def entryCandidate := (profileCandidate entryPlan source seedCaptures originalProfile).get (by decide)

example : (generate entryPlan seedAdmission arrivals).isSome := by
  rw [generate_eq_of_profile seedAdmission (candidate := entryCandidate)
    (by decide) (by decide) (by decide) rfl]
  decide

-- Admission stores the SSA proof, so an unrelated table can still be passed.
-- The diagnostic identifies the table failure before checking packet types.
example : ((generateDetailed plan seedAdmission []).map (fun _ => ())) = .error .arrivalClaims := rfl

-- An old, unused capture may carry a type that cannot type a newly live
-- version-zero read. Generation keeps that interface and rejects it.
private def incompatibleTypes : BoundCtx (Ty SortName) 4 :=
  .ofFin (fun i => if i.val = 2 then .unit else num)

private def incompatibleAdmission := (Certified.admit source [seedX, seedY] arrivals
  captures incompatibleTypes originalProfile exits).get (by decide)

example : ((generateDetailed plan incompatibleAdmission arrivals).map (fun _ => ())) =
    .error (.oldCaptureTypes [2]) := rfl

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split.Examples
