module

public import Silmaril.SSA.PEG.Rules.Defs
public import Silmaril.SSA.Peggy.EPEG.Saturation.Defs
public import Silmaril.SSA.Peggy.EPEG.Selection.Defs
public import Silmaril.SSA.Peggy.EPEG.Selection.Legality.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Fin

/-! # One-loop PEG self-feedback elimination -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Optimizer.Cyclic

open PEG
open RVSDG (Tuple)
open EPEG (Classes Selection)
open EPEG.Selection (FeedbackRank)
open EPEG.Saturation (Obligation)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n : Nat}

def supported {ins : List (Ty Data)} {out : Ty Data} :
    Label P params (Fin 1) ins out → Bool
  | .param _ | .op _ | .phi | .theta _ => true
  | .eval _ | .pass _ => false

def demandRank (phase : Fin n → Nat) : DemandRank n 1 :=
  [.counter 0, .phase phase]

/-- Independent certificates for the structural profile and native demands. -/
structure Admission (g : Graph P params results n 1) where
  feedback : FeedbackRank g
  noParent : g.forest.parent 0 = none
  labels : ∀ i, supported (g.node i).label = true
  demands : (demandRank feedback.rank).check g = true

abbrev Admission.phase {g : Graph P params results n 1} (admitted : Admission g) : Fin n → Nat :=
  admitted.feedback.rank

/-- Infer a structural rank, then check the loop profile and the native demands. -/
def admit (g : Graph P params results n 1) : Option (Admission g) := do
  let some feedback := FeedbackRank.infer g | none
  if ok : g.forest.parent 0 = none ∧ (∀ i, supported (g.node i).label = true) ∧
      (demandRank feedback.rank).check g = true then
    some ⟨feedback, ok.1, ok.2.1, ok.2.2⟩
  else none

variable {g : Graph P params results (n + 1) 1} {site : Fin (n + 1)}

/-- The actual row is a θ with literal self feedback and a distinct,
zero-input initializer. A leaf initializer needs no stream-definedness premise. -/
structure Match (g : Graph P params results (n + 1) 1) (site : Fin (n + 1)) where
  loop : Fin 1
  init : Ref g.sort (g.sort site)
  feedback : Ref g.sort (g.sort site)
  self : feedback.id = site
  distinct : init.id ≠ site
  leaf : (g.node init.id).inputs = []
  shape : Rules.HasNode (Ref.ofId g.sort site) (.theta loop) (.cons init (.cons feedback .nil))

def matchRow (g : Graph P params results (n + 1) 1) (site : Fin (n + 1)) :
    (row : Node P params (Fin 1) g.sort (g.sort site)) → g.node site = row → Option (Match g site)
  | ⟨_, .theta loop, .cons init (.cons feedback .nil)⟩, bound =>
    if ok : feedback.id = site ∧ init.id ≠ site ∧ (g.node init.id).inputs = [] then
      some ⟨loop, init, feedback, ok.1, ok.2.1, ok.2.2, heq_of_eq bound⟩
    else none
  | _, _ => none

def matchAt (g : Graph P params results (n + 1) 1) (site : Fin (n + 1)) :
    Option (Match g site) :=
  matchRow g site (g.node site) rfl

namespace Match

def rule (found : Match g site) : EPEG.GuardedEquation g :=
  ⟨[⟨found.feedback.id, site, congrArg g.sort found.self⟩],
    ⟨site, found.init.id, found.init.typed.symm⟩⟩

def obligation (found : Match g site) : Obligation g := .guarded found.rule

def classes (found : Match g site) : Classes (n + 1) :=
  EPEG.Saturation.saturate [found.obligation] Classes.discrete

/-- Find the remaining address of a vertex different from the deleted one. -/
def survivor (hole v : Fin (n + 1)) (distinct : v ≠ hole) :
    {i : Fin n // hole.succAbove i = v} :=
  Fin.succAboveCases hole (fun h => (h rfl).elim) (fun i _ => ⟨i, rfl⟩) v distinct

/-- Redirect the eliminated row to the initializer and compact all other addresses. -/
def redirect (found : Match g site) {out : Ty Data} (ref : Ref g.sort out) :
    Ref (g.sort ∘ site.succAbove) out :=
  if same : ref.id = site then
    let i := survivor site found.init.id found.distinct
    ⟨i.val, (congrArg g.sort i.property).trans
      (found.init.typed.trans ((congrArg g.sort same.symm).trans ref.typed))⟩
  else
    let i := survivor site ref.id same
    ⟨i.val, (congrArg g.sort i.property).trans ref.typed⟩

def extract (found : Match g site) : Graph P params results n 1 where
  forest := g.forest
  sort := g.sort ∘ site.succAbove
  node i :=
    let old := g.node (site.succAbove i)
    Node.ofLabel old.label (old.args.map fun _ => found.redirect)
  roots := g.roots.map fun _ => found.redirect

def selectionWithRank (found : Match g site) (rank : DemandRank n 1) : Selection g found.extract :=
  ⟨fun i => Ref.ofId g.sort (site.succAbove i), rank⟩

/-- Generate both sides of the certificate from the same retained source row.
Only the operand references are redirected. -/
def rowsWithRank (found : Match g site) (rank : DemandRank n 1) (i : Fin n) :
    Selection.Row (found.selectionWithRank rank) i :=
  let old := g.node (site.succAbove i)
  ⟨old.inputs, old.label, old.args, old.args.map (fun _ => found.redirect), HEq.rfl, rfl⟩

structure Replay (found : Match g site) (rank : DemandRank n 1) : Type where
  boundary : (found.selectionWithRank rank).check found.classes = true
  edges : Selection.checkRows (found.rowsWithRank rank) found.classes = true
  feedback : FeedbackRank found.extract

/-- Use a checked structural rank when the target has already been
admitted. Root classes, ordered wiring and semantic demands are checked
separately against the actual compacted graph. -/
def replayWithFeedback (found : Match g site) (rank : DemandRank n 1)
    (feedback : FeedbackRank found.extract) : Option (found.Replay rank) :=
  if ok : (found.selectionWithRank rank).check found.classes = true ∧
      Selection.checkRows (found.rowsWithRank rank) found.classes = true then
    some ⟨ok.1, ok.2, feedback⟩
  else none

/-- Check the compacted selection for actual feedback edges on cycles,
then replay its wiring receipt with the caller's native demand rank. -/
def replay (found : Match g site) (rank : DemandRank n 1) : Option (found.Replay rank) := do
  let some feedback := FeedbackRank.infer found.extract | none
  found.replayWithFeedback rank feedback

def selection (found : Match g site) (phase : Fin n → Nat) : Selection g found.extract :=
  found.selectionWithRank (demandRank phase)

def rows (found : Match g site) (phase : Fin n → Nat) (i : Fin n) :
    Selection.Row (found.selection phase) i :=
  found.rowsWithRank (demandRank phase) i

end Match

structure Result (g : Graph P params results (n + 1) 1) where
  source : Admission g
  site : Fin (n + 1)
  matched : Match g site
  target : Admission matched.extract
  boundary : (matched.selection target.phase).check matched.classes = true
  edges : Selection.checkRows (matched.rows target.phase) matched.classes = true

def trySite (g : Graph P params results (n + 1) 1) (source : Admission g)
    (site : Fin (n + 1)) : Option (Result g) := do
  let found ← matchAt g site
  let target ← admit found.extract
  let replay ← found.replayWithFeedback (demandRank target.phase) target.feedback
  return ⟨source, site, found, target, replay.boundary, replay.edges⟩

/-- Scan at most one pass over the source addresses. Return the first
candidate passing all the independent checks. -/
def optimize (g : Graph P params results (n + 1) 1) : Option (Result g) := do
  let source ← admit g
  (List.finRange (n + 1)).findSome? (trySite g source)

end Silmaril.SSA.Peggy.Optimizer.Cyclic
