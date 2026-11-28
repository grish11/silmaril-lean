module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Doubling.Switching.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Immediate and two-leg exits of a switching step -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.SwitchingExample

open CategoryTheory CategoryTheory.Limits

/-- The two calls in the repeat path have distinguishable opcodes. -/
inductive Op where
  | first
  | second

instance : HasTy Op (Ty Empty) where
  src _ := .unit
  trg _ := .unit

abbrev U : Ty Empty := .unit
abbrev PairTy : Ty Empty := .product U U
abbrev Flag : Ty Empty := .coprod U U
abbrev Answer : Ty Empty := .coprod U PairTy
abbrev State : Ty Empty := .coprod Flag Flag

abbrev Obj := ofType (τ := Ty Empty) (Φ := Op)
abbrev UnitObj := Obj U
abbrev FlagObj := Obj Flag
abbrev AnswerObj := Obj Answer
abbrev StateObj := Obj State

def early : Region Op := .br 0 (.inl (.var 0))
def late : Region Op := .br 0 (.inr (.pair .unit .unit))

def request (op : Op) (k : Region Op) : Region Op := .let₁ (.op op .unit) k

theorem earlyTyped : ValueBranches [U] early [Answer] := .br rfl (.inl (.var rfl))

theorem requestTyped (op : Op) : ValueBranches [U] (request op (.br 0 .unit)) [U] :=
  .let₁ (.op .unit) (.br rfl .unit)

theorem secondExitTyped : ValueBranches [U] (request .second late) [Answer] :=
  .let₁ (.op .unit) (.br rfl (.inr (.pair .unit .unit)))

theorem twoRequestsTyped : ValueBranches [U] (request .first (request .second late)) [Answer] :=
  .let₁ (.op .unit) (.let₁ (.op .unit) (.br rfl (.inr (.pair .unit .unit))))

def outcome : Region Op := .case (.var 0) early (request .first (request .second late))

theorem outcomeTyped : ValueBranches [Flag] outcome [Answer] :=
  CfgEta.TypeCategory.caseValueBranches earlyTyped twoRequestsTyped

/-- Decode the exact answer into the two ordered, differently typed exits. -/
def unpack : Region Op := .case (.var 0) (.br 0 (.var 0)) (.br 1 (.var 0))

def orderedOutcome : Region Op := outcome.lsubst (fun _ => unpack)

noncomputable abbrev flagLeft : UnitObj ⟶ FlagObj := (sumCofan U U).inl
noncomputable abbrev flagRight : UnitObj ⟶ FlagObj := (sumCofan U U).inr
noncomputable abbrev stateLeft : FlagObj ⟶ StateObj := (sumCofan Flag Flag).inl
noncomputable abbrev stateRight : FlagObj ⟶ StateObj := (sumCofan Flag Flag).inr

/-- The left row exits immediately or makes the first request and switches. -/
noncomputable def left : FlagObj ⟶ AnswerObj ⨿ FlagObj :=
  (sumIso U U).hom ≫ coprod.desc (ofRegion earlyTyped ≫ coprod.inl)
    (ofRegion (requestTyped .first) ≫ flagLeft ≫ coprod.inr)

/-- The right row makes the second request. It can exit or switch back. -/
noncomputable def right : FlagObj ⟶ AnswerObj ⨿ FlagObj :=
  (sumIso U U).hom ≫ coprod.desc (ofRegion secondExitTyped ≫ coprod.inl)
    (ofRegion (requestTyped .second) ≫ flagRight ≫ coprod.inr)

noncomputable def step : StateObj ⟶ AnswerObj ⨿ StateObj :=
  blockCopair (left ≫ coprod.map (𝟙 AnswerObj) stateRight)
    (right ≫ coprod.map (𝟙 AnswerObj) stateLeft)

noncomputable abbrev doubled : StateObj ⟶ AnswerObj ⨿ StateObj :=
  step ≫ coprod.desc coprod.inl step

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.SwitchingExample
