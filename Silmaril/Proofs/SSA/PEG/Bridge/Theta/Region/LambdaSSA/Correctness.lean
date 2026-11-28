module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Schedule.Thms
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Thms
import Silmaril.SSA.PEG.Bridge.RVSDG.Thms
import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Proofs

open RVSDG (Port Tuple)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)
open RVSDG.LambdaSSA.Theta
open Isotope (Value)
open Isotope.LambdaSSA (Tm Region Ren)
open Isotope.LambdaSSA.Semantics (Env extend)
open Simple.Revert.While.Region (Certificate)
open Isotope.LambdaSSA.Semantics.Region (Eval)

universe u

variable {Data : Type} {P : InstructionSet.{0,0} Data} {σ : Type u}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried carried n 1} {slot : Port carried result} {allowInvariant : Bool}
variable (b : Bundle g slot allowInvariant) (m : TotalModel P)
variable (input : Tuple m.toPEG.Value carried)

private theorem tuple_ext {F : Ty Data → Type} {ts : List (Ty Data)} {xs ys : Tuple F ts}
    (pointwise : ∀ t (p : Port ts t), xs.get p = ys.get p) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys =>
      have head : x = y := pointwise _ .head
      have tail : xs = ys := ih (fun t p => pointwise t (.tail p))
      rw [head, tail]

private theorem read_packet (m : TotalModel P) {ts : List (Ty Data)}
    (layout : Schedule.Layout P ts) (env : Env (Atom m)) (values : Tuple m.toPEG.Value ts)
    (state : σ) (reads : layout.Evaluates m env values state) :
    Isotope.LambdaSSA.Semantics.Tm.Eval (instruction m) env (Schedule.tupleTerm layout (Simple.ports ts))
      state (pack m values) state := by
  have packed : (Simple.ports ts).map (fun _ p => values.get p) = values := by
    apply tuple_ext
    intro t p
    rw [Simple.get_map, Simple.ports_get]
  rw [← packed]
  exact Schedule.tupleTerm_eval m layout env values state reads (Simple.ports ts)

private theorem route_hasType {source : Graph P carried [result] n 1}
    (cert : Certificate source allowInvariant) {Γ : List (Code Data)}
    (layout : Schedule.Layout P (.bool :: carried)) (typed : layout.Typed Γ) :
    (route cert layout).HasType Γ [Packet carried, Packet carried] := by
  let old : Schedule.Layout P carried := fun p => layout.shift (.tail p)
  have oldTyped : old.Typed (.unit :: Γ) :=
    fun _ p => (typed _ (.tail p)).rename (Ren.wk _ _)
  refine .case (.op (.pair (typed _ .head) .unit))
    (.br rfl (Schedule.tupleTerm_hasType old oldTyped (Simple.ports carried))) ?_
  exact Schedule.emit_hasType cert.update old _ oldTyped fun _ next nextTyped =>
    .br rfl (Schedule.tupleTerm_hasType next nextTyped (Simple.ports carried))

theorem lower_hasType : (lower b).HasType [Packet carried] [Packet carried] := by
  refine .cfg (fun _ => Packet carried) (.br rfl (.var rfl)) fun _ => ?_
  exact Schedule.emit_hasType b.scalar.guard _ _ (fun _ p => Schedule.field_hasType p (.var rfl))
    (fun _ layout typed => route_hasType b.scalar layout typed)

private theorem route_eval {source : Graph P carried [result] n 1}
    (cert : Certificate source allowInvariant) (m : TotalModel P)
    (layout : Schedule.Layout P (.bool :: carried)) (env : Env (Atom m))
    (guard : ULift Bool) (old next : Tuple m.toPEG.Value carried) (state : σ)
    (reads : layout.Evaluates m env (.cons guard old) state)
    (updated : cert.update.lower.runLoopFree m.toPEG old = some next) :
    Eval (instruction m) env (route cert layout) state (if guard.down then 0 else 1)
      (pack m (if guard.down then next else old)) state := by
  let shifted : Schedule.Layout P carried := fun p => layout.shift (.tail p)
  have oldReads : shifted.Evaluates m (extend env .unit) old state :=
    fun _ p => (reads _ (.tail p)).rename (fun _ => rfl)
  have test : Isotope.LambdaSSA.Semantics.Tm.Eval (instruction m) env
      (.op .test (.pair (layout .head) .unit)) state
      (if guard.down then .inr .unit else .inl .unit) state :=
    .op (.pair (reads _ .head) .unit) ⟨.cons guard .nil, rfl, rfl, rfl⟩
  obtain ⟨flag⟩ := guard
  cases flag
  · exact .case_inl test (.br (read_packet m shifted _ old state oldReads))
  · refine .case_inr test (Schedule.emit_eval m cert.update shifted _ _ old next state 0 _ oldReads updated ?_)
    exact fun outputs localEnv ready => .br (read_packet m outputs localEnv next state ready)

theorem header_eval (m : TotalModel P) (env : Env (Atom m))
    (input output : Tuple (Region.model m).Val (valuePorts carried)) (again : Bool)
    (body : b.compile.body.run (Region.model m) input = RVSDG.Theta.bodyResult (Region.model m) again output)
    (state : σ) :
    Eval (instruction m) (extend env (Operational.pack (Region.model m) input)) (header b)
      state (if again then 0 else 1) (Operational.pack (Region.model m) output) state := by
  let source := fromPorts (F := (Region.model m).Val) carried input
  have round : encode m source = input := to_fromPorts input
  rw [← round] at body ⊢
  obtain ⟨guard, old, next, tested, updated, numbered⟩ := Region.body_run b.scalar m source
  have same := congrArg (Operational.split (Region.model m)) (numbered.symm.trans body)
  simp only [Operational.split_bodyResult] at same
  rw [← (Prod.mk.inj same).1, ← (Prod.mk.inj same).2]
  exact Schedule.emit_eval m b.scalar.guard _ _ _ source (.cons guard old) state _ _
    (fun _ p => Schedule.field_eval m p .var) tested
    (fun layout localEnv reads => route_eval b.scalar m layout localEnv guard old next state reads updated)

theorem lower_eval_iff_returns (m : TotalModel P) (input : Tuple m.toPEG.Value carried)
    (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Eval (instruction m) (Operational.inputEnv (Region.model m) (encode m input)) (lower b)
      start label payload finish ↔
      ∃ output, b.compile.Returns (Region.model m) (encode m input) output ∧
        label = 0 ∧ payload = Operational.pack (Region.model m) output ∧ finish = start :=
  Operational.loop_eval_iff (Region.model m) b.compile (header_eval b m)
    (instruction_deterministic m) (encode m input) start finish label payload

/-- Every finite target execution has the same ordered defined PEG result,
with the unique external exit and unchanged ambient state, and conversely. -/
theorem lower_eval_iff
    (neg : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)
    (idx : Index 1) (start finish : σ) (label : Nat) (payload : Value (Operational.Atom (Region.model m))) :
    Eval (instruction m)
      (Operational.inputEnv (Region.model m) (encode m input)) (lower b) start label payload finish ↔
      ∃ output : Tuple m.toPEG.Value carried,
        g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) ∧
        label = 0 ∧ payload = Operational.pack (Region.model m) (encode m output) ∧ finish = start := by
  let rt := Region.model m
  rw [lower_eval_iff_returns]
  constructor
  · rintro ⟨packed, ran, exit, same, state⟩
    let output := fromPorts (F := rt.Val) carried packed
    have round : encode m output = packed := to_fromPorts packed
    exact ⟨output, (b.returns_iff_observe m input neg idx output).mp (round.symm ▸ ran),
      exit, same.trans (congrArg (Operational.pack rt) round.symm), state⟩
  · rintro ⟨output, observed, exit, same, state⟩
    exact ⟨encode m output, (b.returns_iff_observe m input neg idx output).mpr observed, exit, same, state⟩

/-- A finite CFG evaluation recovers the common PEG pass count and all
defined eval prefixes from the single checked loop trace. -/
theorem firstExit_of_eval
    (neg : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)
    (idx : Index 1) (output : Tuple m.toPEG.Value carried) (state : σ)
    (ran : Eval (instruction m)
      (Operational.inputEnv (Region.model m) (encode m input)) (lower b)
      state 0 (Operational.pack (Region.model m) (encode m output)) state) :
    ∃ (k : Nat) (final : Tuple m.toPEG.Value (.bool :: carried)),
      carriedValues final = output ∧
      b.scalar.TraceObservation m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx k final := by
  obtain ⟨packed, returned, _, packetEq, _⟩ :=
    (lower_eval_iff_returns b m input state state 0 _).mp ran
  have same := Operational.pack_injective (Region.model m) packetEq
  have exactReturn : b.compile.Returns (Region.model m) (encode m input) (encode m output) :=
    same.symm ▸ returned
  obtain ⟨k, _, final, _, _, resultEq, exit, _⟩ := b.firstExit_of_returns m input neg idx output exactReturn
  exact ⟨k, final, resultEq, exit⟩

/-- The bounded runner finds the Figure 11 tuple exactly when a sufficiently
large finite bound exists. Fuel exhaustion is a bounded outcome. -/
theorem exists_runFuel_iff_observe
    (neg : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)
    (idx : Index 1) (output : Tuple m.toPEG.Value carried) :
    (∃ fuel, runFuel b m fuel input = some output) ↔
      g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) := by
  rw [← b.returns_iff_observe m input neg idx, Operational.returns_iff_runFuel]
  constructor
  · rintro ⟨fuel, ran⟩
    obtain ⟨packed, executed, decoded⟩ := Option.map_eq_some_iff.mp ran
    exact ⟨fuel, executed.trans (congrArg some ((to_fromPorts packed).symm.trans (congrArg (encode m) decoded)))⟩
  · rintro ⟨fuel, ran⟩
    exact ⟨fuel, Option.map_eq_some_iff.mpr ⟨_, ran, from_toPorts (F := (Region.model m).Val) output⟩⟩

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Proofs
