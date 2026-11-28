module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Thms
public import Silmaril.SSA.MLIR.SCF.While.Thms
import Silmaril.SSA.PEG.Bridge.RVSDG.Thms
import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Proofs

open Silmaril.MLIR.Arith (Width Var Env)
open Silmaril.MLIR.Pure (Code Eval Operands)
open Silmaril.MLIR.SCF (While Condition Yield Return)
open RVSDG (Port Tuple)
open RVSDG.LambdaSSA.Theta
open Simple.Revert.While.Region (Reads Schedule)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)
open Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Compiler (Layout emit)

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried vars ins outs : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P carried [t] n 1} {Γ : List Width}
variable (profile : Profile Data) (evalOp : Eval (Opcode profile P))

private theorem encode_decodeValue (t : Ty Data) (word : BitVec (profile.width t).val) :
    profile.encodeValue t (profile.decodeValue t word) = word := by
  cases t with
  | data => rfl
  | count => exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)
  | bool => exact (BitVec.setWidth_one (x := word)).symm.trans (BitVec.setWidth_eq word)

theorem encode_decode (ts : List (Ty Data)) (env : Env (profile.widths ts)) :
    profile.encode (profile.decode ts env) = env := by
  induction ts with
  | nil => cases env; rfl
  | cons t ts ih =>
    cases env with
    | cons word tail =>
      change Env.cons (profile.encodeValue t (profile.decodeValue t word))
        (profile.encode (profile.decode ts tail)) = .cons word tail
      rw [encode_decodeValue, ih]

private def Agrees (layout : Layout profile vars Γ) (env : Env Γ)
    (store : Tuple (Ty.Value profile.carrier) vars) : Prop :=
  ∀ t (p : Port vars t), profile.decodeValue t (env.get (layout p)) = store.get p

private theorem initial_agrees (env : Env (profile.widths vars)) :
    Agrees profile (Layout.initial profile) env (profile.decode vars env) := by
  intro t p
  induction p with
  | head => cases env; rfl
  | tail p ih => cases env with | cons head tail => exact ih tail

private theorem front_agrees (state : Env (profile.widths vars)) (input : Env Γ) :
    Agrees profile (Layout.front profile) (state.append input) (profile.decode vars state) := by
  intro t p
  induction p with
  | head => cases state; rfl
  | tail p ih => cases state with | cons head tail => exact ih tail

private theorem decode_operands (layout : Layout profile vars Γ) (env : Env Γ)
    (store : Tuple (Ty.Value profile.carrier) vars) (agrees : Agrees profile layout env store)
    (slots : Tuple (Port vars) ins) :
    profile.decode ins ((Layout.operands profile layout slots).eval env) =
      slots.map (fun _ p => store.get p) := by
  induction slots with
  | nil => rfl
  | cons p ps ih => exact congrArg₂ Tuple.cons (agrees _ p) ih

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

private theorem decode_packet (layout : Layout profile vars Γ) (env : Env Γ)
    (store : Tuple (Ty.Value profile.carrier) vars) (agrees : Agrees profile layout env store) :
    profile.decode vars ((Layout.packet profile layout).eval env) = store := by
  rw [Layout.packet, decode_operands profile layout env store agrees]
  apply tuple_ext
  intro t p
  rw [Simple.get_map, Simple.ports_get]

private theorem args_eval {scope : Tuple (Ref g.sort) vars} {refs : Tuple (Ref g.sort) ins}
    (reads : Reads scope refs) (store : Tuple (Ty.Value profile.carrier) vars) :
    reads.args.eval (model profile evalOp).toPEG store =
      some (reads.slots.map fun _ p => store.get p) := by
  induction reads with
  | nil => rfl
  | cons _ _ _ ih =>
    simp [Reads.args, Reads.slots, Simple.Args.eval, Simple.Expr.evalLift, Tuple.map, ih]

private theorem emit_eval {Term : List Width → Type} {α : Type} (result : α → Prop)
    {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    (schedule : Schedule g false roots scope) (layout : Layout profile vars Γ)
    (finish : ∀ {Δ}, Layout profile outs Δ → Term Δ)
    (evalTerm : ∀ {Δ}, Term Δ → Env Δ → α) (env : Env Γ)
    (store : Tuple (Ty.Value profile.carrier) vars) (output : Tuple (Ty.Value profile.carrier) outs)
    (agrees : Agrees profile layout env store)
    (ran : schedule.lower.runLoopFree (model profile evalOp).toPEG store = some output)
    (continued : ∀ {Δ} (outputs : Layout profile outs Δ) (localEnv : Env Δ),
      Agrees profile outputs localEnv output → result (evalTerm (finish outputs) localEnv)) :
    result ((emit profile schedule layout finish).eval evalOp evalTerm env) := by
  induction schedule generalizing Γ with
  | done reads =>
    have projected : reads.slots.map (fun _ p => store.get p) = output := Option.some.inj ran
    refine continued _ env (fun t p => ?_)
    rw [← projected, Simple.get_map]
    exact agrees t (reads.slots.get p)
  | bind i op refs fresh row reads tail ih =>
    let words := (Layout.operands profile layout reads.slots).eval env
    have decoded := decode_operands profile layout env store agrees reads.slots
    have called : (model profile evalOp).run op (reads.slots.map fun _ p => store.get p) =
        profile.decodeValue (g.sort i) (evalOp (.apply op) words) := by
      rw [← decoded]
      change profile.decodeValue (g.sort i) (evalOp (.apply op) (profile.encode (profile.decode _ words))) = _
      rw [encode_decode]
    have rest : tail.lower.runLoopFree (model profile evalOp).toPEG
        (.cons (profile.decodeValue (g.sort i) (evalOp (.apply op) words)) store) = some output := by
      simpa only [Schedule.lower, Simple.Stmt.runLoopFree, Simple.Expr.eval, Simple.Expr.evalLift,
        args_eval profile evalOp reads store, TotalModel.toPEG, Option.elim,
        Option.map_some, Option.bind_some, called] using ran
    refine ih (Layout.push profile layout) finish _ _ output ?_ rest continued
    intro t p
    cases p with
    | head => rfl
    | tail p => exact agrees t p
  | branch enabled => cases enabled

variable {g' : Graph P carried carried n 1} {slot : Port carried t} {invariants : Bool}
variable (b : Bundle g' slot invariants)

private theorem before_eval (state input : Env (profile.widths carried)) (guard : ULift Bool)
    (old : Tuple (Ty.Value profile.carrier) carried)
    (ran : b.scalar.guard.lower.runLoopFree (model profile evalOp).toPEG (profile.decode carried state) =
      some (.cons guard old)) :
    let result := (lower profile b).before.eval evalOp Condition.eval (state.append input)
    result.1 = guard.down ∧ profile.decode carried result.2 = old := by
  refine emit_eval profile evalOp
    (fun result => result.1 = guard.down ∧ profile.decode carried result.2 = old)
    b.scalar.guard (Layout.front profile)
    (fun outputs => .condition (outputs .head) (Layout.packet profile (fun p => outputs (.tail p))))
    Condition.eval _ _ _ (front_agrees profile state input) ran ?_
  intro Δ layout env agrees
  exact ⟨congrArg ULift.down (agrees _ .head),
    decode_packet profile (fun p => layout (.tail p)) env old (fun t p => agrees t (.tail p))⟩

private theorem after_eval (payload input : Env (profile.widths carried))
    (next : Tuple (Ty.Value profile.carrier) carried)
    (ran : b.scalar.update.lower.runLoopFree (model profile evalOp).toPEG (profile.decode carried payload) =
      some next) :
    profile.decode carried ((lower profile b).after.eval evalOp Yield.eval (payload.append input)) =
      next := by
  refine emit_eval profile evalOp (fun result => profile.decode carried result = next)
    b.scalar.update (Layout.front profile) (fun outputs => .yield (Layout.packet profile outputs))
    Yield.eval _ _ _ (front_agrees profile payload input) ran ?_
  intro Δ layout env agrees
  exact decode_packet profile layout env next agrees

private theorem runFrom_eq (fuel : Nat) (input state : Env (profile.widths carried)) :
    let m := model profile evalOp
    ((lower profile b).runFrom evalOp input fuel state).map
      (fun result => encode m (profile.decode carried result)) =
    Operational.runFuel (Region.model m) b.compile fuel (encode m (profile.decode carried state)) := by
  dsimp only
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    obtain ⟨guard, old, next, tested, updated, numbered⟩ :=
      Region.body_run b.scalar (model profile evalOp) (profile.decode carried state)
    have before := before_eval profile evalOp b state input guard old tested
    cases chosen : (lower profile b).before.eval evalOp Condition.eval (state.append input) with
    | mk takeBody payload =>
      have branch : takeBody = guard.down ∧ profile.decode carried payload = old := by
        simpa only [chosen] using before
      rw [While.runFrom, chosen,
        Operational.runFuel, numbered, Operational.split_bodyResult, ← branch.1]
      cases takeBody
      · have stopped := decode_packet profile (Layout.front profile) (payload.append input)
          (profile.decode carried payload) (front_agrees profile payload input)
        exact congrArg (fun output => some (encode (model profile evalOp) output)) (stopped.trans branch.2)
      · have ranUpdate := after_eval profile evalOp b payload input next (branch.2.symm ▸ updated)
        have continued := ih ((lower profile b).after.eval evalOp Yield.eval (payload.append input))
        rw [ranUpdate] at continued
        exact continued

theorem run_eq (fuel : Nat) (input : Env (profile.widths carried)) :
    let m := model profile evalOp
    ((lower profile b).run evalOp fuel input).map (fun result => encode m (profile.decode carried result)) =
      Operational.runFuel (Region.model m) b.compile fuel (encode m (profile.decode carried input)) := by
  have decoded := decode_packet profile (Layout.initial profile) input (profile.decode carried input)
    (initial_agrees profile input)
  have initialized : (lower profile b).init.eval input = input := by
    change (Layout.packet profile (Layout.initial profile)).eval input = input
    have encoded := congrArg (fun vals => profile.encode vals) decoded
    simpa only [encode_decode] using encoded
  rw [While.run, initialized]
  exact runFrom_eq profile evalOp b fuel input input

private theorem output_injective :
    Function.Injective (fun result : Env (profile.widths carried) =>
      encode (model profile evalOp) (profile.decode carried result)) := by
  intro left right same
  let M := Region.model (model profile evalOp)
  have decoded := congrArg (fromPorts (F := M.Val) carried) same
  have source := (from_toPorts (F := M.Val) (profile.decode carried left)).symm.trans
    (decoded.trans (from_toPorts (F := M.Val) (profile.decode carried right)))
  exact (encode_decode profile carried left).symm.trans
    ((congrArg (fun vals => profile.encode vals) source).trans (encode_decode profile carried right))

theorem returns_iff_numbered (input output : Env (profile.widths carried)) :
    let m := model profile evalOp
    (∃ fuel, (lower profile b).run evalOp fuel input = some output) ↔
      b.compile.Returns (Region.model m) (encode m (profile.decode carried input))
        (encode m (profile.decode carried output)) := by
  dsimp only
  rw [Operational.returns_iff_runFuel]
  constructor
  · rintro ⟨fuel, ran⟩
    exact ⟨fuel, (run_eq profile evalOp b fuel input).symm.trans (congrArg (Option.map _) ran)⟩
  · rintro ⟨fuel, ran⟩
    obtain ⟨result, returned, same⟩ := Option.map_eq_some_iff.mp ((run_eq profile evalOp b fuel input).trans ran)
    exact ⟨fuel, returned.trans (congrArg some (output_injective profile evalOp same))⟩

theorem firstExit_of_run (neg : ∀ flag : Bool,
    (model profile evalOp).run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)
    (input output : Env (profile.widths carried)) (idx : Index 1)
    (fuel : Nat) (ran : (lower profile b).run evalOp fuel input = some output) :
    let m := model profile evalOp
    ∃ (k : Nat) (final : Tuple m.toPEG.Value (.bool :: carried)),
      carriedValues final = profile.decode carried output ∧
        b.scalar.TraceObservation m.toPEG
          (g'.denote m.toPEG (profile.decode carried input) b.demandWellFounded) idx k final := by
  have returned := (returns_iff_numbered profile evalOp b input output).mp ⟨fuel, ran⟩
  obtain ⟨k, _, final, _, _, same, trace, _⟩ := b.firstExit_of_returns
    (model profile evalOp) (profile.decode carried input) neg idx (profile.decode carried output) returned
  exact ⟨k, final, same, trace⟩

end Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Proofs
