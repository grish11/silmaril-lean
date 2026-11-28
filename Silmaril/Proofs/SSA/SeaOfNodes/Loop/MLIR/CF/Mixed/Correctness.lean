module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed.Defs
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.MLIR.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed

open Silmaril.SSA.SeaOfNodes
open Diamond (Val ValueSort dataPorts)
open Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF
open Loop.MLIR.CF.Mixed
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)
open Silmaril.SSA.SeaOfNodes.MLIR.Lowering
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)

variable {inputs carried : List (ValueSort Width)} {result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

private theorem names_agree {sorts : List (ValueSort Width)} {suffix : List Width} (env : Env suffix)
    (values : Tuple (Val Word) (dataPorts sorts)) :
    NamesAgree ((encodeValues values).append env) (names suffix sorts) values := by
  induction sorts with
  | nil => intro _ port; cases port
  | cons s rest ih =>
    cases values with
    | cons value tail =>
      intro sort port
      cases port with
      | head => rfl
      | tail p => exact weaken_names (ih tail) (valueBits value) p

private theorem cast_names_agree {Γ Δ : List Width} (same : Γ = Δ) {ports : List (Diamond.Ty Width)}
    {env : Env Γ} {names : Tuple (Names Γ) ports} {values : Tuple (Val Word) ports}
    (agrees : NamesAgree env names values) :
    NamesAgree (same ▸ env) (same ▸ names) values := by
  cases same
  exact @agrees

private theorem append_nil {Γ : List Width} (env : Env Γ) :
    List.append_nil Γ ▸ env.append .nil = env := by
  induction env with
  | nil => rfl
  | @cons Γ w value tail ih =>
    have cast_cons (left right : List Width) (eq : left = right) (data : Env left) :
        congrArg (List.cons w) eq ▸ Env.cons value data = Env.cons value (eq ▸ data) := by
      cases eq
      rfl
    change (congrArg (List.cons w) (List.append_nil Γ) ▸ Env.cons value (tail.append .nil)) = _
    rw [cast_cons _ _ (List.append_nil Γ), ih]

private theorem entry_agree (values : Tuple (Val Word) (dataPorts inputs)) :
    NamesAgree (encodeValues values) (entryScope inputs).inputs values := by
  have agrees : NamesAgree (List.append_nil (Widths inputs) ▸ (encodeValues values).append .nil)
      (entryScope inputs).inputs values := cast_names_agree (List.append_nil (Widths inputs)) (names_agree .nil values)
  rw [append_nil] at agrees
  exact @agrees

private theorem capture_agree {Γ : List Width} {ports : List (Diamond.Ty Width)}
    {env : Env Γ} {names : Tuple (Names Γ) ports} {values : Tuple (Val Word) ports}
    (agrees : NamesAgree env names values) {before : List Width} (old : Env before) :
    NamesAgree (old.append env) (Bank.prependNames before names) values := by
  induction old with
  | nil => exact agrees
  | cons val _ ih => exact weaken_names ih val

private theorem append_agree {Γ : List Width} {left right : List (Diamond.Ty Width)} {env : Env Γ}
    {front : Tuple (Names Γ) left} {back : Tuple (Names Γ) right}
    {values : Tuple (Val Word) left} {tail : Tuple (Val Word) right}
    (first : NamesAgree env front values) (last : NamesAgree env back tail) :
    NamesAgree env (appendTuple back front) (appendTuple tail values) := by
  induction front with
  | nil => cases values; exact last
  | cons name rest ih =>
    cases values with
    | cons value restValues =>
      intro s port
      cases port with
      | head => exact first .head
      | tail p => exact ih (fun p => first (.tail p)) p

variable (g : Program inputs carried result entrySigs headerSigs)
variable (input : Tuple (Val Word) (dataPorts inputs))

private abbrev headerAt (old : Tuple (Val Word) (dataPorts carried)) : Frame (Label carried result) :=
  ⟨.header, encodeValues old⟩

private abbrev exitAt (value : Word result) : Frame (Label carried result) :=
  ⟨.exit, .cons value .nil⟩

private def stepFrame : Word result ⊕ Tuple (Val Word) (dataPorts carried) → Frame (Label carried result)
  | .inl value => exitAt value
  | .inr next => headerAt next

theorem entry_frame :
    (lower g).entry.eval evalOp (fun term env => term.eval env) (encodeValues input) =
      .inl ⟨.header, encodeValues (g.initial model input)⟩ := by
  refine lowerCode_eval opcode evalOp model.run opcode_eval g.preheader _ _ input PUnit.unit
    ⟨entry_agree input, trivial⟩ (entryTerm g) (fun term env => term.eval env) _ ?_
  intro Δ scope env ok
  exact congrArg (fun args => Sum.inl (Frame.mk Bank.Label.header args))
    (ok.operands_eval (g.phiInputs .entry))

theorem header_frame (old : Tuple (Val Word) (dataPorts carried)) :
    ((lower g).block .header).eval evalOp (fun term env => term.eval env)
      ((encodeValues old).append (encodeValues input)) =
      .inl (match g.step model input old with
        | .inl value => ⟨.exit, .cons value .nil⟩
        | .inr next => ⟨.header, encodeValues next⟩) := by
  let args := appendTuple old input
  have bound : (headerScope inputs carried).Agrees ((encodeValues old).append (encodeValues input))
      args PUnit.unit :=
    ⟨append_agree (capture_agree (entry_agree input) (encodeValues old))
      (names_agree (encodeValues input) old), trivial⟩
  refine lowerCode_eval opcode evalOp model.run opcode_eval g.header _ _ args _ bound
    (headerTerm g) (fun term env => term.eval env) _ ?_
  intro Δ scope env ok
  let locals := g.header.eval model args PUnit.unit
  have testBit (b : Bool) : (BitVec.ofBool b).getLsbD 0 = b := by cases b <;> rfl
  have guard : (env.get (scope.resolveValue g.predicate)).getLsbD 0 =
      (Diamond.read model g.predicate args locals).down :=
    (congrArg (fun bits : BitVec 1 => bits.getLsbD 0) (ok.resolve g.predicate)).trans
      (testBit (Diamond.read model g.predicate args locals).down)
  have next : (operands scope (g.phiInputs .backedge)).eval env =
      encodeValues (g.latch model .backedge args locals) :=
    ok.operands_eval (g.phiInputs .backedge)
  have returned : env.get (scope.resolveValue g.result) = Diamond.read model g.result args locals :=
    ok.resolve g.result
  change Sum.inl (if (env.get (scope.resolveValue g.predicate)).getLsbD 0 then
      (⟨.header, (operands scope (g.phiInputs .backedge)).eval env⟩ : Frame (Label carried result))
    else exitAt (env.get (scope.resolveValue g.result))) = .inl (stepFrame (g.step model input old))
  erw [guard, next, returned]
  have route (test : Bool) (next : Tuple (Val Word) (dataPorts carried)) (out : Word result) :
      (if test then headerAt next else exitAt out) = stepFrame (if test then .inr next else .inl out) := by
    cases test <;> rfl
  exact congrArg Sum.inl (route _ _ _)

private theorem run_entry (fuel : Nat) :
    (lower g).run evalOp (fuel + 1) (encodeValues input) =
      (lower g).runFrom evalOp fuel (encodeValues input) (headerAt (g.initial model input)) := by
  unfold Cfg.run
  rw [Cfg.runBlock, entry_frame]
  rfl

private theorem run_header (fuel : Nat) (old : Tuple (Val Word) (dataPorts carried)) :
    (lower g).runFrom evalOp (fuel + 1) (encodeValues input) (headerAt (result := result) old) =
      (lower g).runFrom evalOp fuel (encodeValues input) (stepFrame (g.step model input old)) := by
  change (lower g).runBlock evalOp _ (fuel + 1) ((lower g).block .header)
    ((encodeValues old).append (encodeValues input)) = _
  rw [Cfg.runBlock, header_frame]
  rfl

private theorem run_from (budget : Nat) (old : Tuple (Val Word) (dataPorts carried)) :
    (lower g).runFrom evalOp (budget + 2) (encodeValues input) (headerAt (result := result) old) =
      (g.evalFrom model input budget old).map (fun value => Env.cons value .nil) := by
  induction budget generalizing old with
  | zero =>
    erw [Loop.Graph.evalFrom.eq_1 g model input old]
    rw [show 0 + 2 = 1 + 1 by rfl, run_header]
    cases g.step model input old with
    | inl value => rfl
    | inr next => exact run_header g input 0 next
  | succ fuel ih =>
    erw [Loop.Graph.evalFrom.eq_2 g model input old fuel]
    rw [show fuel + 1 + 2 = (fuel + 2) + 1 by rfl, run_header]
    cases g.step model input old with
    | inl value => rfl
    | inr next => exact ih next

theorem run_budget (budget : Nat) :
    (lower g).run evalOp (budget + 3) (encodeValues input) =
      (g.evalBackedges model budget input).map (fun value => Env.cons value .nil) := by
  erw [show budget + 3 = (budget + 2) + 1 by rfl, run_entry, run_from]
  rfl

theorem run_short (fuel : Nat) (short : fuel < 3) :
    (lower g).run evalOp fuel (encodeValues input) = none := by
  have casesFuel : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 := by omega
  rcases casesFuel with rfl | rfl | rfl
  · rfl
  · rw [show 1 = 0 + 1 by rfl, run_entry]
    rfl
  · erw [show 2 = (0 + 1) + 1 by rfl, run_entry, run_header]
    cases g.step model input (g.initial model input) <;> rfl

end Silmaril.Proofs.SSA.SeaOfNodes.Loop.MLIR.CF.Mixed
