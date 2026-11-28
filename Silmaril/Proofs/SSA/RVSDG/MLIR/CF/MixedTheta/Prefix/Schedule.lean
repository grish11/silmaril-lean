module

public import Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix.Defs
import Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Thms
import Silmaril.Semantics.ElgotMonads.Thms

public section

namespace Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix.Proofs

open Silmaril.MLIR
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.Pure (Operands i1)
open LambdaSSA.Acyclic.Theta
open LambdaSSA.Acyclic.Theta.Translation
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open Silmaril.Elgot.Part (Runs)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {τ Φ ε σ : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{0,0} τ] [InstructionModel Φ τ ε (StateT σ Part)]
variable {A : τ} {w : Width}
variable (codec : TyDen A ≃ BitVec w.val) (head : PureTheta.Loop Φ ε A) (order : Bool) (leaf : Leaf Φ A)

private def suffixPacket (route : LabelDen [A,A] ⊕ TyDen A) : Env [i1,i1,w] :=
  match route with
  | .inl out => .cons (BitVec.ofBool false) (exitPacket codec out)
  | .inr value => .cons (BitVec.ofBool true) (.cons (BitVec.ofBool false) (packet codec value))

private theorem suffix_result (input : Env [w]) (x : TyDen A) :
    eval (σ := σ) codec (.suffix leaf.code : Body Φ ε A w [w,w] _) ((packet codec x).append input) =
      (ExplicitRuntime.round (ε := ε) (m := StateT σ Part) leaf.loop x >>= fun route => pure (suffixPacket codec route)) := by
  simp only [eval, Leaf.code, Tail.eval, packet, Env.append, Env.get, Equiv.symm_apply_apply,
    ExplicitRuntime.round, Leaf.loop, bind_assoc]
  congr 1
  funext route
  cases route with
  | inl out =>
    change pure (suffixPacket codec (.inl (.inl out))) =
      ((pure (.inl (.inl out)) : StateT σ Part (LabelDen [A,A] ⊕ TyDen A)) >>=
        fun route => pure (suffixPacket codec route))
    rw [pure_bind]
  | inr next =>
    simp only [ExplicitRuntime.bodyAction, bind_assoc]
    congr 1
    funext mid
    congr 1
    funext route
    cases route <;> simp only [pure_bind] <;> rfl

private def prefixFrame : TyDen A ⊕ TyDen A → CF.Frame (Label w)
  | .inl x => ⟨.seam, packet codec x⟩
  | .inr x => ⟨.activate, packet codec x⟩

private def suffixFrame : LabelDen [A,A] ⊕ TyDen A → CF.Frame (Label w)
  | .inl out => ⟨.exit, exitPacket codec out⟩
  | .inr x => ⟨.suffix, packet codec x⟩

private theorem prefix_block (input : Env [w]) (x : TyDen A) :
    ((emit (w := w) head order leaf).block .activate).eval (eval (σ := σ) codec)
        ((packet codec x).append input) =
      (head.step (σ := σ) x >>= fun route => pure (.inl (prefixFrame codec route))) := by
  simp only [emit, CF.Ordered.Block.eval, eval, MixedTheta.activation_result, bind_assoc, pure_bind]
  congr 1
  funext route
  cases route <;>
    simp [MixedTheta.activationPacket, packet, CF.Terminator.eval, CF.Edge.eval, Operands.eval, Env.get, prefixFrame]
  all_goals rfl

private theorem suffix_block (input : Env [w]) (x : TyDen A) :
    ((emit (w := w) head order leaf).block .suffix).eval (eval (σ := σ) codec)
        ((packet codec x).append input) =
      (ExplicitRuntime.round (ε := ε) (m := StateT σ Part) leaf.loop x >>= fun route => pure (.inl (suffixFrame codec route))) := by
  simp only [emit, CF.Ordered.Block.eval, suffix_result, bind_assoc, pure_bind]
  congr 1
  funext route
  rcases route with (x | (x | dead)) | x
  · simp [suffixPacket, packet, CF.Terminator.eval, CF.Edge.eval, Operands.eval, Env.get, suffixFrame, exitPacket]
    rfl
  · simp [suffixPacket, packet, CF.Terminator.eval, CF.Edge.eval, Operands.eval, Env.get, suffixFrame, exitPacket]
    rfl
  · exact dead.elim
  · simp [suffixPacket, packet, CF.Terminator.eval, CF.Edge.eval, Operands.eval, Env.get, suffixFrame]
    rfl

private abbrev runAt (input : Env [w]) {widths : List Width} (label : Label w widths)
    (args : Env widths) (fuel : Nat) (token : σ) : Part (Option (Env [i1,w]) × σ) :=
  let cfg := emit (w := w) head order leaf
  (CF.Ordered.runBlock cfg.block (CF.Ordered.Block.eval (eval (σ := σ) codec)) input fuel
    (cfg.block label) (args.append input)).run token

private theorem prefix_step (input : Env [w]) (fuel : Nat) (start : TyDen A × σ) :
    runAt codec head order leaf input .activate (packet codec start.1) (fuel + 1) start.2 =
      (Elgot.StateT.body (head.step (σ := σ)) start).bind (Sum.elim
        (fun mid => runAt codec head order leaf input .seam (packet codec mid.1) fuel mid.2)
        (fun mid => runAt codec head order leaf input .activate (packet codec mid.1) fuel mid.2)) := by
  obtain ⟨x, initial⟩ := start
  change (CF.Ordered.runBlock _ _ _ (fuel + 1) _ _ : StateT σ Part _).run initial = _
  rw [CF.Ordered.runBlock, prefix_block codec head order leaf]
  simp only [bind_assoc, pure_bind, StateT.run_bind, Part.bind_eq_bind, Elgot.StateT.body,
    Function.comp_apply, Part.pure_eq_some, Part.bind_assoc, Part.bind_some]
  congr 1
  funext result
  rcases result with ⟨route, token⟩
  cases route <;> rfl

private theorem suffix_step (input : Env [w]) (fuel : Nat) (start : TyDen A × σ) :
    runAt codec head order leaf input .suffix (packet codec start.1) (fuel + 1) start.2 =
      (Elgot.StateT.body (ExplicitRuntime.round (ε := ε) (m := StateT σ Part) leaf.loop) start).bind (Sum.elim
        (fun finish => runAt codec head order leaf input .exit (exitPacket codec finish.1) fuel finish.2)
        (fun mid => runAt codec head order leaf input .suffix (packet codec mid.1) fuel mid.2)) := by
  obtain ⟨x, initial⟩ := start
  change (CF.Ordered.runBlock _ _ _ (fuel + 1) _ _ : StateT σ Part _).run initial = _
  rw [CF.Ordered.runBlock, suffix_block codec head order leaf]
  simp only [bind_assoc, pure_bind, StateT.run_bind, Part.bind_eq_bind, Elgot.StateT.body,
    Function.comp_apply, Part.pure_eq_some, Part.bind_assoc, Part.bind_some]
  congr 1
  funext result
  rcases result with ⟨route, token⟩
  cases route <;> rfl

-- A block which closes its local iteration can still branch to a suffix.
private theorem bounded_iff {X E Y : Type} (step : X → Part (E ⊕ X))
    (run : Nat → X → Part Y) (after : Nat → E → Part Y) (out : Y)
    (zero : ∀ x, out ∉ run 0 x)
    (succ : ∀ n x, run (n + 1) x = (step x).bind (Sum.elim (after n) (run n))) (x : X) :
    (∃ fuel, out ∈ run fuel x) ↔ ∃ mid, Runs step x mid ∧ ∃ fuel, out ∈ after fuel mid := by
  constructor
  · rintro ⟨fuel, found⟩
    induction fuel generalizing x with
    | zero => exact (zero x found).elim
    | succ n ih =>
      rw [succ] at found
      obtain ⟨route, ran, rest⟩ := Part.mem_bind_iff.mp found
      cases route with
      | inl mid => exact ⟨mid, .done ran, n, rest⟩
      | inr next =>
        obtain ⟨mid, reached, fuel, returned⟩ := ih next rest
        exact ⟨mid, .more ran reached, fuel, returned⟩
  · rintro ⟨mid, ran, fuel, finished⟩
    induction ran with
    | done last => exact ⟨fuel + 1, by rw [succ]; exact Part.mem_bind last finished⟩
    | more next _ ih =>
      obtain ⟨n, found⟩ := ih finished
      exact ⟨n + 1, by rw [succ]; exact Part.mem_bind next found⟩

private theorem exitPacket_inj : Function.Injective (exitPacket codec) := by
  intro l r eq
  have tag := congrArg (fun v : Env [i1,w] => v.get .here) eq
  have value := congrArg (fun v : Env [i1,w] => v.get (.there .here)) eq
  rcases l with x | (x | dead)
  · rcases r with y | (y | dead)
    · exact congrArg Sum.inl (codec.injective value)
    · have different : (0 : BitVec 1) ≠ 1 := by decide
      exact (different tag).elim
    · exact dead.elim
  · rcases r with y | (y | dead)
    · have different : (1 : BitVec 1) ≠ 0 := by decide
      exact (different tag).elim
    · exact congrArg (fun z => Sum.inr (Sum.inl z)) (codec.injective value)
    · exact dead.elim
  · exact dead.elim

private theorem exit_succ (input : Env [w]) (fuel : Nat) (out : LabelDen [A,A]) (token : σ) :
    runAt codec head order leaf input .exit (exitPacket codec out) (fuel + 1) token =
      Part.some (some (exitPacket codec out), token) := by
  rcases out with x | (x | dead)
  · simp [runAt, emit, CF.Ordered.runBlock, CF.Ordered.Block.eval, eval, MixedTheta.eval, MixedTheta.Body.eval,
      exitPacket, packet, Operands.eval, Env.append, Env.get, CF.Terminator.eval, StateT.run_pure, Part.pure_eq_some]
    rfl
  · simp [runAt, emit, CF.Ordered.runBlock, CF.Ordered.Block.eval, eval, MixedTheta.eval, MixedTheta.Body.eval,
      exitPacket, packet, Operands.eval, Env.append, Env.get, CF.Terminator.eval, StateT.run_pure, Part.pure_eq_some]
    rfl
  · exact dead.elim

private theorem exit_iff (input : Env [w]) (out : LabelDen [A,A]) (final : σ) (finish : LabelDen [A,A] × σ) :
    (∃ fuel, (some (exitPacket codec out), final) ∈
        runAt codec head order leaf input .exit (exitPacket codec finish.1) fuel finish.2) ↔
      finish = (out, final) := by
  cases finish with
  | mk label token =>
    constructor
    · rintro ⟨fuel, got⟩
      cases fuel with
      | zero => simp [runAt, CF.Ordered.runBlock, StateT.run_pure, Part.pure_eq_some] at got
      | succ fuel =>
        rw [exit_succ] at got
        have eq := Part.mem_some_iff.mp got
        have vals := congrArg (fun p : Option (Env [i1,w]) × σ => p.1) eq
        have tokens := congrArg (fun p : Option (Env [i1,w]) × σ => p.2) eq
        exact Prod.ext (exitPacket_inj codec (Option.some.inj vals).symm) tokens.symm
    · intro eq
      cases eq
      exact ⟨1, by rw [exit_succ]; exact Part.mem_some _⟩

private theorem seam_succ (input : Env [w]) (fuel : Nat) (x : TyDen A) (token : σ) :
    runAt codec head order leaf input .seam (packet codec x) (fuel + 1) token =
      runAt codec head order leaf input .suffix (packet codec x) fuel token := by
  simp only [runAt, CF.Ordered.runBlock, emit, CF.Ordered.Block.eval, eval, MixedTheta.eval,
    MixedTheta.Body.eval, packet, Operands.eval, Env.append, Env.get, pure_bind, CF.Terminator.eval, CF.Edge.eval]

private theorem entry_succ (input : TyDen A) (fuel : Nat) (token : σ) :
    ((emit head order leaf).run (eval (σ := σ) codec) (fuel + 1) (packet codec input)).run token =
      runAt codec head order leaf (packet codec input) .activate (packet codec input) fuel token := by
  simp only [CF.Ordered.Cfg.run, runAt, CF.Ordered.runBlock, emit, CF.Ordered.Block.eval, eval, MixedTheta.eval,
    MixedTheta.Body.eval, packet, Operands.eval, Env.get, pure_bind, CF.Terminator.eval, CF.Edge.eval]

theorem cfg_iff (input : TyDen A) (initial : σ) (out : LabelDen [A,A]) (final : σ) :
    (∃ fuel, ((emit head order leaf).run (eval (σ := σ) codec) fuel (packet codec input)).run initial =
      Part.some (some (exitPacket codec out), final)) ↔
    ∃ mid : TyDen A × σ, Runs (Elgot.StateT.body (head.step (σ := σ))) (input, initial) mid ∧
      Runs (Elgot.StateT.body (ExplicitRuntime.round (ε := ε) (m := StateT σ Part) leaf.loop)) mid (out, final) := by
  let env := packet codec input
  let result := (some (exitPacket codec out), final)
  simp only [Part.eq_some_iff]
  have atPrefix :
      (∃ fuel, result ∈ ((emit head order leaf).run (eval (σ := σ) codec) fuel env).run initial) ↔
        ∃ fuel, result ∈ runAt codec head order leaf env .activate env fuel initial := by
    constructor
    · rintro ⟨fuel, got⟩
      cases fuel with
      | zero => simp [CF.Ordered.Cfg.run, CF.Ordered.runBlock, StateT.run_pure, Part.pure_eq_some, result] at got
      | succ fuel =>
        rw [entry_succ] at got
        exact ⟨fuel, got⟩
    · rintro ⟨fuel, got⟩
      exact ⟨fuel + 1, by rw [entry_succ]; exact got⟩
  refine atPrefix.trans ?_
  refine (bounded_iff (Elgot.StateT.body (head.step (σ := σ)))
    (fun fuel mid => runAt codec head order leaf env .activate (packet codec mid.1) fuel mid.2)
    (fun fuel mid => runAt codec head order leaf env .seam (packet codec mid.1) fuel mid.2)
    result (fun _ => by simp [runAt, CF.Ordered.runBlock, StateT.run_pure, Part.pure_eq_some, result])
    (prefix_step codec head order leaf env) (input, initial)).trans ?_
  apply exists_congr
  intro mid
  apply and_congr_right
  intro _
  have atSuffix :
      (∃ fuel, result ∈ runAt codec head order leaf env .seam (packet codec mid.1) fuel mid.2) ↔
        ∃ fuel, result ∈ runAt codec head order leaf env .suffix (packet codec mid.1) fuel mid.2 := by
    constructor
    · rintro ⟨fuel, got⟩
      cases fuel with
      | zero => simp [runAt, CF.Ordered.runBlock, StateT.run_pure, Part.pure_eq_some, result] at got
      | succ fuel => rw [seam_succ] at got; exact ⟨fuel, got⟩
    · rintro ⟨fuel, got⟩
      exact ⟨fuel + 1, by rw [seam_succ]; exact got⟩
  refine atSuffix.trans ((bounded_iff (Elgot.StateT.body (ExplicitRuntime.round (ε := ε) (m := StateT σ Part) leaf.loop))
    (fun fuel mid => runAt codec head order leaf env .suffix (packet codec mid.1) fuel mid.2)
    (fun fuel finish => runAt codec head order leaf env .exit (exitPacket codec finish.1) fuel finish.2)
    result (fun _ => by simp [runAt, CF.Ordered.runBlock, StateT.run_pure, Part.pure_eq_some, result])
    (suffix_step codec head order leaf env) mid).trans ?_)
  simp only [result, exit_iff, exists_eq_right]

end Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix.Proofs
