module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Transfer.ITree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Transfer.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlockTransport

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Proofs.ITree

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Refinement AbortEquiv)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend extend_zero extend_rename)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous (Family Opcode)

variable {n : Nat} {F : Family n} {I O J : Code} {Events : Type → Type}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)
local notation "Tree" => ITree.Tree Events
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

variable (instr : Silmaril.Isotope.Semantics.InstructionModel (Ty.denote (Lifted carriers))
  (Opcode F) (Silmaril.Elgot.ITree.Tree Events))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def litDeriv (c : Code) (v : c.Value) {m : Nat} {β : BoundCtx (Ty Unit) m} :
    Derivation Ops Free β (nativeValue m c v) c.ty :=
  match c, v with
  | .unit, _ => .unit
  | .sum L _, .inl v => .inl (litDeriv L v)
  | .sum _ R, .inr v => .inr (litDeriv R v)

private theorem litDenote (c : Code) (v : c.Value) {m : Nat} {β : BoundCtx (Ty Unit) m}
    (ρ : BoundEnv D β) :
    (litDeriv (F := F) c v).denote D instr γ ρ = (pure (c.raise v) : Tree c.Large) := by
  induction c with
  | unit => rfl
  | sum L R il ir =>
    cases v with
    | inl v => simp only [litDeriv, Derivation.denote, il, pure_bind]; rfl
    | inr v => simp only [litDeriv, Derivation.denote, ir, pure_bind]; rfl

private def stepDeriv {I : Code} (s : Step F I O) {m : Nat} {β : BoundCtx (Ty Unit) m} :
    Derivation Ops Free (β.snoc I.ty) (s.native m) O.ty :=
  match s with
  | .lit v => litDeriv O v
  | .call f x k => .let₁ (.op (litDeriv f.argCode x)) (stepDeriv k)
  | .split l r => .case .bv (stepDeriv l) (stepDeriv r)

private theorem stepDenote (s : Step F I O) {m : Nat} {β : BoundCtx (Ty Unit) m}
    (ρ : BoundEnv D β) (x : I.Large) :
    (stepDeriv s).denote D instr γ (ρ.snoc x) = s.denote instr x := by
  induction s generalizing m with
  | lit v => exact litDenote instr _ v (ρ.snoc x)
  | call f v k ih =>
    simp only [stepDeriv, Derivation.denote, litDenote, pure_bind, ih, Step.denote]
  | split l r il ir =>
    change (pure ((ρ.snoc x) (0 : Fin (m + 1))) >>= _) = _
    rw [BoundEnv.snoc_zero, pure_bind]
    cases x with
    | inl x => exact il (ρ.snoc _) x
    | inr x => exact ir (ρ.snoc _) x

theorem native_denote {ε : Type} [HasEff Ops ε] [Bot ε]
    (pureInstr : InstructionModel.RespectsPure (Φ := Ops) (ε := ε) instr)
    (s : Step F I (.sum O I)) (init : I.Value)
    (d : Derivation Ops Free .nil (.iter (nativeValue 0 I init) (s.native 0)) O.ty) :
    d.denote D instr γ ρ₀ = iter (s.denote instr) (I.raise init) := by
  let canonical : Derivation Ops Free .nil (.iter (nativeValue 0 I init) (s.native 0)) O.ty :=
    .iter (litDeriv I init) (stepDeriv s)
  have h : AbortEquiv (⊥ : ε) Free .nil _ _ O.ty := Refinement.refl d.toHasType
  rw [LetIter.Semantics.Categorical.denote_eq_of_abortEquiv_nil (Lifted carriers) instr pureInstr
    h d canonical ρ₀]
  change ((litDeriv I init).denote D instr γ ρ₀ >>= iter _) = _
  rw [litDenote, pure_bind]
  congr 1
  funext x
  rw [stepDenote]
  exact bind_pure _

variable (raw : Primitive Events (Opcode F) RawAtom)

private theorem termValue (c : Code) (v : c.Value) (env : Env RawAtom) :
    term raw env (value c v) = pure (encode c (c.raise v)) := by
  induction c with
  | unit => rfl
  | sum L R il ir => cases v <;> simp [value, term, il, ir] <;> rfl

private def route {I O : Code} : (Code.sum O I).Large → Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Transfer RawAtom
  | .inl b => (1, encode O b)
  | .inr a => (0, encode I a)

private theorem stepBody (compat : Compatible instr raw) {C : Code} (s : Step F I C)
    (x : I.Large) (env : Env RawAtom) (h : C = .sum O J) :
    region raw (extend env (encode I x)) (iterationBody s.ssa) =
      (s.denote instr x >>= fun y => pure (route (I := J) (O := O) (h ▸ y))) := by
  induction s generalizing env with
  | @lit A C v =>
    subst C
    change region raw _ (.case (value (.sum O J) v) (.br 1 (.var 0)) (.br 0 (.var 0))) = _
    rw [region, termValue, pure_bind, Step.denote, pure_bind]
    cases v with
    | inl v =>
      change (pure (encode O (O.raise v)) >>= fun a => pure (1, a)) = pure (1, encode O (O.raise v))
      rw [pure_bind]
    | inr v =>
      change (pure (encode J (J.raise v)) >>= fun a => pure (0, a)) = pure (0, encode J (J.raise v))
      rw [pure_bind]
  | @call A C f v k ih =>
    subst C
    change region raw (extend env (encode A x)) (.let₁ (.op f (value f.argCode v)) (iterationBody k.ssa)) = _
    rw [region, term, termValue, pure_bind, compat, bind_assoc, Step.denote, bind_assoc]
    congr 1
    funext y
    rw [pure_bind, ih y _ rfl]
  | @split L R C l r il ir =>
    subst C
    change region raw _ (.case (.var 0) (iterationBody l.ssa) (iterationBody r.ssa)) = _
    rw [region, term, extend_zero, pure_bind]
    cases x with
    | inl v => exact il v (extend env (encode (.sum L R) (.inl v))) rfl
    | inr v => exact ir v (extend env (encode (.sum L R) (.inr v))) rfl

private theorem cfg_shape (s : Step F I (.sum O I)) (init : I.Value) :
    loopCFG s init =
      .cfg (.br 0 (value I init)) 1
        (fun _ => (iterationBody s.ssa).renameVars (Silmaril.DeBruijn.lift Nat.succ)) := by
  unfold loopCFG compLSubst
  change ((iterateRegion I.ty s.ssa).renameVars (Silmaril.DeBruijn.lift Nat.succ)).substVars
    (Tm.singleSubst (value I init)) = _
  unfold iterateRegion feedbackRegion cfgEntryContinuations
  simp only [Region.renameVars, Region.substVars, Tm.rename, Tm.subst]
  congr 1
  funext i
  rw [Region.substVars_renameVars, Region.substVars_renameVars,
    Region.renameVars_eq_substVars]
  congr 1
  funext j
  cases j <;> rfl

private def statePacket (c : Code) (x : c.Large) : BlockInput RawAtom 1 :=
  (0, encode c x)

theorem loopCFG_denote (compat : Compatible instr raw) (s : Step F I (.sum O I))
    (init : I.Value) (env : Env RawAtom) :
    region raw env (loopCFG s init) =
      (iter (s.denote instr) (I.raise init) >>= fun b => pure (0, encode O b)) := by
  rw [cfg_shape, region]
  let step (p : BlockInput RawAtom 1) :=
    region raw (extend env p.2) ((iterationBody s.ssa).renameVars (Silmaril.DeBruijn.lift Nat.succ)) >>=
      fun out => (pure (splitTransfer 1 out) : Tree _)
  change (region raw env (.br 0 (value I init)) >>= fun out => Sum.elim pure (iter step) (splitTransfer 1 out)) = _
  simp only [region, termValue, pure_bind]
  change iter step (statePacket I (I.raise init)) = _
  have square : ((mapReturn (s.denote instr) (fun b => pure (0, encode O b))) >=>
      liftPure (Sum.map id (statePacket I))) = (liftPure (statePacket I) >=> step) := by
    funext x
    have rawStep : step (statePacket I x) =
        (s.denote instr x >>= fun v => pure (splitTransfer 1 (route (I := I) (O := O) v))) := by
      -- The extra captured slot lies below the local payload.
      unfold step statePacket
      rw [show region raw (extend env (encode I x))
          ((iterationBody s.ssa).renameVars (Silmaril.DeBruijn.lift Nat.succ)) =
        region raw (extend (fun i => env (i+1)) (encode I x)) (iterationBody s.ssa) from
          region_renameVars raw _ (extend_rename (fun _ => rfl) _)]
      rw [stepBody instr raw compat s x _ rfl, bind_assoc]
      simp only [pure_bind]
    change ((s.denote instr x >>= _) >>= _) = (pure (statePacket I x) >>= step)
    rw [pure_bind, rawStep, bind_assoc]
    congr 1
    funext v
    cases v <;> simp [route, splitTransfer, liftPure, statePacket]
  have replay := congrFun (ITree.iterate_uniformity _ step (statePacket I) square) (I.raise init)
  change _ = (pure (statePacket I (I.raise init)) >>= iter step) at replay
  rw [pure_bind] at replay
  exact ((congrFun (ITree.iterate_naturality (s.denote instr) (fun b => pure (0, encode O b)))
    (I.raise init)).trans replay).symm

section Endpoints

variable {ε : Type} [HasEff (Opcode F) ε]

theorem eraseLoop_denote [Bot ε] (pureInstr : InstructionModel.RespectsPure (ε := ε) instr)
    (compat : Compatible instr raw) (s : Step F I (.sum O I)) (init : I.Value) (env : Env RawAtom)
    (d : Derivation Ops Free .nil (.iter (nativeValue 0 I init) (s.native 0)) O.ty)
    {r : Region Ops} (hr : eraseLoop I (.iter (nativeValue 0 I init) (s.native 0)) = some r) :
    region raw env r = (d.denote D instr γ ρ₀ >>= fun b => pure (0, encode O b)) := by
  have same := Option.some.inj ((erase_loop s init).symm.trans hr)
  rw [← same, loopCFG_denote instr raw compat, native_denote instr pureInstr]

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}

theorem endpoint_observations (pureInstr : InstructionModel.RespectsPure (ε := ε) instr)
    (compat : Compatible instr raw) (t : Transfer.Rows F I O I) (init : I.Value)
    (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) (env : Env RawAtom)
    (d : Derivation Ops Free .nil (Transfer.fusedLoop t init) O.ty)
    (d' : Derivation Ops Free .nil (Transfer.expandedLoop t init) O.ty) :
    d.denote D instr γ ρ₀ = d'.denote D instr γ ρ₀ ∧
    ∃ r s, eraseLoop I (Transfer.fusedLoop t init) = some r ∧
      eraseLoop (.sum I t.pending) (Transfer.expandedLoop t init) = some s ∧
      Region.ValueBranches [Code.unit.ty] r [O.ty] ∧
      Region.ValueBranches [Code.unit.ty] s [O.ty] ∧
      Region.Paper.Extension.Eqv (targetSeed (⊥ : ε)) [Code.unit.ty] r s [O.ty] ∧
      region raw env r = (d.denote D instr γ ρ₀ >>= fun b => pure (0, encode O b)) ∧
      region raw env s = (d'.denote D instr γ ρ₀ >>= fun b => pure (0, encode O b)) := by
  obtain ⟨_, _, heq, r, s, hr, hs, tr, ts, joined⟩ := Transfer.endpoint_transport t init hf he
  exact ⟨LetIter.Semantics.Categorical.denote_eq_of_abortEquiv_nil (Lifted carriers) instr pureInstr
      heq d d' ρ₀,
    r, s, hr, hs, tr, ts, joined,
    eraseLoop_denote instr raw pureInstr compat t.fused init env d hr,
    eraseLoop_denote instr raw pureInstr compat t.expanded (.inl init) env d' hs⟩

end Endpoints

section Joined

open CategoryTheory
open Silmaril.Isotope.LetIter.Semantics.Categorical (ofInstructionModel ofTypeModel)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (RegionTypingCoherent denoteSingletonRegion)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed (ModelTree)
open Region.Paper.Extension.Singleton

variable {ε : Type} [HasEff (Opcode F) ε]

local notation "K" => Kleisli.Adjunction.toKleisli (ofTypeMonad (ModelTree Events))
local notation "M" => ofTypeModel (Ty.denote (Lifted carriers : Unit → Type 1))

theorem denote_eq_of_joined
    (coherent : letI := ofInstructionModel D instr; RegionTypingCoherent (Φ := Ops) K M)
    (pe : ε) {A B : Ty Unit} {r s : Region Ops}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B])
    (eq : Region.Paper.Extension.Eqv (targetSeed pe) [A] r s [B]) (input : D A) :
    let _ := ofInstructionModel D instr
    (denoteSingletonRegion K M hr.hasType).of input =
      (denoteSingletonRegion K M hs.hasType).of input := by
  let _ := ofInstructionModel D instr
  let _ := coherent
  have sound : SeedDenotes (Seed := targetSeed (F := F) pe) K M :=
    joined_seedDenotes (Φ := Ops) K M (fun _ _ => ⟨rfl, rfl⟩) pe
  have same := congrArg ((denoteFunctor K M (fun _ _ => ⟨rfl, rfl⟩) sound).map)
    ((ofRegion_eq_iff (targetSeed pe) hr hs).mpr eq)
  rw [denoteFunctor_map_ofRegion, denoteFunctor_map_ofRegion] at same
  exact congrArg (fun x => x.of input) same

end Joined

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Proofs.ITree
