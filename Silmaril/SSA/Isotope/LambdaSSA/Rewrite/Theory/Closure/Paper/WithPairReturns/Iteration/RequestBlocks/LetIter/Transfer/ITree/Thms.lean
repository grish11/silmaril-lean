module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Transfer.ITree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Transfer.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Transfer.ITree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlockTransport.TransferITree

/-! # Weak observations of the actual transfer-plan endpoints

The native expansion is sound in a shared typed ITree interpretation
under its bottom-purity premise. Its exact erased CFGs also agree with
that observation when each raw primitive agrees on encoded typed inputs
and replies. The existing weak iterator absorbs silent transfers and
the outward result arrives at label zero. The typed joined-quotient
interpretation uses the usual independent region typing coherence premise.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (Primitive region)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous (Family Opcode)

variable {n : Nat} {F : Family n} {I O : Code} {Events : Type → Type}
  {instr : Silmaril.Isotope.Semantics.InstructionModel (Ty.denote (Lifted carriers)) (Opcode F) (ITree.Tree Events)}
  {raw : Primitive Events (Opcode F) RawAtom}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

/-- The actual one-block CFG computes the weak iteration of its typed step.
The result is encoded at outward label zero. -/
theorem loopCFG_denote (compat : Compatible instr raw)
    (s : Step F I (.sum O I)) (init : I.Value) (env : Env RawAtom) :
    region raw env (loopCFG s init) =
      (iter (s.denote instr) (I.raise init) >>= fun b => pure (0, encode O b)) :=
  Proofs.ITree.loopCFG_denote instr raw compat s init env

variable {ε : Type} [HasEff (Opcode F) ε]

/-- The actual native loop computes the weak iteration of its typed step,
independently of the chosen exact typing derivation. -/
theorem native_loop_denote [Bot ε] (pureInstr : InstructionModel.RespectsPure (ε := ε) instr)
    (s : Step F I (.sum O I)) (init : I.Value)
    (d : Derivation Ops Free .nil (.iter (nativeValue 0 I init) (s.native 0)) O.ty) :
    d.denote D instr γ ρ₀ = iter (s.denote instr) (I.raise init) :=
  Proofs.ITree.native_denote instr pureInstr s init d

/-- The exact SSA erasure of a finite typed native loop preserves its
weak observation after encoding the outward result. -/
theorem eraseLoop_denote [Bot ε] (pureInstr : InstructionModel.RespectsPure (ε := ε) instr)
    (compat : Compatible instr raw) (s : Step F I (.sum O I)) (init : I.Value) (env : Env RawAtom)
    (d : Derivation Ops Free .nil (.iter (nativeValue 0 I init) (s.native 0)) O.ty)
    {r : Region Ops} (hr : eraseLoop I (.iter (nativeValue 0 I init) (s.native 0)) = some r) :
    region raw env r = (d.denote D instr γ ρ₀ >>= fun b => pure (0, encode O b)) :=
  Proofs.ITree.eraseLoop_denote instr raw pureInstr compat s init env d hr

section Endpoints

variable [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}

/-- Compare the actual fused and expanded loops at the supplied iterative
bound, and relate each to its exact joined-quotient representative in a
common event family. Both erased representatives therefore agree. -/
theorem Transfer.endpoint_observations (pureInstr : InstructionModel.RespectsPure (ε := ε) instr)
    (compat : Compatible instr raw) (t : Rows F I O I) (init : I.Value)
    (hf : ∀ f : Ops, instrEff f ≤ e) (he : IsIterative e) (env : Env RawAtom)
    (d : Derivation Ops Free .nil (fusedLoop t init) O.ty)
    (d' : Derivation Ops Free .nil (expandedLoop t init) O.ty) :
    d.denote D instr γ ρ₀ = d'.denote D instr γ ρ₀ ∧
    ∃ r s, eraseLoop I (fusedLoop t init) = some r ∧
      eraseLoop (.sum I t.pending) (expandedLoop t init) = some s ∧
      Region.ValueBranches [Code.unit.ty] r [O.ty] ∧
      Region.ValueBranches [Code.unit.ty] s [O.ty] ∧
      Region.Paper.Extension.Eqv (targetSeed (⊥ : ε)) [Code.unit.ty] r s [O.ty] ∧
      region raw env r = (d.denote D instr γ ρ₀ >>= fun b => pure (0, encode O b)) ∧
      region raw env s = (d'.denote D instr γ ρ₀ >>= fun b => pure (0, encode O b)) :=
  Proofs.ITree.endpoint_observations instr raw pureInstr compat t init hf he env d d'

end Endpoints

section Joined

open CategoryTheory
open Silmaril.Isotope.LetIter.Semantics.Categorical (ofInstructionModel ofTypeModel)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (RegionTypingCoherent denoteSingletonRegion)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed (ModelTree)

local notation "K" => Kleisli.Adjunction.toKleisli (ofTypeMonad (ModelTree Events))
local notation "M" => ofTypeModel (Ty.denote (Lifted carriers : Unit → Type 1))

/-- The installed sound quotient interpretation gives equal typed
singleton observations in the coherent ITree Kleisli model. The
representatives from `Transfer.endpoint_transport` supply the equation. -/
theorem denote_eq_of_joined
    (coherent : letI := ofInstructionModel D instr; RegionTypingCoherent (Φ := Ops) K M)
    (pe : ε) {A B : Ty Unit} {r s : Region Ops}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B])
    (eq : Region.Paper.Extension.Eqv (targetSeed pe) [A] r s [B]) (input : D A) :
    let _ := ofInstructionModel D instr
    (denoteSingletonRegion K M hr.hasType).of input =
      (denoteSingletonRegion K M hs.hasType).of input :=
  Proofs.ITree.denote_eq_of_joined instr coherent pe hr hs eq input

end Joined

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport
