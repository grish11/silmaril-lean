module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Institution.Defs
import Silmaril.SSA.LambdaRTL.CFG.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry

open CategoryTheory
open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive region)
open LambdaSSA.Semantics.Interaction.Typed
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)

universe u v
variable {κ : Type (u + 1)} {V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P Q S : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}

private theorem ssa_ext {a b : SSA P I} (hs : a.source = b.source) (ht : a.table = b.table) :
    a = b := by
  cases a
  cases b
  cases hs
  cases ht
  rfl

theorem ssa_map_id (a : SSA P I) : a.map (𝟙 P) = a :=
  ssa_ext (CFG.mapOp_id a.source) (EntryInstitution.Table.map_id a.table)

theorem ssa_map_comp (f : P ⟶ Q) (g : Q ⟶ S) (a : SSA P I) :
    a.map (f ≫ g) = (a.map f).map g :=
  ssa_ext (CFG.mapOp_comp f.toSignatureMap.instr g.toSignatureMap.instr a.source)
    (EntryInstitution.Table.map_comp f g a.table)

private theorem rtl_ext {a b : RTL P I} (hs : a.source = b.source)
    (hv : a.versioned = b.versioned) : a = b := by
  cases a
  cases b
  cases hs
  cases hv
  rfl

theorem rtl_map_id (a : RTL P I) : a.map (𝟙 P) = a :=
  rtl_ext (CFG.mapOp_id a.source) (ssa_map_id a.versioned)

theorem rtl_map_comp (f : P ⟶ Q) (g : Q ⟶ S) (a : RTL P I) :
    a.map (f ≫ g) = (a.map f).map g :=
  rtl_ext (CFG.mapOp_comp f.toSignatureMap.instr g.toSignatureMap.instr a.source)
    (ssa_map_comp f g a.versioned)

variable [AtomValues κ] {Events : Type u → Type u}

local notation "A" => Region.packedInputType I.context.toList
local notation "C" => AtomValues.carrier (κ := κ)

private theorem admitted_run_tree (raw : Primitive Events P.Instr (Sigma C))
    (source : CFG V K P.Instr) (count : Nat) (len : source.blocks.length = count)
    (code : FiniteCFG P.Instr count I.exits.length I.slots)
    (accepted : elaborateAt source I.exits I.names count len = some code)
    (x : Ty.denote C A) :
    (CFG.Cyclic.runSSA (treeModel raw) source (store I.names I.context x) >>=
      fun p => pure (treeExitNumber I.exits p)) =
      region raw (inputEnv I.context x) code.erase := by
  subst count
  rw [elaborateAt_eq] at accepted
  exact run_tree raw source I.exits I.names accepted _ _ fun i =>
    (store_at I.names I.distinct I.context x i).symm

theorem ssa_observe_tree (M : Model (κ := κ) Events P.Instr) (a : SSA P I)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    a.observe M x = region M.raw (extend ambient (encodeValue C A x))
      (Program.ofCFGEntry a.table.typed).code := by
  rw [← inputEnv_packet]
  change a.observe M x =
    region M.raw (extend ambient (Capture.packEnv I.slots (inputEnv I.context x)))
      ((FiniteCFG.packedExecutionRegion a.table.typed).packInputsDestructure I.context.toList)
  rw [Capture.packed_context_tree, ← admitted_run_tree M.raw a.source a.table.blocks a.count
    a.table.code a.accepted x, bind_assoc]
  simp only [SSA.observe, pure_bind]

theorem rtl_observe_version (M : Model (κ := κ) Events P.Instr) (a : RTL P I)
    (x : Ty.denote C A) : a.observe M x = a.versioned.observe M x := by
  let inputs := store I.version.names I.context x
  have store_eq : (fun name => inputs (name, 0)) = store I.names I.context x :=
    funext (store_version_zero I.names I.context x)
  have run := CFG.Cyclic.Versioning.run_commutes (treeModel M.raw) ⟨fun _ _ => rfl⟩ a.source inputs
  rw [store_eq] at run
  let ret := fun p : K × Value (Sigma C) => pure (f := ModelTree Events)
    (FiniteCFG.packedTreeOutput (treeExitNumber I.exits p))
  calc
    _ = ((obs <$> CFG.Cyclic.run (treeModel M.raw) a.source (store I.names I.context x)) >>= ret) := by
      simp only [RTL.observe, ret, map_eq_pure_bind, bind_assoc, pure_bind]
    _ = (CFG.Cyclic.runSSA (treeModel M.raw) (CFG.Cyclic.Versioning.compile a.source) inputs >>= ret) :=
      congrArg (fun t => t >>= ret) run
    _ = _ := congrArg (fun g => CFG.Cyclic.runSSA (treeModel M.raw) g inputs >>= ret) a.compiled.symm

theorem toFlat_satisfies_iff (M : Model (κ := κ) Events P.Instr) (s : SSASentence P I) :
    EntryInstitution.Satisfies Events M (toFlat s) ↔ ssaSatisfies M s := by
  let ambient : Env (Sigma C) := fun _ => .unit
  change M.Satisfies (Program.ofCFGEntry s.1.table.typed) (Program.ofCFGEntry s.2.table.typed) ↔ _
  rw [satisfies_ofCFGEntry_iff _ _ _ ambient]
  exact forall_congr' fun x => by rw [ssa_observe_tree M s.1 x ambient, ssa_observe_tree M s.2 x ambient]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry
