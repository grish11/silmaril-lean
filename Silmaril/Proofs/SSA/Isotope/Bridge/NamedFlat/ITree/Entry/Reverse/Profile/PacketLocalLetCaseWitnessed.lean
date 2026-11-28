module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Tree.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Witnessed.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Acyclic
open LambdaSSA.Acyclic.Positional.Capture.Reverse
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region term)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue encodeValue_injective)
open Morphism.CaseSSA (erase)
open Silmaril.Elgot.ITree (TraceLE eq_iff_traceLE)
open scoped Silmaril.Elgot.ITree.WeakKleisli

universe u v

variable {κ K : Type (u + 1)} [DecidableEq K] {n : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)} [AtomValues κ] {Events : Type u → Type u}

local notation "ports" => numberedInterface context exits external
local notation "exitTypes" => Interface.external (LiveOut.exitInterface ports fields)
local notation "A" => Region.packedInputType context.toList
local notation "exitList" => List.ofFn exitTypes
local notation "B" => Region.packedExitType exitList
local notation "C" => AtomValues.carrier (κ := κ)

variable {source : Operand P.Instr context (Region.packedExitType
    (List.ofFn (LiveOut.exitInterface (numberedInterface context exits external) fields).external))} {g : ResultGrammar source}

omit [DecidableEq K] [AtomValues κ] in
theorem flatList_hasType (g : ResultGrammar source) (slots : List (Fin n)) :
    (flatList g slots).HasType context (packetTypesList g slots) exitTypes :=
  Capture.Carry.graphList_hasType g.toTable.toFlat_hasType slots

omit [DecidableEq K] in
private theorem flat_region (g : ResultGrammar source) (slots : List (Fin n)) (M : Model (κ := κ) Events P.Instr)
    (env : Env (Sigma C)) :
    region M.raw env (flatList g slots).erase =
      region M.raw env (g.toTable.toFlat (exits := exits.length) List.length_ofFn).erase :=
  Capture.Carry.graphList_tree M.raw _ slots env

omit [DecidableEq K] in
private theorem packedFlat_tree {blocks : Nat} {code : FiniteCFG P.Instr blocks exits.length n}
    {R : Fin blocks → Ty κ} (typed : code.HasType context R exitTypes)
    (M : Model (κ := κ) Events P.Instr) (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      (region M.raw (inputEnv context x) code.erase >>= fun p => pure (FiniteCFG.packedTreeOutput p)) := by
  rw [← inputEnv_packet]
  exact Capture.packed_context_tree M.raw typed ambient _

theorem named_tree {slots : List (Fin n)} (M : Model (κ := κ) Events P.Instr)
    (c : CompiledList g slots) (x : Record.Input context) :
    (sourceTree M source x >>= fun b => pure (0, encodeValue C B b)) =
      LiveOut.observe M ports fields c.lowered.source x := by
  let env := inputEnv context x
  let ambient : Env (Sigma C) := fun _ => .unit
  let typed := flatList_hasType g slots
  have native :
      (sourceTree M source x >>= fun b => pure (encodeValue C B b)) =
        term M.raw env (erase source.1) :=
    FlatLetCase.denote_tree ⟨M.instructions.denote⟩ M.raw M.compatible source.2 _ _
      (Record.inputEnv_field context x)
  have packed :
      region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
        (region M.raw env (flatList g slots).erase >>= fun p => pure (FiniteCFG.packedTreeOutput p)) :=
    packedFlat_tree typed M x ambient
  calc
    _ = (term M.raw env (erase source.1) >>= fun b => pure (0, b)) := by
      rw [← native, bind_assoc]
      simp only [pure_bind]
    _ = region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code := by
      rw [g.flat_tree (exits := exits.length) List.length_ofFn, packed, flat_region, bind_assoc]
      simp only [pure_bind, FiniteCFG.packedTreeOutput]
    _ = _ := c.lowered.packed_observe M typed x ambient

theorem packed_eq {slots : List (Fin n)} (M : Model (κ := κ) Events P.Instr) (c : CompiledList g slots) :
    (Program.ofCFGEntry (g.toTable.toFlat_hasType (D := exitTypes))).denote M = c.admission.program.denote M := by
  let ambient : Env (Sigma C) := fun _ => .unit
  have compare (x : Record.Input context) :
      region M.raw (extend ambient (encodeValue C A x))
        (Program.ofCFGEntry (g.toTable.toFlat_hasType (D := exitTypes))).code =
      region M.raw (extend ambient (encodeValue C A x)) c.admission.program.code := by
    refine Eq.trans ?_ (c.admission.packed_roundTrip M (flatList_hasType g slots) x ambient)
    let env := inputEnv context x
    let original := g.toTable.toFlat_hasType (D := exitTypes)
    let emitted := flatList_hasType g slots
    have originalTree :
        region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry original).code =
          (region M.raw env (g.toTable.toFlat (exits := exits.length) List.length_ofFn).erase >>=
            fun p => pure (FiniteCFG.packedTreeOutput p)) :=
      packedFlat_tree original M x ambient
    have emittedTree :
        region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry emitted).code =
          (region M.raw env (flatList g slots).erase >>= fun p => pure (FiniteCFG.packedTreeOutput p)) :=
      packedFlat_tree emitted M x ambient
    exact originalTree.trans ((emittedTree.trans
      (congrArg (fun t => t >>= fun p => pure (FiniteCFG.packedTreeOutput p))
        (flat_region g slots M env))).symm)
  rw [le_antisymm_iff, denote_le_iff M M _ _ ambient, denote_le_iff M M _ _ ambient]
  exact ⟨fun x => (eq_iff_traceLE.mp (compare x)).1, fun x => (eq_iff_traceLE.mp (compare x)).2⟩

section Equation

open Silmaril.Isotope.Institution.LetCase.WeakITree

variable {P : FlatInstitution.Signature.{u, u+1} κ}
  {source : Operand P.Instr context (Region.packedExitType
    (List.ofFn (LiveOut.exitInterface (numberedInterface context exits external) fields).external))} {g : ResultGrammar source}

theorem satisfies {slots : List (Fin n)} (M : Model (κ := κ) Events P.Instr) (c : CompiledList g slots) :
    (equationRoom P).Sat (algebra (P := P) M) c.equation := by
  apply (Silmaril.Isotope.Institution.LetCase.sat_iff (emptyContext (κ := κ)) (signature P)
    (algebra (P := P) M) (closedOperand (P := P) source.2).2
    (closedOperand (P := P) (c.admission.letCase c.ranked).2).2).2
  funext env
  obtain ⟨x, rfl⟩ := Record.field_surjective context env
  rw [denote_closedOperand, denote_closedOperand]
  change sourceTree M source x = c.admission.letCaseTree M c.ranked x
  let tag := fun b => ((0 : Nat), encodeValue C B b)
  have injective : Function.Injective tag :=
    fun _ _ eq => encodeValue_injective C B (congrArg Prod.snd eq)
  have encoded :
      (sourceTree M source x >>= fun b => pure (tag b)) =
      (c.admission.letCaseTree M c.ranked x >>= fun b => pure (tag b)) :=
    (named_tree M c x).trans (c.admission.letCase_observe M c.ranked x (fun _ => .unit)).symm
  have traces := eq_iff_traceLE.mp encoded
  exact ((TraceLE.bind_pure_iff injective).mp traces.1).antisymm
    ((TraceLE.bind_pure_iff injective).mp traces.2)

end Equation
end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed
