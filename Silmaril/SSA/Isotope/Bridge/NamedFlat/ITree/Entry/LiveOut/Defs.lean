module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Institution.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.Thms

/-! # Admit an exact typed projection of the mutable exit store -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v

/-- Field order is the supplied list order. The record is right nested and
terminates in unit, as in the versioner's own store packets. -/
def recordType {V : Type u} {κ : Type v} : List (V × Ty κ) → Ty κ
  | [] => .unit
  | (_, A) :: rest => .product A (recordType rest)

variable {κ V K : Type (u + 1)} {P : FlatInstitution.Signature.{u, v} κ}

/-- The input context and exit order are the original ones. Each exit now
returns its old argument and the typed record specified for that label. -/
def exitInterface (I : Interface κ V K) (fields : K → List (V × Ty κ)) : Interface κ V K :=
  { I with external := fun i => .product (I.external i) (recordType (fields I.exits[i])) }

variable [DecidableEq V] [DecidableEq K]

/-- Admission records the actual typed versioned elaboration of the source
with explicit store reads at its external branches. -/
structure Admission (P : FlatInstitution.Signature.{u, v} κ) (I : Interface κ V K)
    (fields : K → List (V × Ty κ)) (source : CFG V K P.Instr) where
  rtl : RTL P (exitInterface I fields)
  attached : rtl.source = CFG.Cyclic.LiveOut.attach (fun k => (fields k).map Prod.fst) source

/-- Use the ordinary typed checker at the enlarged exit profile and the
supplied internal block profiles. Failure remains explicit. -/
def admit [DecidableEq κ] (I : Interface κ V K) (fields : K → List (V × Ty κ))
    (source : CFG V K P.Instr)
    (internal : Fin (CFG.Cyclic.Versioning.compile
      (CFG.Cyclic.LiveOut.attach (fun k => (fields k).map Prod.fst) source)).blocks.length → Ty κ) :
    Option (Admission P I fields source) :=
  let attached := CFG.Cyclic.LiveOut.attach (fun k => (fields k).map Prod.fst) source
  match h : RTL.admit (I := exitInterface I fields) attached internal with
  | none => none
  | some rtl =>
    some ⟨rtl, by
      unfold RTL.admit at h
      obtain ⟨_, _, eq⟩ := Option.map_eq_some_iff.mp h
      exact congrArg RTL.source eq.symm⟩

variable {I : Interface κ V K} {fields : K → List (V × Ty κ)} {source : CFG V K P.Instr}

local notation "A" => Region.packedInputType I.context.toList
local notation "B" => Region.packedExitType (List.ofFn (Interface.external (exitInterface I fields)))

/-- Use the existing typed execution of the actual open flat CFG. -/
def Admission.program (a : Admission P I fields source) : Program P.Instr A B :=
  Program.ofCFGEntry a.rtl.versioned.table.typed

/-- Run the original mutable table with an explicit initial store and observe
its ordered exit, payload, and selected live-outs. -/
noncomputable def observeRaw {Events : Type u → Type u} {F : Type v} {α : Type (u + 1)}
    (instr : Primitive Events F α) (exits : List K) (fields : K → List V)
    (source : CFG V K F) (input : V → Value α) : ModelTree Events (Transfer α) :=
  let model := treeModel instr
  CFG.Cyclic.run model source input >>= fun final =>
    pure (FiniteCFG.packedTreeOutput (treeExitNumber exits (obs (CFG.Cyclic.LiveOut.project model fields final))))

variable [AtomValues κ] {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)

/-- Run the original mutable program on the supplied record and observe
its old payload and the selected fields of the actual final store. -/
noncomputable def observe (M : Model (κ := κ) Events P.Instr) (I : Interface κ V K)
    (fields : K → List (V × Ty κ)) (source : CFG V K P.Instr)
    (x : Ty.denote C (Region.packedInputType I.context.toList)) :
    ModelTree Events (Transfer (Sigma C)) :=
  observeRaw M.raw I.exits (fun k => (fields k).map Prod.fst) source (store I.names I.context x)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut
