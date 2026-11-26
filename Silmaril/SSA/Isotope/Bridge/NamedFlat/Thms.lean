module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Semantics.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Typing.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Semantics
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Typing

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open LambdaSSA.Semantics (Env extend)

universe u v
variable {V K : Type u} {F : Type v} {n : Nat} [DecidableEq V] [DecidableEq K]

/-- The boolean checker certifies exact Isotope typing. -/
theorem check_sound {Base : Type u} [DecidableEq Base] [HasTy F (Ty Base)]
    {blocks exits : Nat} (graph : LambdaSSA.FiniteCFG F blocks exits n)
    (captures : BoundCtx (Ty Base) n) (internal : Fin blocks → Ty Base)
    (external : Fin exits → Ty Base) (accepted : check graph captures internal external = true) :
    graph.HasType captures internal external :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.check_sound graph captures internal external accepted

/-- Elaborate the generated named graph and check the supplied exact profile.
The result carries the elaboration equation and the erased typing proof. -/
def compileTyped {Base : Type u} [DecidableEq Base] [HasTy F (Ty Base)]
    (source : CFG V K F) (exits : List K) (captures : Fin n → V)
    (captureTypes : BoundCtx (Ty Base) n)
    (internal : Fin (CFG.Cyclic.Versioning.compile source).blocks.length → Ty Base)
    (external : Fin exits.length → Ty Base) :
    Option {g : LambdaSSA.FiniteCFG F (CFG.Cyclic.Versioning.compile source).blocks.length
      exits.length n // compile source exits captures = some g ∧
        g.HasType captureTypes internal external} :=
  match compile source exits captures with
  | none => none
  | some graph =>
      if accepted : check graph captureTypes internal external = true then
        some ⟨graph, rfl, check_sound graph captureTypes internal external accepted⟩
      else none

variable {G α : Type u}

/-- After numbering labels, finite named entry results agree with the erased
Isotope entry. The two input environments agree on the supplied captures. -/
theorem entry_iff (prim : G → Value α → Part (Value α))
    (graph : CFG V K G) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG G graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (store : V → Value α) (env : Env α)
    (inputs : ∀ i : Fin n, env i.val = store (captures i)) (out : Nat) (result : Value α) :
    (out, result) ∈ (graph.entry.evalJump (model prim) store >>= number (labelIndex graph.blocks exits)) ↔
      LambdaSSA.Semantics.Region.Eval (instr prim) env target.entry.erase () out result () :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.entry_iff prim graph exits captures accepted
    store env inputs out result

/-- At an internal first-match lookup, the continuing result of a named cyclic
lexical step agrees with the indexed Isotope block's finite result. The block
can use its packet argument and locals, so it needs no capture agreement. -/
theorem step_iff (prim : G → Value α → Part (Value α))
    (graph : CFG V K G) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG G graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (label : K) (i : Fin graph.blocks.length)
    (hit : graph.blocks.findFinIdx? (fun item => label == item.1) = some i)
    (store : V → Value α) (env : Env α) (payload : Value α) (out : Nat) (result : Value α) :
    (out, result) ∈ (CFG.Cyclic.stepSSA (model prim) graph.blocks store (label, payload) >>=
      Sum.elim (fun _ => Part.none) (number (labelIndex graph.blocks exits))) ↔
      LambdaSSA.Semantics.Region.Eval (instr prim) (extend env payload)
        (target.block i).erase () out result () :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.step_iff prim graph exits captures accepted
    label i hit store env payload out result

end Silmaril.Isotope.Bridge.NamedFlat
