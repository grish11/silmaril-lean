module

public import Silmaril.Wasm.Validation.Generic.SSA.Defs
public import Silmaril.Wasm.Validation.Generic.Thms
public import Silmaril.Wasm.Validation.Generic.Signature.Thms
import Silmaril.Proofs.Wasm.Validation.Generic.SSA

@[expose] public section

namespace Silmaril.Wasm.Generic.SSA

open Silmaril.Isotope.LambdaSSA
open Validation

variable {Φ τ σ : Type} [TypeFormers τ] [TypeFormers σ] [HasTy Φ τ] [HasTy Φ σ]

theorem TypeMap.region (f : TypeMap Φ τ σ) {values labels : List τ} {region : Region Φ}
    (valid : region.HasType values labels) : region.HasType (values.map f.run) (labels.map f.run) :=
  Proofs.Wasm.Validation.Generic.SSA.mapRegion f valid

def TypeMap.declared (f : TypeMap Φ τ σ) {sourceTrap : τ} {targetTrap : σ}
    (trap : f.run sourceTrap = targetTrap) {sig : Signature.Func τ}
    (body : DeclaredBody Φ sourceTrap sig) : DeclaredBody Φ targetTrap (sig.map f.run) :=
  ⟨body.val, by simpa only [Signature.Func.map, List.map_reverse, List.map_cons, List.map_nil, trap]
    using f.region body.property⟩

/-- Specialization can emit syntax or run a partial lowering. In either case
the retyped declaration encodes the same signature and supplies the same code. -/
theorem TypeMap.declared_specialize (f : TypeMap Φ τ σ) {sourceTrap : τ} {targetTrap : σ}
    (trap : f.run sourceTrap = targetTrap) (source : Signature.Encoding τ) (target : Signature.Encoding σ)
    (args : ∀ type, target.arg (f.run type) = source.arg type)
    (results : ∀ type, target.result (f.run type) = source.result type) {Out : Type}
    (emit : TypeIdx → FuncType → Region Φ → Option (List ValType × Out))
    (mod : Signature.Module (DeclaredBody Φ sourceTrap)) :
    (mod.map f.run (f.declared trap)).specialize? target (fun index sig body => emit index sig body.val) =
      mod.specialize? source (fun index sig body => emit index sig body.val) :=
  Signature.Module.specialize_map f.run (f.declared trap) source target _ _
    (Signature.Func.encode_map f.run source target args results) (fun _ _ _ => rfl) mod

theorem TypeMap.term (f : TypeMap Φ τ σ) {values : List τ} {term : Tm Φ} {type : τ}
    (valid : term.HasType values type) : term.HasType (values.map f.run) (f.run type) :=
  Proofs.Wasm.Validation.Generic.SSA.mapTm f valid

structure BoundaryMap (f : TypeMap Φ τ σ) (source : Boundary τ) (target : Boundary σ) : Prop where
  args : ∀ type, target.arg (f.run type) = source.arg type
  result : ∀ type, target.result (f.run type) = source.result type
  trap : f.run source.trap = target.trap

theorem BoundaryMap.mapArgs {f : TypeMap Φ τ σ} {source : Boundary τ} {target : Boundary σ}
    (map : BoundaryMap f source target) (params : List τ) :
    (params.map f.run).mapM target.arg = params.mapM source.arg :=
  Proofs.Wasm.Validation.Generic.SSA.mapArgs f.run map.args params

/-- Change the SSA types, not the Core declaration or the region's syntax. -/
def AtCore.retype {f : TypeMap Φ τ σ} {source : Boundary τ} {target : Boundary σ}
    (map : BoundaryMap f source target) {context : Context} {signature : DefType}
    (fn : AtCore Φ τ source context signature) : AtCore Φ σ target context signature where
  typeRef := fn.typeRef
  params := fn.params.map f.run
  result := f.run fn.result
  coreParams := fn.coreParams
  coreResults := fn.coreResults
  paramsOk := (map.mapArgs fn.params).trans fn.paramsOk
  resultOk := (map.result fn.result).trans fn.resultOk
  signatureOk := fn.signatureOk
  code := fn.code
  typed := by simpa only [List.map_reverse, List.map_cons, List.map_nil, map.trap] using f.region fn.typed

@[simp] theorem AtCore.retype_syntax {f : TypeMap Φ τ σ} {source : Boundary τ} {target : Boundary σ}
    (map : BoundaryMap f source target) {context : Context} {signature : DefType}
    (fn : AtCore Φ τ source context signature) : (fn.retype map).syntax = fn.syntax := rfl

/-- The specialization square includes the whole typed module; headers and
non-body sections are kept by the existing dependent map. -/
theorem retype_module_syntax {f : TypeMap Φ τ σ} {source : Boundary τ} {target : Boundary σ}
    (map : BoundaryMap f source target) {interface : CModuleType}
    (mod : Typed.Module (AtCore Φ τ source) interface) :
    (mod.map (AtCore.retype map)).forget AtCore.syntax = mod.forget AtCore.syntax :=
  Typed.Module.forget_map (AtCore.retype map) AtCore.syntax mod

theorem AtCore.retype_roundtrip {f : TypeMap Φ τ σ} {g : TypeMap Φ σ τ}
    {source : Boundary τ} {target : Boundary σ} (go : BoundaryMap f source target)
    (back : BoundaryMap g target source) (inverse : ∀ type, g.run (f.run type) = type)
    {context : Context} {signature : DefType} (fn : AtCore Φ τ source context signature) :
    (fn.retype go).retype back = fn := by
  cases fn
  simp only [retype, List.map_map, Function.comp_def, inverse, List.map_id']

theorem retype_module_roundtrip {f : TypeMap Φ τ σ} {g : TypeMap Φ σ τ}
    {source : Boundary τ} {target : Boundary σ} (go : BoundaryMap f source target)
    (back : BoundaryMap g target source) (inverse : ∀ type, g.run (f.run type) = type)
    {interface : CModuleType} (mod : Typed.Module (AtCore Φ τ source) interface) :
    (mod.map (AtCore.retype go)).map (AtCore.retype back) = mod := by
  have same : (fun {context signature} (fn : AtCore Φ τ source context signature) =>
      (fn.retype go).retype back) = (fun {_ _} fn => fn) := by
    funext
    apply AtCore.retype_roundtrip go back inverse
  rw [Typed.Module.map_comp, same, Typed.Module.map_id]

end Silmaril.Wasm.Generic.SSA
