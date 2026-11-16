module

public import Silmaril.Logic.Modal.Thms
public import Silmaril.Wasm.Execution.Core.Step

@[expose] public section

/-! Modal observations of actual pinned Wasm Core steps. Native truth is defined
recursively here, independently of the Kripke interpretation used for comparison. -/
namespace Silmaril.Logic.Modal.Wasm
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type}

/-- The frame is fixed by actual execution; only observations and the point vary. -/
structure Model (P : Profile) (host : HostSemantics H) (S : Modal.Signature) : Type 1 where
  valuation : S.Atom → Config H → Prop
  point : Config H

variable {P : Profile} {host : HostSemantics H} {S T : Modal.Signature}

/-- Direct one-step observations. Box quantifies over every actual successor. -/
def Holds (M : Model P host S) : Modal.Formula S → Config H → Prop
  | .atom a, c => M.valuation a c
  | .bot, _ => False
  | .imp p q, c => Holds M p c → Holds M q c
  | .box p, c => ∀ d, Step P host c d → Holds M p d

def Sat (M : Model P host S) (p : Modal.Formula S) : Prop := Holds M p M.point

/-- Forget the operational presentation without changing states, steps or atoms. -/
def toModal (M : Model P host S) : Modal.Model S :=
  ⟨Config H, Step P host, M.valuation, M.point⟩

/-- Full bounded morphisms, including successor lifting (back), are retained. -/
instance : Category (Model P host S) where
  Hom M N := Modal.Model.Hom (toModal M) (toModal N)
  id M := 𝟙 (toModal M)
  comp {M _ N} f g := (show toModal M ⟶ toModal N from f ≫ g)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The comparison is functorial on all bounded morphisms, not just identities. -/
def modalModels (P : Profile) (host : HostSemantics H) (S : Modal.Signature) :
    Model P host S ⥤ Modal.Model S where
  obj := toModal
  map h := h
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Atom renaming leaves the actual execution frame and point fixed. -/
def reduct (f : S ⟶ T) : Model P host T ⥤ Model P host S where
  obj M := ⟨fun a => M.valuation (f a), M.point⟩
  map h := ⟨h.map, h.point, fun a c => h.atoms (f a) c, h.forth, h.back⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Diamond is the ordinary classical abbreviation ¬□¬, using the same syntax. -/
def diamond (p : Modal.Formula S) : Modal.Formula S :=
  .imp (.box (.imp p .bot)) .bot

end Silmaril.Logic.Modal.Wasm
