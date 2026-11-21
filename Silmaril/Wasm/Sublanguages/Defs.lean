module

public import Silmaril.Wasm.Profiles.Injections.Thms
public import Silmaril.Wasm.Profiles.Thms
public import Mathlib.CategoryTheory.Category.Basic

/-! Syntax over Core 3.0, independently of a feature set, binary grammar,
typing witness or execution policy. Native V2 syntax enters on the domain of
its ordinary (not binary-retagging) translations. -/

@[expose] public section

namespace Silmaril.Wasm.Sublanguages

open Profiles Profiles.Injections

/-- Chosen faithful images in the three Core syntax sorts. No claim about
reflection of typing or observations is part of a syntax embedding. -/
structure Language where
  Instruction : Type
  Function : Type
  Module : Type
  toInstr : Instruction ↪ Wasm.Instr
  toFunc : Function ↪ Wasm.Func
  toModule : Module ↪ Wasm.Module

/-- A syntax inclusion over Core: all three erasures commute exactly. -/
structure Inclusion (A B : Language) where
  instr : A.Instruction → B.Instruction
  func : A.Function → B.Function
  mod : A.Module → B.Module
  instr_comm : ∀ source, B.toInstr (instr source) = A.toInstr source
  func_comm : ∀ source, B.toFunc (func source) = A.toFunc source
  mod_comm : ∀ source, B.toModule (mod source) = A.toModule source

namespace Inclusion

variable {A B C : Language}

def identity (A : Language) : Inclusion A A := ⟨id, id, id, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

def comp (first : Inclusion A B) (second : Inclusion B C) : Inclusion A C :=
  ⟨second.instr ∘ first.instr, second.func ∘ first.func, second.mod ∘ first.mod,
    fun source => (second.instr_comm _).trans (first.instr_comm source),
    fun source => (second.func_comm _).trans (first.func_comm source),
    fun source => (second.mod_comm _).trans (first.mod_comm source)⟩

def modules (arrow : Inclusion A B) : A.Module ↪ B.Module :=
  ⟨arrow.mod, fun {left right} eq => A.toModule.injective
    ((arrow.mod_comm left).symm.trans ((congrArg B.toModule eq).trans (arrow.mod_comm right)))⟩

end Inclusion

instance : CategoryTheory.Category.{0} Language where
  Hom := Inclusion
  id := Inclusion.identity
  comp := Inclusion.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

def core : Language := ⟨Wasm.Instr, Wasm.Func, Wasm.Module, .refl _, .refl _, .refl _⟩

def Language.intoCore (language : Language) : Inclusion language core :=
  ⟨language.toInstr, language.toFunc, language.toModule, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

def wasm1 : Language := ⟨Instruction Wasm1, Function Wasm1, Profiles.Module Wasm1,
  ⟨V1.Instr.toCore, V1.Instr.toCore_injective⟩, wasm1ToWasm3Function, wasm1ToWasm3⟩

def lime : Language := ⟨Instruction Lime, Function Lime, Profiles.Module Lime,
  ⟨Lime1.Instr.toCore, Lime1.Instr.toCore_injective⟩, limeToWasm3Function, limeToWasm3⟩

def wasm2Instruction : PartialInjection (Instruction Wasm2) Wasm.Instr :=
  ⟨V2.Instr.toCore, V2.Instr.toCore_injective⟩

def wasm2 : Language := ⟨wasm2Instruction.Domain, wasm2ToWasm3Function.Domain, wasm2ToWasm3.Domain,
  wasm2Instruction.onDomain, wasm2ToWasm3Function.onDomain, wasm2ToWasm3.onDomain⟩

def functional (gc : GCMode) (exn : ExceptionMode) : Language := ⟨
  Instruction (FunctionalCore gc exn), Function (FunctionalCore gc exn), Profiles.Module (FunctionalCore gc exn),
  ⟨Subtype.val, fun {_ _} => Subtype.ext⟩, ⟨Subtype.val, fun {_ _} => Subtype.ext⟩,
  FunctionalCore.toCore gc exn⟩

/-- Relax the capabilities while retaining the same closed module shape. -/
def functionalOfLE {gc nextGC : GCMode} {exn nextExn : ExceptionMode}
    (le : FunctionalCore.features gc exn ≤ FunctionalCore.features nextGC nextExn) :
    Inclusion (functional gc exn) (functional nextGC nextExn) :=
  ⟨fun instr => ⟨instr.val, Models.inFeatB_mono le _ instr.property⟩,
    fun fn => ⟨fn.val, Models.func_mono le _ fn.property⟩,
    FunctionalCore.ofLE le, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

def strictIntoFunctional : Inclusion (functional .immutable .disabled) (functional .mutable .internal) :=
  functionalOfLE ((FunctionalCore.mutation_le .disabled).trans
    (Models.remove_le (FunctionalCore.features .mutable .internal) .exn))

def wasm1IntoLime : Inclusion wasm1 lime :=
  ⟨V1.Instr.toLime, wasm1ToLimeFunction, wasm1ToLime,
    V1.Instr.toLime_toCore, V1.Func.toLime_toCore, wasm1_core_via_lime⟩

def imageMember {Source Target : Type} (arrow : PartialInjection Source Target)
    (source : Source) {image : Target} (eq : arrow.run source = some image) : arrow.Domain :=
  ⟨source, Option.isSome_iff_exists.mpr ⟨image, eq⟩⟩

theorem imageMember_image {Source Target : Type} (arrow : PartialInjection Source Target)
    {source : Source} {image : Target} (eq : arrow.run source = some image) :
    arrow.onDomain (imageMember arrow source eq) = image :=
  Option.some.inj ((arrow.onDomain_spec _).symm.trans eq)

def limeIntoWasm2 : Inclusion lime wasm2 :=
  ⟨fun instr => imageMember wasm2Instruction instr.toV2 (Lime1.Instr.toV2_toCore instr),
    fun fn => imageMember wasm2ToWasm3Function fn.toV2 (Lime1.Func.toV2_toCore fn),
    fun mod => imageMember wasm2ToWasm3 mod.toV2 (Lime1.Module.toV2_toCore mod),
    fun instr => imageMember_image wasm2Instruction (Lime1.Instr.toV2_toCore instr),
    fun fn => imageMember_image wasm2ToWasm3Function (Lime1.Func.toV2_toCore fn),
    fun mod => imageMember_image wasm2ToWasm3 (Lime1.Module.toV2_toCore mod)⟩

/-- Capability admission is evaluated on the exact Core image. This is not
native validation and does not test policy or binary representations. -/
def Language.Admits (language : Language) (caps : Models.FeatureSet) (mod : language.Module) : Prop :=
  Models.Module.InFeat caps (language.toModule mod)

def Language.admittedImage (language : Language) (caps : Models.FeatureSet) : Set Wasm.Module :=
  { coreMod | ∃ mod, language.Admits caps mod ∧ language.toModule mod = coreMod }

end Silmaril.Wasm.Sublanguages
