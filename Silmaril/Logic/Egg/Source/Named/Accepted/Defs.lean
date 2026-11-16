module

public import Silmaril.Logic.Egg.Source.Named.Parser.Defs
public import Silmaril.Logic.Egg.Source.Named.Resolution.Thms
public import Silmaril.Logic.Egglog.Source.Named.Accepted.Thms

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named

/-- The entire original file and its exact executable boundaries are retained. -/
structure AcceptedProgram (D : Declarations) where
  bytes : List UInt8
  raw : RawProgram
  read_eq : Parser.readProgram bytes = some raw
  resolved : List (Core.Rule D.signature)
  resolve_eq : resolveProgram? D raw = some resolved

def AcceptedProgram.Holds {D : Declarations} (p : AcceptedProgram D)
    (M : Core.Model D.signature) : Prop := p.raw.Holds M

def acceptSupplied? (D : Declarations) (bytes : List UInt8) : Option (AcceptedProgram D) :=
  match hr : Parser.readProgram bytes with
  | none => none
  | some raw =>
      match hc : resolveProgram? D raw with
      | none => none
      | some resolved => some ⟨bytes, raw, hr, resolved, hc⟩

/-- Inferred admission records the computation, not merely a chosen vocabulary. -/
structure AcceptedInferredProgram where
  declarations : Declarations
  program : AcceptedProgram declarations
  infer_eq : inferDeclarations? program.raw = some declarations

def acceptInferred? (bytes : List UInt8) : Option AcceptedInferredProgram :=
  match hr : Parser.readProgram bytes with
  | none => none
  | some raw =>
      match hd : inferDeclarations? raw with
      | none => none
      | some D =>
          match hc : resolveProgram? D raw with
          | none => none
          | some rules => some ⟨D, ⟨bytes, raw, hr, rules, hc⟩, hd⟩

theorem AcceptedProgram.mapM_eq {D : Declarations} (p : AcceptedProgram D) :
    p.raw.mapM (resolveRule? D) = some p.resolved := by
  have success := p.resolve_eq
  unfold resolveProgram? at success
  split at success
  · exact success
  · contradiction

theorem AcceptedProgram.resolved_holds {D : Declarations} (p : AcceptedProgram D)
    (M : Core.Model D.signature) : p.Holds M ↔ ∀ r ∈ p.resolved, r.Holds M :=
  resolveProgram_holds_iff D p.raw p.resolved p.resolve_eq M

/-- Entry APIs retain the complete source file rather than synthetic rule bytes. -/
structure ProgramEntry (D : Declarations) where
  program : AcceptedProgram D
  index : Fin program.raw.length

def ProgramEntry.raw {D : Declarations} (e : ProgramEntry D) : RawRule :=
  e.program.raw.get e.index

def ProgramEntry.compiledIndex {D : Declarations} (e : ProgramEntry D) :
    Fin e.program.resolved.length :=
  Fin.cast (Silmaril.Logic.Egglog.Source.Named.mapM_length _ _ _ e.program.mapM_eq) e.index

def ProgramEntry.resolved {D : Declarations} (e : ProgramEntry D) : Core.Rule D.signature :=
  e.program.resolved.get e.compiledIndex

theorem ProgramEntry.resolve_eq {D : Declarations} (e : ProgramEntry D) :
    resolveRule? D e.raw = some e.resolved :=
  Silmaril.Logic.Egglog.Source.Named.mapM_get _ _ _ e.program.mapM_eq e.index

end Silmaril.Logic.Egg.Source.Named
