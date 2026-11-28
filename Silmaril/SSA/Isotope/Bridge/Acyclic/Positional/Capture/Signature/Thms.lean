module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Signature.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Signature.Relabel
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Signature.Render

/-! # Signature laws for captured table and grammar relabelling -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open Morphism (SignatureMap)
open Institution (InstrSig)
open Reverse

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ) [h.PreservesProducts] [h.PreservesSums]
  {d n : Nat} {β : BoundCtx τ d} {L : LCtx τ}

theorem Table.localTargets_mapSignature (p : Table P.Instr β L n) :
    (p.mapSignature g).localTargets = p.localTargets :=
  table_mapSignature_localTargets g p

@[simp] theorem Table.check_mapSignature (p : Table P.Instr β L n) :
    (p.mapSignature g).check = p.check :=
  congrArg Rank.check (p.localTargets_mapSignature g)

/-- Relabelling the actual native CFG changes only its primitive instructions. -/
theorem Table.toSSA_mapSignature (p : Table P.Instr β L n) (i : Fin (n + 1))
    (a : Operand P.Instr β (p.types i)) :
    (p.mapSignature g).toSSA i (a.mapSignature g) = (p.toSSA i a).mapInstr g.instr :=
  native_mapSignature g p i a

theorem Table.mapSignature_id_heq (p : Table P.Instr β L n) :
    HEq (p.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) p :=
  table_mapSignature_id p

theorem Table.mapSignature_comp_heq (p : Table P.Instr β L n) :
    HEq (p.mapSignature (h.comp g)) ((p.mapSignature g).mapSignature h) :=
  table_mapSignature_comp g h p

theorem Reverse.Program.mapSignature_id_heq (p : Program P.Instr β L) :
    HEq (p.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) p :=
  program_mapSignature_id p

theorem Reverse.Program.mapSignature_comp_heq (p : Program P.Instr β L) :
    HEq (p.mapSignature (h.comp g)) ((p.mapSignature g).mapSignature h) :=
  program_mapSignature_comp g h p

/-- Reading the grammar commutes exactly with relabelling, even when the
rank proofs of the two tables are supplied independently. -/
theorem Reverse.tableProgram_mapSignature (p : Table P.Instr β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand P.Instr β (p.types i)) (ok' : (p.mapSignature g).check = true) :
    tableProgram (p.mapSignature g) ok' i (a.mapSignature g) = (tableProgram p ok i a).mapSignature g :=
  tableProgram_map g p ok i a ok'

/-- Rendering the mapped grammar commutes exactly with the typed finite-exit map. -/
theorem Reverse.Program.toFiniteExit_mapSignature (p : Program P.Instr β L) :
    (p.mapSignature g).toFiniteExit = p.toFiniteExit.mapSignature g :=
  program_render_map g p

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
