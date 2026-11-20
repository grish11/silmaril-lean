module

public import Silmaril.Wasm.Game.HandleAccept.Parse.Defs
public import Silmaril.Semantics.Accept.Mixed.Defs

/-!
# Parsers that build their trees: mixed writer and parsing plays of core Wasm modules

A module that **parses through exports and builds through writer imports** (for instance
`parse(x : i64) -> i32` calling `word`, `nil`, `cons`) is read with the mixed events
`Silmaril.Accept.Mixed.MEv` of its instance plays, per move:

* an export call `.inr (.ask _)` is the export-call boundary `.w .enter`;
* an import call `.inl (.ask e)` is decoded by the writer decoder `dAsk` (`accept(h)`, …);
* an import answer `.inl (.ans e v)` is decoded by the writer decoder `dAns` (a write
  `word(x) = r`, `cons(a, b) = r`, …);
* an export answer `.inr (.ans f v)` is decoded by the parsing decoder `pdec`
  (`Silmaril.Wasm.Game.HandleAccept.Parsing.parseDec`: `parse(v) = h`, …).

`mixedEvents dAsk dAns pdec p` is the decoded trace of a play, `mixedTraces` those of a strategy.
For the cons writer API (`Silmaril.Wasm.Game.HandleAccept.Writers.ConsWImports`) and the parsing
exports `ParseExports`, `moduleMixedRel P m wix pix pol ppol` is the input/tree relation of the
instance in the store semantics (a returned handle resolves in the store of the trees the module
constructed during the play) and `moduleMixedFixedRel … Envs` the one over fixed environments.

**Assume/guarantee.** In a fixed environment `ρ` the import specification is the cons writer
specification `Silmaril.Wasm.Game.HandleAccept.Writers.writerISpec`: `word(x)` returns the
sentinel or `r` with `ρ r = some (atom x)`, `nil()` returns `r` with `ρ r = some nil`,
`cons(a, b)` returns `r` with `ρ r = some (cons (ρ a) (ρ b))`. The export specification is the
one-shot parse specification `Silmaril.Wasm.Game.HandleAccept.Parsing.parseESpec`: a returned
non-sentinel handle `h` for `parse(v)` has `ρ h = some x` only for `([v], x) ∈ R`. `mixedISpec`
is the import side (`accept` calls unconstrained: every tree, `Set.univ`).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers
  Silmaril.Wasm.Game.HandleAccept.Parsing
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-! ## Decoding plays -/

variable {E F : Sig.{0}} {Op V H : Type}

/-- **The mixed events of a play**: export calls as `enter`, import moves through the writer
decoders, export answers through the parsing decoder. -/
def mixedEvents (dAsk : E.Op → Option (WEv Op H))
    (dAns : (e : E.Op) → E.Ar e → Option (WEv Op H))
    (pdec : (f : F.Op) → F.Ar f → Option (PEv V H)) : List (Move E F) → List (MEv Op V H)
  | [] => []
  | .inl (.ask e) :: p => ((dAsk e).map .w).toList ++ mixedEvents dAsk dAns pdec p
  | .inl (.ans e v) :: p => ((dAns e v).map .w).toList ++ mixedEvents dAsk dAns pdec p
  | .inr (.ask _) :: p => .w .enter :: mixedEvents dAsk dAns pdec p
  | .inr (.ans f v) :: p => ((pdec f v).map .p).toList ++ mixedEvents dAsk dAns pdec p

/-- The decoded mixed traces of a strategy. -/
def mixedTraces (σ : Strategy E F) (dAsk : E.Op → Option (WEv Op H))
    (dAns : (e : E.Op) → E.Ar e → Option (WEv Op H))
    (pdec : (f : F.Op) → F.Ar f → Option (PEv V H)) : Set (List (MEv Op V H)) :=
  {t | ∃ p ∈ σ, t = mixedEvents dAsk dAns pdec p}

/-! ## Relations of modules -/

/-- The decoded mixed traces of every play of a module's instance (cons writer imports `wix`,
parsing exports `pix`). -/
noncomputable def moduleMixedTraces (P : Profile) (m : Module) (wix : ConsWImports)
    (pix : ParseExports V) : Set (List (MEv (ConsOp (BitVec 64)) V (BitVec 32))) :=
  mixedTraces ((Verify.instOf m).strategy P (Verify.instOf m).store) (consWDecAsk wix)
    (consWDecAns wix) (parseDec pix)

/-- **The input/tree relation of a parser module building its trees** through the cons writer
imports (store semantics). -/
noncomputable def moduleMixedRel (P : Profile) (m : Module) (wix : ConsWImports)
    (pix : ParseExports V) (pol : Policy (BitVec 32)) (ppol : PPolicy (BitVec 32)) :
    Set (List V × SExp2 (BitVec 64)) :=
  mixedRel (consW (BitVec 64)) pol ppol (moduleMixedTraces P m wix pix)

/-- The input/tree relation over the fixed environments `Envs`. -/
noncomputable def moduleMixedFixedRel (P : Profile) (m : Module) (wix : ConsWImports)
    (pix : ParseExports V) (pol : Policy (BitVec 32)) (ppol : PPolicy (BitVec 32))
    (Envs : Set (Env (BitVec 32) (SExp2 (BitVec 64)))) : Set (List V × SExp2 (BitVec 64)) :=
  mixedFixedRel (consW (BitVec 64)) pol ppol Envs (moduleMixedTraces P m wix pix)

/-! ## Specifications -/

variable {ts : List FnType}

/-- The import specification of a mixed module in `ρ`: cons writer answers agree with `ρ`
(sentinel `s`); `accept` is unconstrained. -/
def mixedISpec (wix : ConsWImports) (s : Option (BitVec 32))
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) : ISpec (ifaceSig ts) :=
  writerISpec (consW (BitVec 64)) s (consWDecAsk wix) (consWDecAns wix) ρ Set.univ

end Silmaril.Wasm.Game.HandleAccept.Mixed
