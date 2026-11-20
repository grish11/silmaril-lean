module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Defs
public import Silmaril.Semantics.Accept.Mixed.Thms
public import Silmaril.Wasm.Logic.GameLink.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Basic

/-!
# Parsers that build their trees: the assume/guarantee bridge

For a module with cons writer imports `wix` and one-shot parsing exports `pix`
(`ParseExports.OneShot`), the Hoare-logic obligation

`GameSat P (instOf m) Inv (mixedISpec wix pol.sentinel ρ) (parseESpec pix ppol.sentinel ρ R)`

says: **assuming** that every writer answer agrees with the environment `ρ` (`word(x)` returns
the sentinel or a handle denoting `atom x` in `ρ`, `nil()` one denoting `nil`, `cons(a, b)` one
denoting `cons (ρ a) (ρ b)`), the module **guarantees** that every non-sentinel handle `h` it
returns from `parse(v)` denotes in `ρ` a tree `x` with `([v], x) ∈ R`.

* `moduleMixedRel_sound_of_gameSat`: if the obligation holds for **every** `ρ`, the store
  relation (`moduleMixedRel`, a returned handle resolved in the store the play constructed) is in
  `R`, for writer and parsing policies without undefined behaviour. The environment witnessing a
  run is its final store: every write of the run agrees with it (stores only grow).
* `moduleMixedFixedRel_sound_of_gameSat`: if it holds for every `ρ ∈ Envs`, the relation over
  the fixed environments `Envs` is in `R`, for every writer policy.

Unlike `Silmaril.Wasm.Game.HandleAccept.Parsing.moduleParseRel_sound_of_gameSat`, where the tree
of a returned handle is whatever an arbitrary environment says (so an export specification can
only constrain the input), here the import side ties handles to the trees the module built, so
the export side constrains the tree.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Formats Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Parsing
open Silmaril.Wasm.Logic.GameLink (GameSat)

variable {V : Type} {P : Profile} {m : Module} {wix : ConsWImports} {pix : ParseExports V}
  {pol : Policy (BitVec 32)} {ppol : PPolicy (BitVec 32)} {R : Set (List V × SExp2 (BitVec 64))}
  {Inv : Store Nat → Prop}

/-- **Soundness of a parser module building its trees** (store semantics) from its Hoare-logic
obligation in every environment. -/
theorem moduleMixedRel_sound_of_gameSat
    (hm : ∀ ρ, GameSat P (Verify.instOf m) Inv (mixedISpec wix pol.sentinel ρ)
      (parseESpec pix ppol.sentinel ρ R))
    (hs : Inv (Verify.instOf m).store) (h1 : pix.OneShot) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P m wix pix pol ppol ⊆ R :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.moduleMixedRel_sound_of_gameSat hm hs h1 hw ha hb
    ho

/-- **Soundness over fixed environments**, for every writer policy. -/
theorem moduleMixedFixedRel_sound_of_gameSat
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))}
    (hm : ∀ ρ ∈ Envs, GameSat P (Verify.instOf m) Inv (mixedISpec wix pol.sentinel ρ)
      (parseESpec pix ppol.sentinel ρ R))
    (hs : Inv (Verify.instOf m).store) (h1 : pix.OneShot) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedFixedRel P m wix pix pol ppol Envs ⊆ R :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.moduleMixedFixedRel_sound_of_gameSat hm hs h1 hb ho

end Silmaril.Wasm.Game.HandleAccept.Mixed
