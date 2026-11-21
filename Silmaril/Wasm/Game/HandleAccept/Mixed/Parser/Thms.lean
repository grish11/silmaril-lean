module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Parser.Defs
public import Silmaril.Wasm.Game.HandleAccept.Mixed.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Parser

/-!
# A parser that builds its tree: what is proved

* `listParse` validates and instantiates (`listParse_instance`).
* **Hoare-logic specification** (`listParse_sat`): in every environment `ρ` and every profile,
  assuming the cons writer answers agree with `ρ` (`mixedISpec twoIx none ρ`: no writer
  sentinel), the instance guarantees the parse specification `parseESpec listPix 0 ρ listR`
  (proof in `Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Parser`).
* **Soundness**, through the assume/guarantee bridge
  `Silmaril.Wasm.Game.HandleAccept.Mixed.moduleMixedRel_sound_of_gameSat`: for every profile,
  every writer policy without a failure sentinel and without UB, and every parsing policy with
  sentinel `0` and without UB, every input/tree pair of `listParse` is `([x], (x))` for a nonzero
  word `x` (`listParse_sound`, `listParse_rel`); likewise over any set of fixed environments,
  for every writer policy without a sentinel (`listParse_fixed_sound`, `listParse_fixed_rel`).

The tree is constrained, not only the input (compare
`Silmaril.Wasm.Game.HandleAccept.Parsing.Checkers.nzParse_sound`): a returned handle is resolved
in the store of the trees the module constructed through its writer imports.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Parser

open Silmaril.Wasm Silmaril.Formats Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Writers
  Silmaril.Wasm.Game.HandleAccept.Writers.Builders Silmaril.Wasm.Game.HandleAccept.Parsing
open Silmaril.Wasm.Logic.GameLink (GameSat)

theorem listParse_instance : (Verify.instance? listParse).isSome = true := by decide +kernel

/-- **`listParse` meets its mixed specification**: writer answers agreeing with `ρ` guarantee
returns related by `listR` in `ρ`. -/
theorem listParse_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf listParse) listInv (mixedISpec twoIx none ρ)
      (parseESpec listPix 0 ρ listR) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Parser.listParse_sat P ρ

/-- **`listParse` relates only `([x], (x))`, `x ≠ 0`** (store semantics). -/
theorem listParse_sound (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (h0 : ppol.sentinel = 0) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P listParse twoIx listPix pol ppol ⊆ listR :=
  moduleMixedRel_sound_of_gameSat (Inv := listInv)
    (fun ρ => hsen ▸ h0 ▸ listParse_sat P ρ) rfl ⟨rfl, rfl, rfl, rfl⟩ hw ha hb ho

/-- **`listParse` relates only `([x], (x))`, `x ≠ 0`**, over any set of fixed environments. -/
theorem listParse_fixed_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none) {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleMixedFixedRel P listParse twoIx listPix pol ppol Envs ⊆ listR :=
  moduleMixedFixedRel_sound_of_gameSat (Inv := listInv)
    (fun ρ _ => hsen ▸ h0 ▸ listParse_sat P ρ) rfl ⟨rfl, rfl, rfl, rfl⟩ hb ho

/-- Every related pair, read off. -/
theorem listParse_rel (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (h0 : ppol.sentinel = 0) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    {w : List (BitVec 64)} {t : SExp2 (BitVec 64)}
    (h : (w, t) ∈ moduleMixedRel P listParse twoIx listPix pol ppol) :
    ∃ x : BitVec 64, x ≠ 0 ∧ w = [x] ∧ t = SExp2.ofAtoms [x] := by
  obtain ⟨x, hx, he⟩ := listParse_sound P hsen hw ha h0 hb ho h
  cases he
  exact ⟨x, hx, rfl, rfl⟩

end Silmaril.Wasm.Game.HandleAccept.Mixed.Parser
