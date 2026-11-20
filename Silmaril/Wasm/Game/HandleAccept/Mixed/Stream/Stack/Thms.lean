module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack.Defs
public import Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Stack

/-!
# A streaming parser keeping its stack in globals: what is proved

* `stackParse` validates and instantiates (`stackParse_instance`); its instantiated store
  represents the empty buffer (`stackInv_init`).
* **Stateful Hoare-logic specification** (`stackParse_sat`): in every environment `ρ` and every
  profile, for every parsing policy whose `done` clears the buffer, assuming the cons writer
  answers agree with `ρ` (`mixedISpec twoIx none ρ`), the instance meets
  `streamSSpec stackPix ppol ρ stackR (stackInv ρ)`: from a store representing the pending
  buffer `g`, `append(x)` ends in a store representing `g ++ [x]`, and a handle `h` returned by
  `done()` denotes `SExp2.ofAtoms g.reverse` in `ρ`, in a store representing `[]` (proof in
  `Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Stack`).
* **Soundness** through the streaming bridge
  `Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.moduleMixedRel_sound_of_streamSat`: for every
  profile, every writer policy without a failure sentinel and without UB, and every parsing
  policy without UB whose `done` clears the buffer (any parsing sentinel), every input/tree pair
  of `stackParse` is `(vs, SExp2.ofAtoms vs.reverse)` (`stackParse_sound`, `stackParse_rel`):
  the values appended since the previous `done`, most recent first. Likewise over any set of
  fixed environments (`stackParse_fixed_sound`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack

open Silmaril.Wasm Silmaril.Formats Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing

theorem stackParse_instance : (Verify.instance? stackParse).isSome = true := by decide +kernel

theorem stackInv_init (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    stackInv ρ [] (Verify.instOf stackParse).store :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Stack.stackInv_init ρ

/-- **`stackParse` meets its streaming specification**: writer answers agreeing with `ρ`
guarantee that `done()` returns the reversed list of the values appended since the last
`done`. -/
theorem stackParse_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))
    {ppol : PPolicy (BitVec 32)} (hc : ppol.doneClears = true) :
    SGameSat P (Verify.instOf stackParse) (mixedISpec twoIx none ρ)
      (streamSSpec stackPix ppol ρ stackR (stackInv ρ)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Stack.stackParse_sat P ρ hc

/-- **`stackParse` relates only `(vs, (vs reversed))`** (store semantics). -/
theorem stackParse_sound (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (hc : ppol.doneClears = true) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P stackParse twoIx stackPix pol ppol ⊆ stackR :=
  moduleMixedRel_sound_of_streamSat (Inv := stackInv)
    (fun ρ => hsen ▸ stackParse_sat P ρ hc) stackInv_init hw ha hb ho

/-- **`stackParse` relates only `(vs, (vs reversed))`**, over any set of fixed environments. -/
theorem stackParse_fixed_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none) {ppol : PPolicy (BitVec 32)} (hc : ppol.doneClears = true)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleMixedFixedRel P stackParse twoIx stackPix pol ppol Envs ⊆ stackR :=
  moduleMixedFixedRel_sound_of_streamSat (Inv := stackInv)
    (fun ρ _ => hsen ▸ stackParse_sat P ρ hc) (fun ρ _ => stackInv_init ρ) hb ho

/-- Every related pair, read off. -/
theorem stackParse_rel (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (hc : ppol.doneClears = true) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    {w : List (BitVec 64)} {t : SExp2 (BitVec 64)}
    (h : (w, t) ∈ moduleMixedRel P stackParse twoIx stackPix pol ppol) :
    t = SExp2.ofAtoms w.reverse :=
  stackParse_sound P hsen hw ha hc hb ho h

end Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Stack
