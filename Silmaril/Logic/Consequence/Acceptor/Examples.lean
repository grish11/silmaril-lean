module

public import Silmaril.Logic.Consequence.Acceptor.Thms

/-!
# CSLib acceptors and their interpreters as consequence systems: examples

A toy acceptor `LenIs n` accepts the Boolean words of length `n`. Its "programs" are numbers
(`interp n = LenIs n`), and their "bytes" are lists of numbers that encode a program as a
singleton (`decode`). The three views:

* acceptor: `⟨2⟩ ⊢ [true, false]`;
* program: `2 ⊢ [true, false]`, and the row of `n` is the language of `LenIs n`;
* bytes: `[2] ⊢ [true, false]`; `[1, 2]` does not decode and proves nothing, unlike `[0]`,
  which decodes to a program whose row is only the empty word.

`LenLe n` (length at most `n`) gives a second interpreter, and the `LenIs` reading is sound
against it (`ofInterpreter_le_iff`).
-/

@[expose] public section

namespace Silmaril.Consequence.Examples.AcceptorSystems

open Silmaril.Consequence.System

/-- Accept the Boolean words of length `n`. -/
structure LenIs where
  n : Nat

instance : Cslib.Automata.Acceptor LenIs Bool := ⟨fun a w => w.length = a.n⟩

/-- The interpreter of programs (numbers). -/
def interp (n : Nat) : LenIs := ⟨n⟩

/-- The decoder of encoded programs: exactly the singletons. -/
def decode : List Nat → Option Nat
  | [n] => some n
  | _ => none

/-- The acceptor view. -/
example : ofAcceptor LenIs ⟨2⟩ [true, false] := rfl

example : ¬ ofAcceptor LenIs ⟨2⟩ [true] := by simp [ofAcceptor, Cslib.Automata.Acceptor.Accepts]

/-- The program view, and its rows. -/
example : ofInterpreter interp 2 [true, false] := rfl

example (n : Nat) :
    {w | ofInterpreter interp n w} = Cslib.Automata.Acceptor.language (interp n) :=
  ofInterpreter_row interp n

/-- The bytes view. -/
example : ofDecoder decode interp [2] [true, false] := ⟨2, rfl, rfl⟩

/-- Undecodable bytes prove nothing, so they are consistent ... -/
example (w : List Bool) : ¬ ofDecoder decode interp [1, 2] w :=
  ofDecoder_of_eq_none interp rfl w

example : (ofDecoder decode interp : System (List Nat) (List Bool)).ContextConsistent [1, 2] :=
  contextConsistent_ofDecoder_of_eq_none interp rfl

/-- ... while a decodable program with a small language still proves its words. -/
example : ofDecoder decode interp [0] ([] : List Bool) := ⟨0, rfl, rfl⟩

/-- Accept the Boolean words of length at most `n`. -/
structure LenLe where
  n : Nat

instance : Cslib.Automata.Acceptor LenLe Bool := ⟨fun a w => w.length ≤ a.n⟩

/-- Soundness is language inclusion, program by program: every word of length `n` has length at
most `n`, so the `LenIs` reading is below the `LenLe` reading. -/
example : (ofInterpreter interp : System Nat (List Bool)) ≤ ofInterpreter (fun n => LenLe.mk n) :=
  (ofInterpreter_le_iff _ _).2 fun _ _ (h : _ = _) => h.le

/-- Encoding a program as a singleton and decoding it back: the bytes system restricts to the
program system. -/
example : (ofDecoder decode interp : System (List Nat) (List Bool)).pullback (fun n => [n]) id =
    ofInterpreter interp :=
  ofDecoder_pullback_of_roundtrip (fun _ => rfl) interp

/-- One acceptor as the only context is the lift `liftCAll` of its language. -/
example : (ofAcceptor LenIs).pullback (fun _ : Unit => (⟨1⟩ : LenIs)) id =
    liftCAll (Cslib.Automata.Acceptor.language (⟨1⟩ : LenIs)) :=
  pullback_const_ofAcceptor _

end Silmaril.Consequence.Examples.AcceptorSystems
