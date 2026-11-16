module

public import Silmaril.Logic.Consequence.Acceptor.Defs
public import Silmaril.Logic.Consequence.Accept.Defs

/-!
# CSLib acceptors and their interpreters as consequence systems: laws

**Rows are languages.** `ofAcceptor_apply`, `ofInterpreter_apply`: a judgement is membership in
the acceptor's language (`Cslib.Automata.Acceptor.language`); `ofAcceptor_row`,
`ofInterpreter_row` state it for the whole row of a context.

**Reindexing.** `ofInterpreter_id`: the identity interpreter gives `ofAcceptor`;
`ofInterpreter_comp`: precomposing the interpreter is pulling back the system;
`ofDecoder_some`: a total decoder gives `ofInterpreter`; `ofDecoder_pullback_of_roundtrip`:
along an encoder that the decoder inverts, the bytes system restricts to the program system.

**Decoding.** `ofDecoder_of_eq_some`: decoded bytes have the row of their program;
`ofDecoder_of_eq_none`: undecodable bytes prove nothing, so they are consistent
(`contextConsistent_ofDecoder_of_eq_none`).

**Soundness and completeness are language inclusions.** `ofInterpreter_le_iff`: one
interpreter's system is below another's iff each program's language is included;
`ofDecoder_mono` lifts this through any decoder.

**The single-context lifts.** `pullback_const_ofAcceptor`: fixing one acceptor as the only
context gives `liftCAll` of its language; `liftTTC_le_iff_language`: `liftTTC tt L` is below
`ofAcceptor` iff `L` is included in the language of `tt`.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u u' v w w' t

open Cslib.Automata (Acceptor)

namespace System

variable {X : Type u} {Y : Type u'} {α : Type v} [Acceptor X α] [Acceptor Y α]
  {W : Type w} {W' : Type w'} {B : Type t}

@[simp] theorem ofAcceptor_apply (x : X) (w : List α) :
    ofAcceptor X x w ↔ w ∈ Acceptor.language x := Iff.rfl

theorem ofAcceptor_row (x : X) : {w | ofAcceptor X x w} = Acceptor.language x := rfl

@[simp] theorem ofInterpreter_apply (interp : W → X) (m : W) (w : List α) :
    ofInterpreter interp m w ↔ w ∈ Acceptor.language (interp m) := Iff.rfl

theorem ofInterpreter_row (interp : W → X) (m : W) :
    {w | ofInterpreter interp m w} = Acceptor.language (interp m) := rfl

theorem ofInterpreter_id : ofInterpreter (id : X → X) = ofAcceptor X := rfl

theorem ofInterpreter_comp (interp : W → X) (f : W' → W) :
    ofInterpreter (interp ∘ f) = (ofInterpreter interp).pullback f id := rfl

/-- Inclusion of interpreter systems is inclusion of languages, program by program. -/
theorem ofInterpreter_le_iff (i : W → X) (j : W → Y) :
    (ofInterpreter i : System W (List α)) ≤ ofInterpreter j ↔
      ∀ m, Acceptor.language (i m) ≤ Acceptor.language (j m) :=
  ⟨fun h m _ hw => h m _ hw, fun h m _ hw => h m hw⟩

theorem ofInterpreter_eq_iff (i : W → X) (j : W → Y) :
    (ofInterpreter i : System W (List α)) = ofInterpreter j ↔
      ∀ m, Acceptor.language (i m) = Acceptor.language (j m) := by
  rw [le_antisymm_iff, ofInterpreter_le_iff, ofInterpreter_le_iff]
  exact ⟨fun h m => (h.1 m).antisymm (h.2 m), fun h => ⟨fun m => (h m).le, fun m => (h m).ge⟩⟩

theorem ofDecoder_of_eq_some {decode : B → Option W} (interp : W → X) {b : B} {m : W}
    (h : decode b = some m) (w : List α) :
    ofDecoder decode interp b w ↔ ofInterpreter interp m w :=
  ⟨fun ⟨_, hm, hw⟩ => Option.some.inj (h.symm.trans hm) ▸ hw, fun hw => ⟨m, h, hw⟩⟩

/-- Bytes that do not decode prove nothing. -/
theorem ofDecoder_of_eq_none {decode : B → Option W} (interp : W → X) {b : B}
    (h : decode b = none) (w : List α) : ¬ ofDecoder decode interp b w :=
  fun ⟨_, hm, _⟩ => by simp [h] at hm

theorem contextConsistent_ofDecoder_of_eq_none {decode : B → Option W} (interp : W → X) {b : B}
    (h : decode b = none) : (ofDecoder decode interp : System B (List α)).ContextConsistent b :=
  fun hall => ofDecoder_of_eq_none interp h [] (hall [])

theorem ofDecoder_some (interp : W → X) :
    (ofDecoder some interp : System W (List α)) = ofInterpreter interp :=
  funext fun _ => funext fun _ => propext (ofDecoder_of_eq_some interp rfl _)

/-- Along an encoder that the decoder inverts, the bytes system is the program system. -/
theorem ofDecoder_pullback_of_roundtrip {decode : B → Option W} {encode : W → B}
    (h : ∀ m, decode (encode m) = some m) (interp : W → X) :
    (ofDecoder decode interp : System B (List α)).pullback encode id = ofInterpreter interp :=
  funext fun m => funext fun _ => propext (ofDecoder_of_eq_some interp (h m) _)

/-- Language inclusion, program by program, survives decoding. -/
theorem ofDecoder_mono (decode : B → Option W) {i : W → X} {j : W → Y}
    (h : ∀ m, Acceptor.language (i m) ≤ Acceptor.language (j m)) :
    (ofDecoder decode i : System B (List α)) ≤ ofDecoder decode j :=
  fun _ _ ⟨m, hm, hw⟩ => ⟨m, hm, h m hw⟩

end System

variable {X : Type u} {α : Type v} [Acceptor X α]

/-- One acceptor as the only context: the lift `liftCAll` of its language. -/
theorem pullback_const_ofAcceptor {Ax : Type w} (x : X) :
    (System.ofAcceptor X).pullback (fun _ : Ax => x) id = liftCAll (Acceptor.language x) := rfl

/-- `liftTTC tt L` is below the acceptor system iff `tt` accepts every word of `L`. -/
theorem liftTTC_le_iff_language (tt : X) (L : Set (List α)) :
    liftTTC tt L ≤ System.ofAcceptor X ↔ L ⊆ Acceptor.language tt :=
  ⟨fun h _ hw => h tt _ ⟨rfl, hw⟩, fun h _ _ ⟨e, hw⟩ => e ▸ h hw⟩

end Silmaril.Consequence
