module

public import Silmaril.Wasm.Game.HandleAccept.Memory.Defs

/-! # Proofs: inputs of traced sessions and memory-carrying writes -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Memory

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api

theorem mem_inputsOf {X I O C : Type} {enter : Option I} {i : I} :
    ∀ {ts : List (Tag X I O C)}, i ∈ inputsOf enter ts → Tag.inp i ∈ ts ∨ enter = some i
  | [], h => by simp [inputsOf] at h
  | .inp j :: ts, h => by
      simp only [inputsOf, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inl List.mem_cons_self
      · exact (mem_inputsOf h).imp (List.mem_cons_of_mem _) id
  | .enter _ :: ts, h => by
      simp only [inputsOf, List.mem_append, Option.mem_toList] at h
      rcases h with h | h
      · exact .inr h
      · exact (mem_inputsOf h).imp (List.mem_cons_of_mem _) id
  | .out _ :: ts, h => by
      simp only [inputsOf] at h
      exact (mem_inputsOf h).imp (List.mem_cons_of_mem _) id
  | .exit _ :: ts, h => by
      simp only [inputsOf] at h
      exact (mem_inputsOf h).imp (List.mem_cons_of_mem _) id

theorem calloutAt?_imp {m : Module} {memAddr : Option Nat} {c : Config Nat} {o : Callout}
    (h : calloutAt? m memAddr c = some o) :
    ∃ i ∈ m.imports, o.imp = (i.moduleName, i.name) := by
  unfold calloutAt? at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨_, _, k, args⟩, -, i, hi, rfl⟩ := h
  exact ⟨i, List.mem_of_getElem? hi, rfl⟩

/-- **Every input of a traced session is decoded from a callout of an import of the module**,
at the call (`callIn`) or at its answer (`answerIn`). -/
theorem tsession_inputs {X I O C : Type} {P : Numerics.Profile} {L : SEnv UImp} {m : Module}
    {memAddr : Option Nat} {R : Roles X I O C} {c₀ : Config Nat} {q₀ : L.S} {addrs : List Nat}
    {p : IOAccept.Phase} {w : Bool} {x : Config Nat × L.S} {ts : List (Tag X I O C)}
    (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) :
    ∀ i, Tag.inp i ∈ ts → ∃ o, (∃ c, calloutAt? m memAddr c = some o) ∧
      (R.callIn o = some i ∨ ∃ wr, R.answerIn o wr = some i) := by
  induction h with
  | start => simp
  | internal _ _ ih => exact ih
  | @call _ c _ _ _ _ _ _ _ _ ih =>
      intro i hi
      rcases List.mem_append.1 hi with hi | hi
      · exact ih i hi
      · rcases hc : calloutAt? m memAddr c with _ | o
        · simp [hc] at hi
        · simp only [hc, Option.elim, Roles.callTags, List.mem_append, List.mem_map,
            Option.mem_toList] at hi
          rcases hi with ⟨j, hj, he⟩ | ⟨j, -, he⟩
          · cases he; exact ⟨o, ⟨c, hc⟩, .inl hj⟩
          · cases he
  | @answer _ c _ _ _ _ _ _ _ a _ _ _ ih =>
      intro i hi
      rcases List.mem_append.1 hi with hi | hi
      · exact ih i hi
      · rcases hc : calloutAt? m memAddr c with _ | o
        · simp [hc] at hi
        · simp only [hc, Option.elim, Roles.answerTags, List.mem_map, Option.mem_toList] at hi
          obtain ⟨j, hj, he⟩ := hi
          cases he
          exact ⟨o, ⟨c, hc⟩, .inr ⟨_, hj⟩⟩
  | invoke _ _ _ _ _ ih =>
      intro i hi
      rcases List.mem_append.1 hi with hi | hi
      · exact ih i hi
      · simp at hi
  | ret _ _ ih =>
      intro i hi
      rcases List.mem_append.1 hi with hi | hi
      · exact ih i hi
      · simp at hi

theorem memWrite_cases {ix : MemImports} {o : Callout} {w : HostReply} {op : SxOp MemAtom}
    {args : List (BitVec 32)} {r : BitVec 32} (h : memWrite ix o w = some (.write op args r)) :
    o.imp = ix.sexp ∨ ∃ a, op = .atom a ∧ args = [] := by
  unfold memWrite at h
  rcases hr : replyI32 w with _ | r' <;> simp only [hr, Option.bind_eq_bind, Option.bind_none,
    Option.bind_some, reduceCtorEq] at h
  split_ifs at h with h1 h2 h3 h4
  · rcases hb : o.bytes32 with _ | bs <;> simp only [hb, Option.bind_none, Option.bind_some,
      reduceCtorEq] at h
    rcases hu : utf8? bs with _ | s <;> simp only [hu, Option.bind_none, Option.bind_some,
      reduceCtorEq, Option.pure_def, Option.some.injEq, WEv.write.injEq] at h
    exact .inr ⟨_, h.1.symm, h.2.1.symm⟩
  · rcases hb : o.bytes32 with _ | bs <;> simp only [hb, Option.bind_none, Option.bind_some,
      reduceCtorEq] at h
    rcases hu : utf8? bs with _ | s <;> simp only [hu, Option.bind_none, Option.bind_some,
      reduceCtorEq, Option.pure_def, Option.some.injEq, WEv.write.injEq] at h
    exact .inr ⟨_, h.1.symm, h.2.1.symm⟩
  · rcases hb : o.bytes32 with _ | bs <;> simp only [hb, Option.bind_none, Option.bind_some,
      reduceCtorEq, Option.pure_def, Option.some.injEq, WEv.write.injEq] at h
    exact .inr ⟨_, h.1.symm, h.2.1.symm⟩
  · exact .inl h4

theorem memAccept_not_write {ix : MemImports} {o : Callout} {op : SxOp MemAtom}
    {args : List (BitVec 32)} {r : BitVec 32} : memAccept ix o ≠ some (.write op args r) := by
  unfold memAccept
  split_ifs
  · cases Callout.args1 Callout.i32? o.args <;> simp
  · simp

end Silmaril.Proofs.Wasm.Game.HandleAccept.Memory
