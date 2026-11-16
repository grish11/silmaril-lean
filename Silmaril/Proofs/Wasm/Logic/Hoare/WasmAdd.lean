module

public import Silmaril.Wasm.Logic.Hoare.WasmAdd.Defs

@[expose] public section
namespace Silmaril.Logic.Hoare.Wasm
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post)
variable {H : Type}

/-- Every run of the add block satisfies the exact normal postcondition. -/
theorem addBlock_hwp (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (x y : BitVec 32) :
    Silmaril.Wasm.Logic.Hoare.HWP P host s f (vals vs ++ expression (addBlock x y))
      (addPost s f vs x y) := by
  have h : Silmaril.Wasm.Logic.Hoare.HWP P host s f
      (vals (vs ++ [Val.i32 x, Val.i32 y]) ++ [.plain (.intBinOp .i32 .add)])
      (addPost s f vs x y) := by
    apply Silmaril.Wasm.Logic.Hoare.HWP.intBinOp
    · intro z hz
      change Except.ok (x + y) = Except.ok z at hz
      cases hz
      simpa [vals, List.map_append, Val.i32, Val.toAdmin] using
        (Silmaril.Wasm.Logic.Hoare.HWP.of_vals (P := P) (host := host) (s := s) (f := f)
          (vs := vs ++ [Val.i32 (x + y)]) (Q := addPost s f vs x y) ⟨rfl, rfl, rfl⟩)
    · intro e he
      cases he
  simpa [addBlock, expression, vals, List.map_append, List.append_assoc, Val.i32, Val.toAdmin] using h

/-- Independent native interpreter computation, with a top-first operand stack. -/
theorem addBlock_exec (s : Store H) (f : Frame) (rs : List Val) (x y : BitVec 32) :
    Silmaril.Wasm.Logic.Core.exec s f rs (addBlock x y) =
      some (s, f, Val.i32 (x + y) :: rs) := rfl

/-- Interpreter soundness supplies a genuine pinned Core completion. -/
theorem addBlock_steps (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (x y : BitVec 32) :
    Steps P host ⟨s, f, vals vs ++ expression (addBlock x y)⟩
      ⟨s, f, vals (vs ++ [Val.i32 (x + y)])⟩ := by
  have h := Silmaril.Wasm.Logic.Core.exec_sound (P := P) (host := host) []
    (addBlock_exec s f vs.reverse x y)
  simpa only [List.reverse_cons, List.reverse_reverse, vals, List.map_append,
    List.map_cons, List.map_nil, List.append_nil] using h

theorem addBlock_valid (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (x y : BitVec 32) :
    triple.Satisfies Unit
      (model P host s f (vals vs ++ expression (addBlock x y)) (addPost s f vs x y)) :=
  hwp_valid P host s f _ _ (addBlock_hwp P host s f vs x y)

theorem addBlock_reachability (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (x y : BitVec 32) :
    Reachability.Sentence.Satisfies ()
      (expand Unit (model P host s f (vals vs ++ expression (addBlock x y)) (addPost s f vs x y)))
      (encode Unit triple) :=
  hwp_reachability P host s f _ _ (addBlock_hwp P host s f vs x y)

theorem addBlock_matching (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (x y : BitVec 32) :
    Matching.FixedPoint.Sentence.Satisfies
      (expand Unit (model P host s f (vals vs ++ expression (addBlock x y)) (addPost s f vs x y)))
      (Reachability.encode () (encode Unit triple)) :=
  hwp_matching P host s f _ _ (addBlock_hwp P host s f vs x y)

/-- False normal postconditions fail because a real completed run exists. -/
theorem addBlock_false_post (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (x y : BitVec 32) :
    ¬ triple.Satisfies Unit
      (model P host s f (vals vs ++ expression (addBlock x y)) (fun _ _ _ => False)) := by
  intro h
  have bad := h ⟨s, f, vals vs ++ expression (addBlock x y)⟩ rfl
    ⟨s, f, vals (vs ++ [Val.i32 (x + y)])⟩
    ⟨addBlock_steps P host s f vs x y, _, rfl⟩
  rcases bad with ⟨_, _, impossible⟩
  exact impossible

theorem addBlock_false_reachability (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (x y : BitVec 32) :
    ¬ Reachability.Sentence.Satisfies ()
      (expand Unit (model P host s f (vals vs ++ expression (addBlock x y)) (fun _ _ _ => False)))
      (encode Unit triple) :=
  fun h => addBlock_false_post P host s f vs x y ((encode_correct _ _).mp h)

theorem addBlock_false_matching (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (x y : BitVec 32) :
    ¬ Matching.FixedPoint.Sentence.Satisfies
      (expand Unit (model P host s f (vals vs ++ expression (addBlock x y)) (fun _ _ _ => False)))
      (Reachability.encode () (encode Unit triple)) :=
  fun h => addBlock_false_reachability P host s f vs x y ((Reachability.encode_correct _ _).mp h)

/-- The concrete overflow case executes to zero on every older operand tail. -/
theorem wrapping_add_exec (s : Store H) (f : Frame) (rs : List Val) :
    Silmaril.Wasm.Logic.Core.exec s f rs (addBlock (4294967295#32) (1#32)) =
      some (s, f, Val.i32 (0#32) :: rs) := by
  simpa only [show (4294967295#32) + (1#32) = 0#32 from by decide] using
    addBlock_exec s f rs (4294967295#32) (1#32)

theorem wrapping_add_wrong_post (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) :
    ¬ triple.Satisfies Unit
      (model P host s f (vals vs ++ expression (addBlock (4294967295#32) (1#32)))
        (fun _ _ o => o = .normal (vs ++ [Val.i32 (1#32)]))) := by
  intro h
  have hs := addBlock_steps P host s f vs (4294967295#32) (1#32)
  have bad := h _ rfl _ ⟨hs, _, rfl⟩
  rcases bad with ⟨_, he, ho⟩
  have values_equal := (SingleThreaded.Det.vals_inj.mp he).trans
    (Silmaril.Wasm.Logic.Core.Outcome.normal.inj ho)
  have same := List.append_cancel_left values_equal
  have impossible : Val.i32 (0#32) = Val.i32 (1#32) := by simpa using same
  exact (by decide : Val.i32 (0#32) ≠ Val.i32 (1#32)) impossible

end Silmaril.Logic.Hoare.Wasm
