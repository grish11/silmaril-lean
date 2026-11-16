module

public import Silmaril.Logic.Reachability.Relational
public import Silmaril.Wasm.Execution.Core.Step

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Reachability.Wasm
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
variable {H : Type}

/-- Two real DROP instructions remove the top two values, preserving the stack prefix. -/
def start (s : Store H) (f : Frame) (vs : List Val) (a b : Val) : Config H :=
  ⟨s, f, vals vs ++ [a.toAdmin, b.toAdmin, .plain .drop, .plain .drop]⟩
def middle (s : Store H) (f : Frame) (vs : List Val) (a : Val) : Config H :=
  ⟨s, f, vals vs ++ [a.toAdmin, .plain .drop]⟩
def finish (s : Store H) (f : Frame) (vs : List Val) : Config H := ⟨s, f, vals vs⟩

theorem first_step (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (a b : Val) : Step P host (start s f vs a b) (middle s f vs a) := by
  simpa only [start, middle, vals, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using
    (Step.ctxtInstrs (P := P) (host := host) (s := s) (f := f)
      (vs := vs ++ [a]) (rest := [.plain .drop]) (.parametric (.drop b))
      (Or.inr (List.cons_ne_nil _ _)))

theorem second_step (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (a : Val) : Step P host (middle s f vs a) (finish s f vs) := by
  cases vs with
  | nil => exact .parametric (.drop a)
  | cons v vs =>
      simpa only [middle, finish, List.append_nil] using
        (Step.ctxtInstrs (P := P) (host := host) (s := s) (f := f)
          (vs := v :: vs) (rest := []) (.parametric (.drop a)) (Or.inl (List.cons_ne_nil _ _)))

theorem two_steps (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (vs : List Val) (a b : Val) :
    Reaches (Step P host) (fun c => c = finish s f vs) (start s f vs a b) :=
  .next trivial (first_step P host s f vs a b) (.next trivial (second_step P host s f vs a) (.now rfl))

/-- The matching step is precisely pinned Core `Step`, not a second operational relation. -/
def model (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (vs : List Val) (a b : Val) :
    Model () (relationalSignature Bool) :=
  @relationalModel Bool (Config H) ⟨finish s f vs⟩ (Step P host)
    (fun flag => {c | c = if flag then finish s f vs else start s f vs a b})

theorem rule_valid (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (vs : List Val) (a b : Val) :
    (atomRule .finite false true).Satisfies () (model P host s f vs a b) := by
  let _ : Nonempty (Config H) := ⟨finish s f vs⟩
  apply (atomRule_iff _ _ _ _ _).mpr
  intro c hc
  change c = start s f vs a b at hc
  exact hc ▸ two_steps P host s f vs a b

/-- The real execution proof reaches the actual μ-matching sentence. -/
theorem compiled_valid (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (vs : List Val) (a b : Val) :
    Matching.FixedPoint.Sentence.Satisfies (model P host s f vs a b)
      (encode () (atomRule .finite false true)) :=
  (encode_correct _ _).mpr (rule_valid P host s f vs a b)

end Silmaril.Logic.Reachability.Wasm
