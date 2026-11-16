module

public import Silmaril.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Hoare.Wasm
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post)
variable {H : Type}

def signature : Signature Unit := ⟨⟨Bool, Unit⟩, fun _ => .action ()⟩

/-- One command execution is actual Core Steps ending normally, not repeated Steps-as-actions. -/
def normalExec (P : Profile) (host : HostSemantics H) (c d : Config H) : Prop :=
  Steps P host c d ∧ ∃ vs, d.code = vals vs

def model (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (code : List Admin) (Q : Post H) : Model Unit signature where
  World := Config H
  step := fun _ => normalExec P host
  valuation := fun (b : Bool) => if b then {d | ∃ vs, d.code = vals vs ∧ Q d.store d.frame (.normal vs)}
    else {c | c = ⟨s,f,code⟩}
  point := ⟨s,f,code⟩

def triple : Triple Unit signature := ⟨(), .atom false, .atom true⟩

/-- Existing every-run Wasm safety plus partial correctness supplies a genuine generic triple.
The converse is not claimed: normal-only relational partial correctness forgets safety/other outcomes. -/
theorem hwp_valid (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (code : List Admin) (Q : Post H) (h : Silmaril.Wasm.Logic.Hoare.HWP P host s f code Q) :
    triple.Satisfies Unit (model P host s f code Q) := by
  intro c hc d ⟨hs, vs, hd⟩
  change c = ⟨s,f,code⟩ at hc
  change ∃ vs, d.code = vals vs ∧ Q d.store d.frame (.normal vs)
  refine ⟨vs, hd, ?_⟩
  have hs' : Steps P host ⟨s,f,code⟩ ⟨d.store,d.frame,vals vs⟩ := by
    have he : d = ⟨d.store,d.frame,vals vs⟩ := by
      cases d with | mk store frame code => exact congrArg (Config.mk store frame) hd
    exact hc ▸ he ▸ hs
  exact h.sound_vals hs'

theorem hwp_reachability (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (code : List Admin) (Q : Post H) (h : Silmaril.Wasm.Logic.Hoare.HWP P host s f code Q) :
    Reachability.Sentence.Satisfies () (expand Unit (model P host s f code Q)) (encode Unit triple) :=
  (encode_correct _ _).mpr (hwp_valid P host s f code Q h)

/-- The constrained reachability client also reaches the actual μ/ν matching compiler. -/
theorem hwp_matching (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (code : List Admin) (Q : Post H) (h : Silmaril.Wasm.Logic.Hoare.HWP P host s f code Q) :
    Matching.FixedPoint.Sentence.Satisfies (expand Unit (model P host s f code Q))
      (Reachability.encode () (encode Unit triple)) :=
  (Reachability.encode_correct _ _).mpr (hwp_reachability P host s f code Q h)

/-- A concrete existing LOCAL.GET proof is carried all the way to fixed-point matching. -/
theorem localGet_matching (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (x : LocalIdx) (v : Val) (hv : f.local? x = some (some v)) :
    Matching.FixedPoint.Sentence.Satisfies
      (expand Unit (model P host s f (vals vs ++ [.plain (.localGet x)])
        (fun _ _ o => o = .normal (vs ++ [v]))))
      (Reachability.encode () (encode Unit triple)) := by
  apply hwp_matching
  apply Silmaril.Wasm.Logic.Hoare.HWP.localGet hv
  simpa only [List.append_nil] using
    (Silmaril.Wasm.Logic.Hoare.HWP.of_vals (P := P) (host := host) (s := s) (f := f)
      (vs := vs ++ [v]) rfl)

/-- A trapped program has no normal completion; the normal-only partial triple is vacuous. -/
theorem trap_relational_partial (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) :
    triple.Satisfies Unit (model P host s f [.trap] (fun _ _ _ => False)) := by
  intro c hc d ⟨hs, vs, hd⟩
  change c = ⟨s,f,[.trap]⟩ at hc
  have hs' : Steps P host ⟨s,f,[.trap]⟩ d := hc ▸ hs
  have terminal : ∀ e, Steps P host ⟨s,f,[.trap]⟩ e → e = ⟨s,f,[.trap]⟩ := by
    intro e he
    induction he with
    | refl => rfl
    | @tail u v _ huv ih => exact (Silmaril.Wasm.Logic.Hoare.not_step_trap (ih ▸ huv)).elim
  have end_eq : d = ⟨s,f,[.trap]⟩ := terminal d hs'
  have he : ([.trap] : List Admin) = vals vs := (congrArg Config.code end_eq).symm.trans hd
  cases vs with
  | nil => cases he
  | cons v vs =>
      have hh : Admin.trap = v.toAdmin := (List.cons.inj he).1
      have impossible : (none : Option Val) = some v :=
        (congrArg Admin.val? hh).trans (Admin.val?_toAdmin v)
      cases impossible

/-- Existing Wasm HWP detects the false trap postcondition, unlike normal-only partial correctness. -/
theorem trap_not_hwp (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) :
    ¬ Silmaril.Wasm.Logic.Hoare.HWP P host s f [.trap] (fun _ _ _ => False) := by
  intro h
  rcases h 1 with ⟨_, _, hfalse⟩ | ⟨⟨c, hc⟩, _⟩
  · exact hfalse
  · exact Silmaril.Wasm.Logic.Hoare.not_step_trap hc

/-- info: 'Silmaril.Logic.Hoare.Wasm.hwp_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hwp_matching

end Silmaril.Logic.Hoare.Wasm
