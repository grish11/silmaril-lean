module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.IR
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.Fixture
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkConds

/-!
# Linked sessions: the fixture `linkedC`

* `linkedC_sessSpec`: the session `poke, peek` of `LinkedSession.linkedC` in the specification
  (`Linked2.SessSpec`), for every profile: `poke`'s import call `set` is a trapped call of A
  (`set_trapAt`, A's store moves to `g = 1`), so `poke` answers `none`; `peek`'s import call
  `get` then answers `1` from that store;
* `linkedC_ir_session_of_spec`: #703's `linkedC_ir_session`, derived through
  `linked2_sess_specToIR`;
* `linkedC_adequate`: `linkedC` satisfies `Linked2.Adequate`, so `linked2_sess_refToSpec` and
  `linked2_sess_sound` apply to it (`linkedC_sess_sound`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.LinkedSession
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

/-- **The session `poke, peek` of `linkedC` in the specification**, for every profile: `trap`,
then `1`. -/
theorem linkedC_sessSpec (P : Profile) :
    Linked2.SessSpec P linkedC sgInst ppInst ppInst.store sgInst.store
      [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])] [none, some [.u32 1]] ppStore sgStore₁ := by
  obtain ⟨_, _, _, ⟨g, hglob, _⟩⟩ := sgFacts
  exact .round pokeR pokeR_ok (poke_path P) (.trap ⟨0, by decide⟩ rfl (set_trapAt P) (.nil _)) rfl
    (.round (peekR 1) (peekR_ok 1) (peek_path P 1)
      (.ret ⟨1, by decide⟩ rfl (get_retAt P rfl (sgStore₁_globals hglob) rfl) (.nil _)) rfl
      (.nil _ _))

/-- **#703's `linkedC_ir_session` through the specification**: the IR play
`poke · trap · peek · 1`, for every profile. -/
theorem linkedC_ir_session_of_spec (P : Profile) :
    ([.inr (.ask (⟨0, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨0, by decide⟩, .vals [])) none),
      .inr (.ask (⟨1, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨1, by decide⟩, .vals [])) (some (.vals [.u32 1])))] :
      List (Move linkedC.toComp.imports.sig (sigN linkedC.toComp.exports.length))) ∈
      linkedC.toComp.den (impSem P) :=
  linked2_sess_specToIR setGetS_good pokePeekI_good sg_isInst pp_isInst (linkedC_sessSpec P)

/-! ## The hypotheses -/

/-- A name of length `n + 1` other than `tag "t" n` is no generated type name. -/
theorem ne_tag_of_length {s : String} (n : Nat) (hs : s.length = n + 1) (hne : s ≠ tag "t" n) :
    ∀ m, s ≠ tag "t" m := by
  intro m e
  have hm : (tag "t" m).length = 1 + m := tag_length "t" m
  rw [← e, hs] at hm
  have hmn : m = n := by omega
  subst hmn
  exact hne e

theorem setGetS_inst : setGetS.Inst := ⟨⟨sgInst, sg_isInst⟩, by decide⟩

/-- The validated import types of `pokePeekCore`, summarised. -/
def ppImportsSummary : Bool :=
  match Silmaril.Wasm.Validation.validate? LinkedSession.pokePeekCore with
  | some mt => decide (mt.imports = pokePeekI.imports.map fun p =>
      .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩))
  | none => false

theorem ppImportsSummary_eq : ppImportsSummary = true := by decide +kernel

theorem pp_importTypes : ∃ mt, Silmaril.Wasm.Validation.validate? pokePeekI.mod.mod = some mt ∧
    mt.imports = pokePeekI.imports.map fun p =>
      .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩) := by
  have h : ppImportsSummary = true := ppImportsSummary_eq
  unfold ppImportsSummary at h
  split at h
  next mt hmt => exact ⟨mt, hmt, of_decide_eq_true h⟩
  next => cases h

theorem pokePeekI_inst : pokePeekI.Inst :=
  ⟨⟨ppInst, pp_isInst⟩, by decide, by decide, rfl, pp_importTypes⟩

theorem pokePeekI_arity : pokePeekI.Arity := by
  unfold SimpleI.Arity
  decide

theorem pokePeekI_floatFree : pokePeekI.FloatFree := by
  unfold SimpleI.FloatFree
  decide

theorem linkedC_wireTy : linkedC.WireTy := by
  refine ⟨rfl, fun k w hk => ?_⟩
  match k, hk with
  | 0, hk =>
    have hw : w = 0 := (Option.some.inj hk).symm
    subst hw
    exact ⟨_, rfl, rfl⟩
  | 1, hk =>
    have hw : w = 1 := (Option.some.inj hk).symm
    subst hw
    exact ⟨_, rfl, rfl⟩
  | _ + 2, hk => simp [linkedC] at hk

theorem linkedC_namesOk : linkedC.NamesOk := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [linkedC, setGetS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ne_tag_of_length 2 (by decide) (by decide)
    · exact ne_tag_of_length 2 (by decide) (by decide)
  · simp only [linkedC, pokePeekI, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ne_tag_of_length 3 (by decide) (by decide)
    · exact ne_tag_of_length 3 (by decide) (by decide)

theorem linkedC_wireNodup : linkedC.WireNodup := by
  unfold Linked2.WireNodup
  decide

theorem linkedC_splitOk : linkedC.SplitOk :=
  ⟨⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **`linkedC` satisfies the adequacy hypotheses.** -/
theorem linkedC_adequate : linkedC.Adequate :=
  ⟨setGetS_good, setGetS_inst, pokePeekI_good, pokePeekI_inst, pokePeekI_arity,
    pokePeekI_floatFree, linkedC_wireTy, linkedC_namesOk, linkedC_wireNodup, linkedC_splitOk⟩

theorem linkedC_typed :
    SimpleI.TypedCalls linkedC.imp [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])] := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> rfl

/-- **The reference sessions `poke, peek` of `linkedC` are IR plays** (every profile, component
choice profile and host functions; `linked2_sess_sound`). -/
theorem linkedC_sess_sound (P : Profile) (prof : ProfileKind) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)
    {o : List (Option (List Silmaril.Wasm.Component.Value.Val))}
    (ho : o ∈ Linked2.sessObs prof linkedC impl h₀ [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])]) :
    ∃ outs, o = refOuts outs ∧ 2 = outs.length ∧
      Linked2.sessMoves linkedC [(⟨0, by decide⟩, []), (⟨1, by decide⟩, [])] outs ∈
        linkedC.toComp.den (impSem P) :=
  linked2_sess_sound P prof linkedC linkedC_adequate impl h₀ _ linkedC_typed ho

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
