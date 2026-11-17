module

public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Ghost
public import Silmaril.Wasm.Execution.Core.Step

@[expose] public section

/-!
# One Core step on a store and on its typing witness (proofs)

`step_ghost`: a host-free Core step of a supported configuration whose frames are below the
store's tags is matched by a host-free step of the same code on any typing witness
`gst s T X`. Either the step keeps the tags and exceptions, and the witness step leaves the
witness of the new store with code equal up to exception references (a caught payload is read from
the witness), or it is a Wasm `throw`, which allocates the same exception at the end of both
exception lists.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-! ## Families -/

section Families

variable {c c' : Config H} (T : List TagInst) (X : List ExnInst)

theorem VariableStep.gst (h : VariableStep c c') :
    VariableStep (H := H) ⟨gst c.store T X, c.frame, c.code⟩ ⟨gst c'.store T X, c'.frame, c'.code⟩ ∧
      c'.store.tags = c.store.tags ∧ c'.store.exns = c.store.exns := by
  cases h <;> exact ⟨by constructor! <;> assumption, rfl, rfl⟩

theorem TableStep.gst (h : TableStep P c c') :
    TableStep P (H := H) ⟨gst c.store T X, c.frame, c.code⟩ ⟨gst c'.store T X, c'.frame, c'.code⟩ ∧
      c'.store.tags = c.store.tags ∧ c'.store.exns = c.store.exns := by
  cases h <;> exact ⟨by constructor! <;> assumption, rfl, rfl⟩

theorem MemoryStep.gst (h : MemoryStep P c c') :
    MemoryStep P (H := H) ⟨gst c.store T X, c.frame, c.code⟩ ⟨gst c'.store T X, c'.frame, c'.code⟩ ∧
      c'.store.tags = c.store.tags ∧ c'.store.exns = c.store.exns := by
  cases h <;> exact ⟨by constructor! <;> assumption, rfl, rfl⟩

end Families

/-! ## Supported code -/

theorem ASupp.not_unsupp {k : Nat} {i : Instr} (h : ASupp k (.plain i)) (hs : ¬ Structured i) :
    ¬ Unsupp i := by
  cases h with
  | plain h =>
    cases h with
    | atom _ hn => exact hn
    | _ => exact absurd trivial hs

theorem unsupp_last {k : Nat} {code : List Admin} {i : Instr} (hs : ∀ a ∈ code, ASupp k a)
    (hl : code.getLast? = some (.plain i)) (hu : Unsupp i) (hst : ¬ Structured i) : False :=
  (hs _ (List.mem_of_getLast? hl)).not_unsupp hst hu

theorem AggregateStep.not_supp {c c' : Config H} (h : AggregateStep c c') {k : Nat}
    (hs : ∀ a ∈ c.code, ASupp k a) : False := by
  cases h <;>
    (have h' := hs _ (List.getLast_mem (by simp))
     simp at h'
     exact h'.not_unsupp (by simp [Structured]) trivial)

theorem tag?_gst {s : Store H} {T : List TagInst} {X : List ExnInst} (hT : s.tags <+: T)
    {f : Frame} {x : TagIdx} {p : Nat × TagInst} (h : s.tag? f x = some p) :
    (gst s T X).tag? f x = some p := by
  obtain ⟨u, rfl⟩ := hT
  revert h
  simp only [Store.tag?, Option.bind_eq_bind, Option.bind_eq_some_iff]
  rintro ⟨ta, hta, ti, hti, h⟩
  exact ⟨ta, hta, ti, by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hti).1]; exact hti, h⟩

theorem RefStep.gst {c c' : Config H} {T : List TagInst} {X : List ExnInst}
    (hg : GhostOk c.store T X) (hs : ∀ a ∈ c.code, ASupp c.store.tags.length a)
    (h : RefStep c c') :
    RefStep (H := H) ⟨gst c.store T X, c.frame, c.code⟩ ⟨gst c'.store T X, c'.frame, c'.code⟩ ∧
      c'.store.tags = c.store.tags ∧ c'.store.exns = c.store.exns := by
  cases h with
  | testTrue _ => exact (unsupp_last hs rfl trivial (by simp [Structured])).elim
  | testFalse _ => exact (unsupp_last hs rfl trivial (by simp [Structured])).elim
  | castSucceed hr =>
    exact ⟨.castSucceed ((refOk_gst_iff hg ((hs _ (List.mem_of_getLast? rfl)).not_unsupp
      (by simp [Structured]))).2 hr), rfl, rfl⟩
  | castFail hr =>
    exact ⟨.castFail fun h' => hr ((refOk_gst_iff hg ((hs _ (List.mem_of_getLast? rfl)).not_unsupp
      (by simp [Structured]))).1 h'), rfl, rfl⟩
  | refFunc h => exact ⟨.refFunc h, rfl, rfl⟩
  | isNullFalse h => exact ⟨.isNullFalse h, rfl, rfl⟩
  | asNonNullAddr h => exact ⟨.asNonNullAddr h, rfl, rfl⟩
  | eqTrue h => exact ⟨.eqTrue h, rfl, rfl⟩
  | eqFalse h => exact ⟨.eqFalse h, rfl, rfl⟩
  | externConvertAddr h => exact ⟨.externConvertAddr h, rfl, rfl⟩
  | _ => exact ⟨by constructor!, rfl, rfl⟩

/-! ## One step -/

/-- The host with no answer. -/
abbrev NH : HostSemantics H := fun _ _ _ _ => False

/-- **The witness step of a step `c ⟶ c'`**, at the witness `gst c.store T X`. -/
def GhostStep (P : Profile) (c c' : Config H) (T : List TagInst) (X : List ExnInst) : Prop :=
  (c'.store.tags = c.store.tags ∧ c'.store.exns = c.store.exns ∧ ∃ es,
      Step P NH ⟨gst c.store T X, c.frame, c.code⟩ ⟨gst c'.store T X, c'.frame, es⟩ ∧
        CodeApprox X.length c'.code es) ∨
    (∃ e, c'.store = c.store.addExn e ∧ ∃ es,
      Step P NH ⟨gst c.store T X, c.frame, c.code⟩ ⟨gst c'.store T (X ++ [e]), c'.frame, es⟩ ∧
        CodeApprox (X.length + 1) c'.code es)

theorem GhostStep.wrap {c c' : Config H} {T : List TagInst} {X : List ExnInst} {f₀ f₀' : Frame}
    {K : List Admin → List Admin}
    (hK : ∀ {N es es'}, CodeApprox N es es' → CodeApprox N (K es) (K es'))
    (hS : ∀ {s s' : Store H} {es es' : List Admin},
      Step P NH ⟨s, c.frame, es⟩ ⟨s', c'.frame, es'⟩ → Step P NH ⟨s, f₀, K es⟩ ⟨s', f₀', K es'⟩)
    (h : GhostStep P c c' T X) :
    GhostStep P ⟨c.store, f₀, K c.code⟩ ⟨c'.store, f₀', K c'.code⟩ T X := by
  rcases h with ⟨h1, h2, es, hst, hx⟩ | ⟨e, he, es, hst, hx⟩
  · exact .inl ⟨h1, h2, _, hS hst, hK hx⟩
  · exact .inr ⟨e, he, _, hS hst, hK hx⟩

/-- **One host-free step of a supported configuration is matched on every typing witness.** -/
theorem step_ghost {c c' : Config H} (h : Step P NH c c') :
    ∀ {T : List TagInst} {X : List ExnInst}, GhostOk c.store T X →
      FrameBelow c.store.tags.length c.frame → (∀ a ∈ c.code, ASupp c.store.tags.length a) →
      GhostStep P c c' T X := by
  induction h with
  | parametric hp => intro _ _ _ _ _; exact .inl ⟨rfl, rfl, _, .parametric hp, .refl _⟩
  | numeric hp => intro _ _ _ _ _; exact .inl ⟨rfl, rfl, _, .numeric hp, .refl _⟩
  | vector hp => intro _ _ _ _ _; exact .inl ⟨rfl, rfl, _, .vector hp, .refl _⟩
  | «variable» hp =>
    intro T X _ _ _
    obtain ⟨h1, h2, h3⟩ := VariableStep.gst T X hp
    exact .inl ⟨h2, h3, _, .variable h1, .refl _⟩
  | table hp =>
    intro T X _ _ _
    obtain ⟨h1, h2, h3⟩ := TableStep.gst T X hp
    exact .inl ⟨h2, h3, _, .table h1, .refl _⟩
  | memory hp =>
    intro T X _ _ _
    obtain ⟨h1, h2, h3⟩ := MemoryStep.gst T X hp
    exact .inl ⟨h2, h3, _, .memory h1, .refl _⟩
  | reference hp =>
    intro T X hg _ hs
    obtain ⟨h1, h2, h3⟩ := RefStep.gst hg hs hp
    exact .inl ⟨h2, h3, _, .reference h1, .refl _⟩
  | aggregate hp =>
    intro T X _ _ hs
    exact (AggregateStep.not_supp hp hs).elim
  | ctxtInstrs hst hne ih =>
    intro T X hg hf hs
    exact GhostStep.wrap (K := fun es => vals _ ++ es ++ _)
      (fun hx => ((CodeApprox.refl _).append hx).append (CodeApprox.refl _))
      (fun st => .ctxtInstrs st hne) (ih hg hf fun a ha => hs a (by simp [ha]))
  | @ctxtLabel s s' f f' n cont is is' hst ih =>
    intro T X hg hf hs
    have hb : ∀ a ∈ is, ASupp s.tags.length a := by
      cases hs _ (List.mem_singleton_self _) with
      | label _ _ hb => exact hb
    exact GhostStep.wrap (K := fun es => [.label _ _ es]) (fun hx => .cons (.label _ _ hx) .nil)
      (fun st => .ctxtLabel st) (ih hg hf hb)
  | @ctxtHandler s s' f f' n cs is is' hst ih =>
    intro T X hg hf hs
    have hb : ∀ a ∈ is, ASupp s.tags.length a := by
      cases hs _ (List.mem_singleton_self _) with
      | handler _ _ hb => exact hb
    exact GhostStep.wrap (K := fun es => [.handler _ _ es])
      (fun hx => .cons (.handler _ _ hx) .nil) (fun st => .ctxtHandler st) (ih hg hf hb)
  | @ctxtFrame s s' f fi fi' n is is' hst ih =>
    intro T X hg hf hs
    obtain ⟨hfi, hb⟩ : FrameBelow s.tags.length fi ∧ ∀ a ∈ is, ASupp s.tags.length a := by
      cases hs _ (List.mem_singleton_self _) with
      | frame _ hf hb => exact ⟨hf, hb⟩
    rcases ih hg hfi hb with ⟨h1, h2, es, st, hx⟩ | ⟨e, he, es, st, hx⟩
    · exact .inl ⟨h1, h2, _, .ctxtFrame st, .cons (.frame _ _ hx) .nil⟩
    · exact .inr ⟨e, he, _, .ctxtFrame st, .cons (.frame _ _ hx) .nil⟩
  | @throw s f x vs ta ti ts ht he hn =>
    intro T X hg _ _
    refine .inr ⟨_, rfl, _, Step.throw (s := gst s T X) (tag?_gst hg.tags ht) he hn, ?_⟩
    exact .cons (.ref (.exn (Nat.lt_succ_of_lt hg.lt))) (.cons (.refl _) .nil)
  | @throwRefHandlerCatch s f n x l cs a e he ht =>
    intro T X hg _ _
    obtain ⟨e', h', htag, hfs⟩ := hg.real a e he
    refine .inl ⟨rfl, rfl, _,
      .throwRefHandlerCatch (s := gst s T X) h' (by rw [htag]; exact ht), ?_⟩
    exact (CodeApprox.of_vals hfs).append (CodeApprox.refl _)
  | @throwRefHandlerCatchRef s f n x l cs a e he ht =>
    intro T X hg _ _
    obtain ⟨e', h', htag, hfs⟩ := hg.real a e he
    refine .inl ⟨rfl, rfl, _,
      .throwRefHandlerCatchRef (s := gst s T X) h' (by rw [htag]; exact ht), ?_⟩
    exact (CodeApprox.of_vals hfs).append (CodeApprox.refl _)
  | throwRefHandlerNext hnm =>
    intro T X hg hf _
    exact .inl ⟨rfl, rfl, _,
      .throwRefHandlerNext fun h' => hnm ((catchMatches_gst_iff hg hf).1 h'), .refl _⟩
  | brOnCastSucceed _ =>
    intro _ _ _ _ hs
    exact (unsupp_last hs rfl trivial (by simp [Structured])).elim
  | brOnCastFail _ =>
    intro _ _ _ _ hs
    exact (unsupp_last hs rfl trivial (by simp [Structured])).elim
  | brOnCastFailSucceed _ =>
    intro _ _ _ _ hs
    exact (unsupp_last hs rfl trivial (by simp [Structured])).elim
  | brOnCastFailFail _ =>
    intro _ _ _ _ hs
    exact (unsupp_last hs rfl trivial (by simp [Structured])).elim
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | _ =>
    intro _ _ _ _ _
    first
      | exact .inl ⟨rfl, rfl, _, .block ‹_› ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .loop ‹_› ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .ifTrue ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .ifFalse, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .labelVals, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .brLabelZero ‹_› ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .brLabelSucc ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .brHandler, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .brIfTrue ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .brIfFalse, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .brTableLt ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .brTableGe ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .brOnNullNull, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .brOnNullAddr ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .brOnNonNullNull, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .brOnNonNullAddr ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .call ‹_› ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .callRefNull ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .callRefFunc ‹_› ‹_› ‹_› ‹_› ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .returnCall ‹_› ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .returnCallRefLabel ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .returnCallRefHandler ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .returnCallRefFrameNull ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .returnCallRefFrameAddr ‹_› ‹_› ‹_› ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .callIndirect, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .returnCallIndirect, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .frameVals ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .returnFrame ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .returnLabel, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .returnHandler, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .throwRefNull, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .throwRefInstrs ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .throwRefLabel, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .throwRefFrame, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .throwRefHandlerEmpty, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .throwRefHandlerCatchAll, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .throwRefHandlerCatchAllRef, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .tryTable ‹_› ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .handlerVals, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .trapInstrs ‹_›, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .trapLabel, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .trapHandler, .refl _⟩
      | exact .inl ⟨rfl, rfl, _, .trapFrame, .refl _⟩

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
