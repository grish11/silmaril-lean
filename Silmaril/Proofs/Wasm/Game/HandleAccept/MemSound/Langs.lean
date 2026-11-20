module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Bridge
public import Silmaril.Semantics.Accept.Handle.Thms
public import Silmaril.Wasm.Game.HandleAccept.Writer.Thms

/-!
# Proofs: memory-observing languages from the program logic

* `tagTraces_pre`: the bridge at the level of a module's tag traces.
* `inputsOf` lemmas: positions of decoded inputs.
* `memWriterLang_subset_of_closed`: closed-writes contracts bound the writer language.
* `run_fixed`: a run of the writer in a fixed environment `ρ` only has writes correct in `ρ`,
  and accepts trees named by `accept` events (the fixed-environment invariant of
  `Silmaril.Accept.Handle`, restated here for traced sessions); `memFixedLang_subset`.
* `memReaderLang_subset`: the reader bridge through certified traces.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.IO
  Silmaril.Accept.Handle Silmaril.Accept.Host Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
open Silmaril.Wasm.Logic.Hoare

variable {X I O C : Type}

/-! ## The bridge on tag traces -/

theorem tagTraces_pre {P : Numerics.Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {R : Roles X I O C} {K : MemContract I}
    {Inv : Store Nat → Prop} (hsat : MemSat P m memIdx R K Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs K.reply s L) {ts : List (Tag X I O C)}
    (hts : ts ∈ tagTraces P Envs memIdx m R) {u v : List (Tag X I O C)} {x : I}
    (hd : ts = u ++ .inp x :: v) (hu : ∀ y, Tag.inp y ∈ u → K.ans y) :
    ∃ o, K.pre o ∧ (R.callIn o = some x ∨ ∃ w, R.answerIn o w = some x) := by
  obtain ⟨mt, Is, c₀, hI, L, q₀, hL, p, w, y, hs⟩ := hts
  obtain ⟨hinst, hexp⟩ := hsat mt Is c₀ hI
  exact (tsession_good hinst hexp (hE _ _ hL) hs).2 u x v hd hu

/-! ## Decoded inputs -/

theorem mem_inputsOf {e x : I} :
    ∀ {ts : List (Tag X I O C)}, x ∈ inputsOf (some e) ts → Tag.inp x ∈ ts ∨ x = e
  | [], h => by simp [inputsOf] at h
  | .inp j :: ts, h => by
      simp only [inputsOf, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inl List.mem_cons_self
      · exact (mem_inputsOf h).imp (List.mem_cons_of_mem _) id
  | .enter _ :: ts, h => by
      simp only [inputsOf, Option.toList_some, List.cons_append, List.nil_append,
        List.mem_cons] at h
      rcases h with rfl | h
      · exact .inr rfl
      · exact (mem_inputsOf h).imp (List.mem_cons_of_mem _) id
  | .out _ :: ts, h => by
      simp only [inputsOf] at h
      exact (mem_inputsOf h).imp (List.mem_cons_of_mem _) id
  | .exit _ :: ts, h => by
      simp only [inputsOf] at h
      exact (mem_inputsOf h).imp (List.mem_cons_of_mem _) id

/-- A decoded input other than the boundary event sits at an input tag, after the tags whose
inputs are the events before it. -/
theorem inputsOf_split {e x : I} (hx : x ≠ e) :
    ∀ {ts : List (Tag X I O C)} {u v : List I}, inputsOf (some e) ts = u ++ x :: v →
      ∃ u' v', ts = u' ++ .inp x :: v' ∧ inputsOf (some e) u' = u
  | [], u, v, h => by simp [inputsOf] at h
  | .inp j :: ts, u, v, h => by
      simp only [inputsOf] at h
      cases u with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨[], ts, rfl, rfl⟩
      | cons y u =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        obtain ⟨u', v', rfl, hu⟩ := inputsOf_split hx h
        exact ⟨.inp j :: u', v', rfl, by simp [inputsOf, hu]⟩
  | .enter z :: ts, u, v, h => by
      simp only [inputsOf, Option.toList_some, List.cons_append, List.nil_append] at h
      cases u with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        exact absurd h.1.symm hx
      | cons y u =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        obtain ⟨u', v', rfl, hu⟩ := inputsOf_split hx h
        exact ⟨.enter z :: u', v', rfl, by simp [inputsOf, hu]⟩
  | .out z :: ts, u, v, h => by
      simp only [inputsOf] at h
      obtain ⟨u', v', rfl, hu⟩ := inputsOf_split hx h
      exact ⟨.out z :: u', v', rfl, by simp [inputsOf, hu]⟩
  | .exit z :: ts, u, v, h => by
      simp only [inputsOf] at h
      obtain ⟨u', v', rfl, hu⟩ := inputsOf_split hx h
      exact ⟨.exit z :: u', v', rfl, by simp [inputsOf, hu]⟩

/-- An input tag of a tag list is an event of its decoded inputs. -/
theorem mem_inputsOf_of_inp {e x : I} :
    ∀ {ts : List (Tag X I O C)}, Tag.inp x ∈ ts → x ∈ inputsOf (some e) ts
  | [], h => by simp at h
  | t :: ts, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp [inputsOf]
      · have := mem_inputsOf_of_inp (e := e) h
        cases t <;> simp [inputsOf, this]

/-! ## Memory-carrying writers -/

theorem memAccept_not_write {ix : MemImports} {o : Callout} {op : SxOp MemAtom}
    {args : List (BitVec 32)} {r : BitVec 32} : memAccept ix o ≠ some (.write op args r) := by
  unfold memAccept
  split
  · cases Callout.args1 Callout.i32? o.args <;> simp
  · simp

theorem memWrite_isWrite {ix : MemImports} {o : Callout} {w : HostReply} {ev : MemWEv}
    (h : memWrite ix o w = some ev) : ∃ op args r, ev = .write op args r := by
  unfold memWrite at h
  rcases hr : replyI32 w with _ | r
  · simp [hr] at h
  · simp only [hr] at h
    split_ifs at h
    all_goals
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      aesop

theorem memAccept_isAccept {ix : MemImports} {o : Callout} {ev : MemWEv}
    (h : memAccept ix o = some ev) : ∃ h, ev = .accept h := by
  unfold memAccept at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨h, -, rfl⟩ := h
    exact ⟨h, rfl⟩
  · cases h

theorem memWrite_ne_accept {ix : MemImports} {o : Callout} {w : HostReply} {h : BitVec 32} :
    memWrite ix o w ≠ some (.accept h) := fun he => by
  obtain ⟨_, _, _, he'⟩ := memWrite_isWrite he
  cases he'

/-- **Closed-writes contracts bound the writer language.** -/
theorem memWriterLang_subset_of_closed {P : Numerics.Profile}
    {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat} {m : Module} {ix : MemImports}
    {pol : Policy (BitVec 32)} {S : Set SymStrBytesSExp} {reply : UCall Nat → UReply → Prop}
    {Inv : Store Nat → Prop} (hsat : MemSat P m memIdx (memRoles ix) (closedContract ix S reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) : memWriterLang P Envs memIdx m ix pol ⊆ S := by
  refine Silmaril.Wasm.Game.HandleAccept.Writers.writerLang_subset_of_closed ha hw ?_
  rintro _ ⟨ts, hts, rfl⟩ op args r hm
  obtain ⟨u0, v0, hu0⟩ := List.append_of_mem hm
  obtain ⟨u, v, hd, -⟩ := inputsOf_split (e := WEv.enter) (by simp) hu0
  obtain ⟨o, hpre, hc | ⟨w, hd'⟩⟩ := tagTraces_pre hsat hE hts hd fun _ _ => trivial
  · exact absurd hc memAccept_not_write
  · exact hpre w op args r hd'

/-! ## Fixed environments -/

variable {Op Y H : Type} [DecidableEq H] {W : Writer Op Y}

omit [DecidableEq H] in
theorem lookupAll_extends {σ ρ : Env H Y} (he : σ.Extends ρ) :
    ∀ {hs : List H} {ts : List Y}, σ.lookupAll hs = some ts → ρ.lookupAll hs = some ts
  | [], ts, h => h
  | h₀ :: hs, ts, h => by
      simp only [Env.lookupAll, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h ⊢
      obtain ⟨x, hx, xs, hxs, rfl⟩ := h
      exact ⟨x, he hx, xs, lookupAll_extends he (hs := hs) hxs, rfl⟩

omit [DecidableEq H] in
theorem built_extends {σ ρ : Env H Y} (he : σ.Extends ρ) {op : Op} {args : List H} {t : Y}
    (h : W.built σ op args = some t) : W.built ρ op args = some t := by
  unfold Writer.built at h ⊢
  rcases hl : σ.lookupAll args with _ | ts
  · simp [hl] at h
  · rw [hl] at h
    rw [lookupAll_extends he hl]
    exact h

/-- The invariant of a run in the fixed environment `ρ`. -/
def FInv (ρ : Env H Y) (s : WState H Y) : Prop := s.phase ≠ .chaos ∧ s.store.Extends ρ

/-- What a write answered in the fixed environment `ρ` returns. -/
def WriteOk (W : Writer Op Y) (sent : Option H) (ρ : Env H Y) (op : Op) (args : List H)
    (r : H) : Prop :=
  sent = some r ∨ ∃ t, W.built ρ op args = some t ∧ ρ r = some t

/-- Where an accepted tree comes from. -/
def AcceptedBy (ρ : Env H Y) (x : Y) (e : WEv Op H) : Prop :=
  (∃ h, e = .accept h ∧ ρ h = some x) ∨ (∃ h b, e = .acceptErr h b) ∨ e = .acceptAll ∨
    ∃ k, e = .acceptBatch k

theorem step_fixed {pol : Policy H} {ρ : Env H Y} {s s' : WState H Y} {e : WEv Op H}
    {A : Set Y} (hs : WStep W pol (some ρ) s e s' A) (hI : FInv ρ s) :
    FInv ρ s' ∧ (∀ op args r, e = .write op args r → WriteOk W pol.sentinel ρ op args r) ∧
      ∀ x ∈ A, AcceptedBy ρ x e := by
  obtain ⟨hp, hst⟩ := hI
  cases hs with
  | @writeOk σ B op args r t hbt _ hag =>
      have hr : ρ r = some t := hag ρ rfl
      refine ⟨⟨by simp, fun h y hy => ?_⟩, ?_, by simp⟩
      · by_cases hh : h = r
        · subst hh; simp at hy; exact hy ▸ hr
        · simp [Function.update_of_ne hh] at hy; exact hst hy
      · rintro op' args' r' he
        cases he
        exact .inr ⟨t, built_extends hst hbt, hr⟩
  | writeFail hsn _ =>
      refine ⟨⟨hp, hst⟩, ?_, by simp⟩
      rintro op' args' r' he
      cases he
      exact .inl hsn
  | writeChaos _ _ hfix => cases hfix
  | @writeFixed σ B op args r t ρ' _ _ hfix hbt _ hr =>
      cases hfix
      refine ⟨⟨by simp, fun h y hy => ?_⟩, ?_, by simp⟩
      · by_cases hh : h = r
        · subst hh; simp at hy; exact hy ▸ hr
        · simp [Function.update_of_ne hh] at hy; exact hst hy
      · rintro op' args' r' he
        cases he
        exact .inr ⟨t, hbt, hr⟩
  | @acceptOk σ B h t hh =>
      refine ⟨⟨hp, hst⟩, by simp, ?_⟩
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact .inl ⟨h, rfl, hst hh⟩
  | acceptCallTrap => exact ⟨⟨by simp, hst⟩, by simp, by simp⟩
  | acceptSessionTrap => exact ⟨⟨by simp, hst⟩, by simp, by simp⟩
  | acceptIgnore => exact ⟨⟨hp, hst⟩, by simp, by simp⟩
  | acceptChaos _ _ hfix => cases hfix
  | @acceptFixed σ B h ρ' _ _ hfix =>
      cases hfix
      exact ⟨⟨hp, hst⟩, by simp, fun x hx => .inl ⟨h, rfl, hx⟩⟩
  | acceptErrOk => exact ⟨⟨hp, hst⟩, by simp, fun _ _ => .inr (.inl ⟨_, _, rfl⟩)⟩
  | acceptErrBad => exact ⟨⟨hp, hst⟩, by simp, by simp⟩
  | acceptAll => exact ⟨⟨hp, hst⟩, by simp, fun _ _ => .inr (.inr (.inl rfl))⟩
  | acceptBatch k => exact ⟨⟨hp, hst⟩, by simp, fun _ _ => .inr (.inr (.inr ⟨k, rfl⟩))⟩
  | enter => exact ⟨⟨hp, hst⟩, by simp, by simp⟩
  | resume => exact ⟨⟨by simp, hst⟩, by simp, by simp⟩
  | chaos => exact absurd rfl hp

theorem run_fixed {pol : Policy H} {ρ : Env H Y} {s s' : WState H Y} {t : List (WEv Op H)}
    {A : Set Y} (hr : (writer W pol (some ρ)).Run s t s' A) (hI : FInv ρ s) :
    (∀ op args r, WEv.write op args r ∈ t → WriteOk W pol.sentinel ρ op args r) ∧
      ∀ x ∈ A, ∃ e ∈ t, AcceptedBy ρ x e := by
  induction hr with
  | nil => exact ⟨by simp, by simp⟩
  | cons hs _ ih =>
      obtain ⟨hI', hw, hA⟩ := step_fixed hs hI
      obtain ⟨hw', hA'⟩ := ih hI'
      refine ⟨fun op args r hm => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.1 hm with he | hm
        · exact hw op args r he.symm
        · exact hw' op args r hm
      · rcases hx with hx | hx
        · exact ⟨_, List.mem_cons_self, hA x hx⟩
        · obtain ⟨e, he, h⟩ := hA' x hx
          exact ⟨e, List.mem_cons_of_mem _ he, h⟩

/-- **The memory writer bridge in a fixed environment.** -/
theorem memFixedLang_subset {P : Numerics.Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : MemImports} {pol : Policy (BitVec 32)}
    {ρ : Env (BitVec 32) SymStrBytesSExp} {L : Set SymStrBytesSExp}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : MemSat P m memIdx (memRoles ix) (writerContract ix pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) :
    fixedLang (sexpW MemAtom) pol {ρ} (memTraces P Envs memIdx m ix) ⊆ L := by
  intro x hx
  simp only [fixedLang, langOver, Set.mem_iUnion] at hx
  obtain ⟨⟨ρ', hρ'⟩, hx⟩ := hx
  rw [Set.mem_singleton_iff] at hρ'
  subst ρ'
  obtain ⟨t, ⟨ts, hts, rfl⟩, s, A, hr, hxA⟩ := mem_lang.1 hx
  obtain ⟨hwr, hacc⟩ := run_fixed hr ⟨by simp [writer, WState.init],
    fun _ _ h => by simp [writer, WState.init, Env.empty] at h⟩
  obtain ⟨ev, hev, hby⟩ := hacc x hxA
  have hall : ∀ y, Tag.inp y ∈ ts → (writerContract ix pol.sentinel ρ L reply).ans y := by
    rintro y hy op args r rfl
    exact hwr op args r (mem_inputsOf_of_inp hy)
  rcases hby with ⟨h, rfl, hρ⟩ | ⟨h, b, rfl⟩ | rfl | ⟨k, rfl⟩
  · obtain ⟨u, v, hu⟩ := List.append_of_mem hev
    obtain ⟨u', v', hd, -⟩ := inputsOf_split (e := WEv.enter) (by simp) hu
    obtain ⟨o, hpre, hc | ⟨w, hd'⟩⟩ := tagTraces_pre hsat hE hts hd
      fun y hy => hall y (by rw [hd]; exact List.mem_append_left _ hy)
    · exact hpre h hc x hρ
    · exact absurd hd' memWrite_ne_accept
  all_goals
    rcases mem_inputsOf hev with hi | hi
    · obtain ⟨u, v, hu⟩ := List.append_of_mem hi
      obtain ⟨o, -, hc | ⟨w, hd'⟩⟩ := tagTraces_pre hsat hE hts hu
        fun y hy => hall y (by rw [hu]; exact List.mem_append_left _ hy)
      · obtain ⟨_, he⟩ := memAccept_isAccept hc; cases he
      · obtain ⟨_, _, _, he⟩ := memWrite_isWrite hd'; cases he
    · cases hi

/-- **The memory writer bridge** (store semantics, no undefined behaviour). -/
theorem memWriterLang_subset {P : Numerics.Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : MemImports} {pol : Policy (BitVec 32)}
    {L : Set SymStrBytesSExp} {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (memRoles ix) (writerContract ix pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : memWriterLang P Envs memIdx m ix pol ⊆ L := by
  intro x hx
  have hx' := writerLang_subset_fixedLang hw ha _ hx
  rw [fixedLang, langOver, Set.mem_iUnion] at hx'
  obtain ⟨⟨ρ, _⟩, hρx⟩ := hx'
  refine memFixedLang_subset (pol := {pol with onAccept := .ub}) (ρ := ρ) (hsat ρ) hE ?_
  simp only [fixedLang, langOver, Set.mem_iUnion]
  exact ⟨⟨ρ, rfl⟩, hρx⟩

/-! ## The memory-returning reader -/

theorem mem_reads {Q A H' : Type} {q : Q} {a : A} :
    ∀ {t : List (REv Q A H')}, REv.read q a ∈ t → (q, a) ∈ REv.reads t
  | [], h => by simp at h
  | e :: t, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp [REv.reads]
      · have := mem_reads h
        cases e <;> simp [REv.reads, this]

theorem itemsRead_ne_accept {ix : ReadImports} {o : Callout} {w : HostReply} {h : BitVec 32} :
    itemsRead ix o w ≠ some (.accept h) := by
  unfold itemsRead
  split
  · split <;> simp
  · simp

theorem readAccept_isAccept {ix : ReadImports} {o : Callout} {ev : MemREv}
    (h : readAccept ix o = some ev) : ∃ h, ev = .accept h := by
  unfold readAccept at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨h, -, rfl⟩ := h
    exact ⟨h, rfl⟩
  · cases h

/-- **The memory reader bridge**: under the trapping read policy and no accept UB, the reader
language over every set of fixed environments is included in `L`. -/
theorem memReaderLang_subset {P : Numerics.Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : ReadImports} {L : Set SymStrBytesSExp}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (memReadRoles ix) (readerContract ix ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Env (BitVec 32) SymStrBytesSExp)) :
    memReaderLang P Envs memIdx m ix .trap oa Rhos ⊆ L := by
  refine readerLang_trap_subset hoa (cert := fun hist h => ∀ ρ : Env (BitVec 32) SymStrBytesSExp,
      (∀ p ∈ hist, (sexpR MemAtom (BitVec 32)).valid ρ p.1 ∧
        (sexpR MemAtom (BitVec 32)).ok ρ p.1 p.2) → ∀ t, ρ h = some t → t ∈ L)
    (fun ρ hist h hh hc => hc ρ hh) ?_ Rhos
  rintro _ ⟨ts, hts, rfl⟩ u v h hu ρ hreads
  obtain ⟨u', v', hd, rfl⟩ := inputsOf_split (e := REv.enter) (by simp) hu
  have hall : ∀ y, Tag.inp y ∈ u' → (readerContract ix ρ L reply).ans y := by
    rintro y hy q a rfl
    exact hreads (q, a) (mem_reads (mem_inputsOf_of_inp hy))
  obtain ⟨o, hpre, hc | ⟨w, hd'⟩⟩ := tagTraces_pre (hsat ρ) hE hts hd hall
  · exact hpre h hc
  · exact absurd hd' itemsRead_ne_accept

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
