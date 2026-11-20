module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Pull.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun

/-!
# Proofs: pull-style chunked input

* `run_short`: a run of the parsing host (`Silmaril.Accept.Parse.parser`) over a trace of chunk
  feeds and finishes of at most `k` bytes relates only inputs of at most `k` bytes, for every
  policy without undefined behaviour.
* `echo_sat`: `echoMod` meets the contract "every `finish(used, h)` call has `used ≤ 16`" under
  the hosts of `echoReply` (Hoare logic: `used` is the result of `read(0, 16)`, which the
  admitted hosts bound by `16`); `echo_short` (with the bridge `tagTraces_pre`): every input
  `echoMod` relates has at most `16` bytes.
* `echo_traces`, `echo_live`: against `echoEnv` (writes `68 69`, returns `2`), the parsing trace
  `[feed [68, 69], finish 2 7]`, which relates `68 69` to the tree of `7`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Accept.Parse Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Game.HandleAccept.MemSound.Pull
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt)

/-! ## Parsing runs over short finishes -/

section Runs

variable {V H X : Type} [DecidableEq H] {pol : PPolicy H} {ρ : Silmaril.Accept.Handle.Env H X}

omit [DecidableEq H] in
theorem returns_phase {s s' : PState V} {e : PEv V H} {w : List V} {h : H}
    (hR : Returns pol s e w h s') : s'.phase = s.phase := by
  cases e with
  | parse v h₀ => simp only [Returns] at hR; obtain ⟨-, -, rfl⟩ := hR; rfl
  | done h₀ => simp only [Returns] at hR; obtain ⟨-, -, rfl⟩ := hR; rfl
  | finish n h₀ => simp only [Returns] at hR; obtain ⟨-, -, -, rfl⟩ := hR; rfl
  | append v => exact hR.elim
  | feed c => exact hR.elim
  | reset => exact hR.elim

theorem resolve_fst {w : List V} {h : H} {A : Set (List V × X)} {p : List V × X}
    (hres : resolve pol ρ w h = some A) (hp : p ∈ A) : p.1 = w := by
  unfold resolve at hres
  split_ifs at hres
  · cases hres
    simp at hp
  · obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 hres
    rw [Set.mem_singleton_iff] at hp
    rw [hp]

/-- The events of pull-style traces, with finishes of at most `k` bytes. -/
def ShortEv (k : Nat) (e : PEv V H) : Prop := (∃ c, e = .feed c) ∨ ∃ n h, e = .finish n h ∧ n ≤ k

theorem step_short (hb : pol.onBadHandle ≠ .ub) (ho : pol.onOverrun ≠ .ub) {k : Nat}
    {s s₁ : PState V} {e : PEv V H} {A : Set (List V × X)} (hst : PStep pol ρ s e s₁ A)
    (hs : s.phase ≠ .chaos) (he : ShortEv k e) :
    s₁.phase ≠ .chaos ∧ ∀ p ∈ A, p.1.length ≤ k := by
  cases hst with
  | ret hl hR hres =>
    refine ⟨by rw [returns_phase hR]; exact hs, fun p hp => ?_⟩
    rw [resolve_fst hres hp]
    rcases he with ⟨c, rfl⟩ | ⟨n, h, rfl, hn⟩
    · exact hR.elim
    · simp only [Returns] at hR
      obtain ⟨-, rfl, -, -⟩ := hR
      exact (List.length_take_le _ _).trans hn
  | retBadIgnore hl hR _ _ =>
    exact ⟨by rw [returns_phase hR]; exact hs, fun p hp => by simp at hp⟩
  | retBadSessionTrap _ _ _ _ => exact ⟨by simp, fun p hp => by simp at hp⟩
  | retBadUB _ _ _ h => exact absurd h hb
  | append v => exact ⟨by simp, fun p hp => by simp at hp⟩
  | feed c => exact ⟨by simp, fun p hp => by simp at hp⟩
  | overrunIgnore _ _ => exact ⟨by simp, fun p hp => by simp at hp⟩
  | overrunUB _ h => exact absurd h ho
  | reset => exact ⟨by simp, fun p hp => by simp at hp⟩
  | chaos _ h => exact absurd h hs

/-- **Short finishes relate short inputs.** -/
theorem run_short (hb : pol.onBadHandle ≠ .ub) (ho : pol.onOverrun ≠ .ub) {k : Nat} :
    ∀ {s : PState V} {t : List (PEv V H)} {s' : PState V} {A : Set (List V × X)},
      (parser pol ρ).Run s t s' A → s.phase ≠ .chaos → (∀ e ∈ t, ShortEv k e) →
      ∀ p ∈ A, p.1.length ≤ k := by
  intro s t s' A hr
  induction hr with
  | nil s => intro _ _ p hp; simp at hp
  | cons hst _ ih =>
    intro hs ht p hp
    obtain ⟨hs₁, hA⟩ := step_short hb ho hst hs (ht _ List.mem_cons_self)
    rcases hp with hp | hp
    · exact hA p hp
    · exact ih hs₁ (fun e he => ht e (List.mem_cons_of_mem _ he)) p hp

end Runs

/-! ## Decoded events -/

theorem mem_inputsOf_none {X I O C : Type} {x : I} :
    ∀ {ts : List (Tag X I O C)}, x ∈ inputsOf none ts → Tag.inp x ∈ ts
  | [], h => by simp [inputsOf] at h
  | .inp j :: ts, h => by
      simp only [inputsOf, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_inputsOf_none h)
  | .enter _ :: ts, h => by
      simp only [inputsOf, Option.toList_none, List.nil_append] at h
      exact List.mem_cons_of_mem _ (mem_inputsOf_none h)
  | .out _ :: ts, h => by
      simp only [inputsOf] at h
      exact List.mem_cons_of_mem _ (mem_inputsOf_none h)
  | .exit _ :: ts, h => by
      simp only [inputsOf] at h
      exact List.mem_cons_of_mem _ (mem_inputsOf_none h)

theorem pullRead_feed {ix : PullImports} {o : Callout} {w : HostReply} {e : PullEv}
    (h : pullRead ix o w = some e) : ∃ c, e = .feed c := by
  unfold pullRead at h
  split_ifs at h
  split at h
  · obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨c, rfl⟩
  · cases h

theorem pullFinish_finish {ix : PullImports} {o : Callout} {e : PullEv}
    (h : pullFinish ix o = some e) : ∃ n h, e = .finish n h := by
  unfold pullFinish at h
  split_ifs at h
  split at h
  · obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨n, _, rfl⟩
  · cases h

/-! ## The contract of `echoMod` -/

/-- Every `finish` call reports at most `16` bytes. -/
abbrev echoK : MemContract PullEv where
  pre o := ∀ n h, pullFinish {} o = some (.finish n h) → n ≤ 16
  reply := echoReply

/-- **Every input of a module meeting `echoK` has at most `16` bytes.** -/
theorem short_of_sat {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {m : Module}
    {Inv : Store Nat → Prop} (hsat : MemSat P m 0 (pullRoles {}) echoK Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs echoReply s L) {X : Type} {pol : PPolicy (BitVec 32)}
    (hb : pol.onBadHandle ≠ .ub) (ho : pol.onOverrun ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)) :
    inputLang (pullRel P Envs 0 m {} pol Rhos) ⊆ {w | w.length ≤ 16} := by
  rintro w ⟨⟨w', x⟩, hp, rfl⟩
  simp only [pullRel, parseRel, langOver, Host.lang, Set.mem_iUnion] at hp
  obtain ⟨ρ, t, ⟨ts, hts, rfl⟩, s', A, hr, hA⟩ := hp
  refine run_short hb ho hr (by simp [parser, PState.init]) (fun e he => ?_) _ hA
  obtain ⟨u, v, hd⟩ := List.append_of_mem (mem_inputsOf_none he)
  obtain ⟨o, hpre, hc | ⟨w, hd'⟩⟩ := tagTraces_pre hsat hE hts hd fun _ _ => trivial
  · obtain ⟨n, h, rfl⟩ := pullFinish_finish hc
    exact .inr ⟨n, h, rfl, hpre n h hc⟩
  · exact .inl (pullRead_feed hd')

/-! ## The Hoare-logic proof of `echoMod` -/

/-- The shape of the instantiated module. -/
def echoOk : Bool :=
  match prep echoMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 2 f₀ && stubOk 1 2 f₁ &&
          fnOk [] echoBody 0 0 [0, 1, 2] [0] [] f₂
       | _ => false)
  | none => false

theorem echoOk_true : echoOk = true := by decide +kernel

theorem echo_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep echoMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧ stubOk 0 2 f₀ = true ∧
      stubOk 1 2 f₁ = true ∧ fnOk [] echoBody 0 0 [0, 1, 2] [0] [] f₂ = true := by
  have h := echoOk_true
  unfold echoOk at h
  rw [hp] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  split at h6
  · rename_i f₀ f₁ f₂ hf
    simp only [Bool.and_eq_true] at h6
    exact ⟨f₀, f₁, f₂, hf, h6.1.1, h6.1.2, h6.2⟩
  · cases h6

/-- The store invariant: the instantiated functions and one memory. -/
def echoInv (s : Store Nat) : Prop :=
  ∃ c st, prep echoMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

theorem finish_used {s : Store Nat} {v h : BitVec 32} {n : Nat}
    (hd : pullFinish {} (calloutIn ⟨"input", "finish", .func ⟨1⟩⟩ (some 0) s [.i32 v, .i32 7]) =
      some (.finish n h)) : n = v.toNat := by
  simp only [pullFinish, calloutIn, Val.i32, ↓reduceIte, usedOfI32, Option.map_eq_some_iff] at hd
  obtain ⟨n', hn', he⟩ := hd
  cases he
  split_ifs at hn'
  cases hn'
  rfl

/-- **The body of `run`.** -/
theorem echo_body {P : Profile} {c : Config Nat} {st : Option FuncIdx}
    (hp : prep echoMod = some (c, st)) {f₀ f₁ f₂ : FuncInst Nat}
    (hf : c.store.funcs = [f₀, f₁, f₂]) (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 2 f₁ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2]) {s : Store Nat}
    (hs : echoInv s) {Q : Post Nat} (hQ : BodyExits echoInv Q) :
    HWP P (memHost echoMod (some 0) (pullRoles {}) echoK) s F
      (vals [] ++ expression echoBody) Q := by
  obtain ⟨c', st', hp', hsf, hml⟩ := hs
  have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
  rw [hcc, hf] at hsf
  have hinv : ∀ s', s'.funcs = s.funcs → s'.mems.length = s.mems.length → echoInv s' :=
    fun s' h1 h2 => ⟨c, st, hp, by rw [h1, hsf, hf], by rw [h2, hml]⟩
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  unfold echoBody
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine hwp_call (us := []) (args := [.i32 0, .i32 16]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := ⟨"input", "read", .func ⟨0⟩⟩) (by rw [hFf]; rfl) (by rw [hsf]; rfl) hc₀ he₀
    (by simp [hn₀]) rfl (fun n h hd => by simp [pullFinish, calloutIn] at hd) ?_
  rintro s' r ⟨⟨hfs', hml'⟩, hshape⟩ -
  have hs' : echoInv s' := hinv s' hfs' hml'
  refine ⟨fun res hr => ?_, fun _ => (hQ s' hs' F).2.2.1, fun a _ => (hQ s' hs' F).2.2.2 a⟩
  obtain ⟨v, rfl, hv⟩ := (hshape res hr).1 rfl
  have hv16 : v.toNat ≤ 16 := hv 0 16 rfl
  refine X.i32Const (us := [] ++ [.i32 v]) ?_
  refine hwp_call (us := []) (args := [.i32 v, .i32 7]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := ⟨"input", "finish", .func ⟨1⟩⟩) (by rw [hFf]; rfl) (by rw [hfs', hsf]; rfl) hc₁ he₁
    (by simp [hn₁]) rfl (fun n h hd => by rw [finish_used hd]; exact hv16) ?_
  rintro s'' r' ⟨⟨hfs'', hml''⟩, hshape'⟩ -
  have hs'' : echoInv s'' := hinv s'' (hfs''.trans hfs') (hml''.trans hml')
  refine ⟨fun res hr => ?_, fun _ => (hQ s'' hs'' F).2.2.1, fun a _ => (hQ s'' hs'' F).2.2.2 a⟩
  obtain rfl := (hshape' res hr).2 rfl
  exact X.done (hQ s'' hs'' F).1

/-- **`echoMod` meets its contract**, for every profile. -/
theorem echo_sat (P : Profile) : MemSat P echoMod 0 (pullRoles {}) echoK echoInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := echo_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 2 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, -, hrs, hfuncs, -, -⟩ := fnOk_spec h2
  refine export_valid (fi := f₂) (fun s hs => ?_) hcode2 he hrs ?_
  · obtain ⟨c', st', hp', hfs, _⟩ := hs
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc, hf]
    rfl
  · intro s args hs _ Q hQ
    rw [hbody]
    exact echo_body hp hf h0 h1 (by simp [Frame.forCall, hfuncs]) hs hQ

/-- **`echoMod` relates only inputs of at most `16` bytes** (no undefined behaviour). -/
theorem echo_short (P : Profile) {X : Type} {pol : PPolicy (BitVec 32)}
    (hb : pol.onBadHandle ≠ .ub) (ho : pol.onOverrun ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)) :
    inputLang (pullRel P (ReplyEnvs echoReply) 0 echoMod {} pol Rhos) ⊆
      {w | w.length ≤ 16} :=
  short_of_sat (echo_sat P) (fun _ _ h => h) hb ho Rhos

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull
