module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Probe.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Langs

/-!
# Proofs: the probe reader accepts only trees meeting the facts of its two reads

* `probe_body`: the body of `check` under the most general host of the reader contract in a
  fixed environment `ρ`. The correct read of `next(h, 0)` returns `c` with
  `Rd.ok ρ (q₂ h 0) (a₂ c)`; the correct read of `leaf(c, 0)` gives `Rd.ok ρ (q₃ c) a` for the
  answer `a` decoded from the reply; at `accept(h)` the hypothesis `ProbeFacts` turns these
  two facts into `t ∈ L` for the tree `t` that `h` denotes;
* `probe_sat`, `probeLang_subset` (the reader bridge for the probe roles, any reader), and
  `probe_sound`;
* `nary_facts`, `cons_facts`, `ast_facts`: the facts of the three probes (`firstAtoms`,
  `carAtoms`, `firstLeaves`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.IO Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Probe
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {Qy An Y α : Type}

/-- **The facts of the probe imply membership**: a correct read of `next(h, 0)` returning `c`
and a correct read of `leaf(c, 0)` (for every reply) make every tree `h` denotes a member of
`L`. -/
def ProbeFacts (Rd : Reader Qy An (BitVec 32) Y) (d : ProbeDec Qy An) (L : Set Y) : Prop :=
  ∀ (ρ : Env (BitVec 32) Y) h c w t, Rd.ok ρ (d.q₂ h 0) (d.a₂ c) → Rd.ok ρ (d.q₃ c) (d.a₃ w 0) →
    ρ h = some t → t ∈ L

/-! ## Instance facts -/

/-- The shape of the instantiated module (and distinct `next` and `leaf` names). -/
def probeOk (ix : ProbeImports) : Bool :=
  ix.leaf != ix.next &&
  match prep (probeMod ix) with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [3] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂, f₃] => stubOk 0 2 f₀ && stubOk 1 2 f₁ && stubOk 2 1 f₂ &&
          fnOk [] probeBody 1 0 [0, 1, 2, 3] [0] [] f₃
       | _ => false)
  | none => false

theorem probe_facts {ix : ProbeImports} (hok : probeOk ix = true) {c : Config Nat}
    {st : Option FuncIdx} (hp : prep (probeMod ix) = some (c, st)) :
    ix.leaf ≠ ix.next ∧ st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧
    exportFuncAddrs c.frame.module = [3] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂ f₃, c.store.funcs = [f₀, f₁, f₂, f₃] ∧
      stubOk 0 2 f₀ = true ∧ stubOk 1 2 f₁ = true ∧ stubOk 2 1 f₂ = true ∧
      fnOk [] probeBody 1 0 [0, 1, 2, 3] [0] [] f₃ = true := by
  unfold probeOk at hok
  rw [hp] at hok
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at hok
  obtain ⟨hne, ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩⟩ := hok
  refine ⟨hne, h1, h2, h3, h4, h5, ?_⟩
  split at h6
  · rename_i f₀ f₁ f₂ f₃ hf
    simp only [Bool.and_eq_true] at h6
    exact ⟨f₀, f₁, f₂, f₃, hf, h6.1.1.1, h6.1.1.2, h6.1.2, h6.2⟩
  · cases h6

/-- The store invariant: the instantiated functions and one memory. -/
def probeInv (ix : ProbeImports) (s : Store Nat) : Prop :=
  ∃ c st, prep (probeMod ix) = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The reader contract of the probe in the fixed environment `ρ`. -/
abbrev probeK (Rd : Reader Qy An (BitVec 32) Y) (d : ProbeDec Qy An) (L : Set Y)
    (ρ : Env (BitVec 32) Y) : MemContract (REv Qy An (BitVec 32)) :=
  probeContract Rd d ρ L probeReply

/-! ## The decoder -/

theorem probeAccept_inv {ix : ProbeImports} {o : Callout} {v : Val} {h : BitVec 32}
    (ha : o.args = [v]) (hd : probeAccept (Q := Qy) (A := An) ix o = some (.accept h)) :
    v = .i32 h := by
  unfold probeAccept at hd
  split at hd
  · simp only [ha, Callout.args1, Option.map_eq_some_iff, REv.accept.injEq] at hd
    obtain ⟨a, hi, rfl⟩ := hd
    exact i32?_some hi
  · cases hd

theorem probeAccept_two {ix : ProbeImports} {o : Callout} {a b : Val} {h : BitVec 32}
    (ha : o.args = [a, b]) : probeAccept (Q := Qy) (A := An) ix o ≠ some (.accept h) := by
  unfold probeAccept
  split
  · simp [ha, Callout.args1]
  · simp

theorem probeRead_ne_accept {d : ProbeDec Qy An} {o : Callout} {w : HostReply} {h : BitVec 32} :
    probeRead d o w ≠ some (.accept h) := by
  unfold probeRead
  split
  · split <;> simp
  · split
    · split <;> simp
    · simp

/-! ## The body -/

/-- **The body of `check`**, in the fixed environment `ρ`. -/
theorem probe_body {P : Profile} {Rd : Reader Qy An (BitVec 32) Y} {d : ProbeDec Qy An}
    {L : Set Y} (hL : ProbeFacts Rd d L) (hne : d.ix.leaf ≠ d.ix.next)
    {ρ : Env (BitVec 32) Y} {f₀ f₁ f₂ : FuncInst Nat}
    (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 2 f₁ = true) (h2 : stubOk 2 1 f₂ = true)
    {v : Val} {F : Frame}
    (hFf : F.module.funcs = [0, 1, 2, 3]) (hFl : F.locals = [some v])
    {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁, f₂] ++ fs.drop 3) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → probeInv d.ix s') {Q : Post Nat}
    (hQ : BodyExits (probeInv d.ix) Q) :
    HWP P (memHost (probeMod d.ix) (some 0) (probeRoles d) (probeK Rd d L ρ)) s F
      (vals [] ++ expression probeBody) Q := by
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  have htrap : ∀ s' (F' : Frame), s'.funcs = fs → s'.mems.length = 1 → Q s' F' .trap :=
    fun s' F' h h' => (hQ s' (hinv s' h h') F').2.2.1
  have hthrow : ∀ s' (F' : Frame) a, s'.funcs = fs → s'.mems.length = 1 →
      Q s' F' (.throw a) :=
    fun s' F' a h h' => (hQ s' (hinv s' h h') F').2.2.2 a
  have hv : F.local? ⟨0⟩ = some (some v) := by simp [Frame.local?, hFl, Idx.toNat]
  unfold probeBody
  -- next(h, 0)
  refine X.localGet (us := []) hv ?_
  refine X.i32Const (us := [] ++ [v]) ?_
  refine hwp_call (us := []) (args := [v, .i32 0]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := ⟨d.ix.next.1, d.ix.next.2, .func ⟨0⟩⟩) (by rw [hFf]; rfl) (by rw [hsf, hfs]; rfl)
    hc₀ he₀ (by simp [hn₀]) rfl (fun _ hd => absurd hd (probeAccept_two rfl)) ?_
  rintro s₁ r ⟨⟨hfs₁, hml₁⟩, hshape⟩ hans
  have hfs₁' : s₁.funcs = fs := hfs₁.trans hsf
  have hml₁' : s₁.mems.length = 1 := hml₁.trans hml
  refine ⟨fun res hr => ?_, fun _ => htrap s₁ F hfs₁' hml₁',
    fun a _ => hthrow s₁ F a hfs₁' hml₁'⟩
  obtain ⟨c, rfl⟩ := (hshape res hr).1 rfl
  subst hr
  have hfact : ∀ h, v = .i32 h → Rd.ok ρ (d.q₂ h 0) (d.a₂ c) := by
    rintro h rfl
    have hd : probeRead d (calloutIn ⟨d.ix.next.1, d.ix.next.2, .func ⟨0⟩⟩ (some 0) s
        [.i32 h, .i32 0]) ⟨.values [.i32 c], memOf (some 0) s₁⟩ =
        some (.read (d.q₂ h 0) (d.a₂ c)) := by
      simp [probeRead, calloutIn, Val.i32]
    exact (hans _ hd _ _ rfl).2
  -- leaf(c, 0)
  refine X.i32Const (us := [] ++ [.i32 c]) ?_
  refine hwp_call (us := []) (args := [.i32 c, .i32 0]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := ⟨d.ix.leaf.1, d.ix.leaf.2, .func ⟨1⟩⟩) (by rw [hFf]; rfl) (by rw [hfs₁', hfs]; rfl)
    hc₁ he₁ (by simp [hn₁]) rfl (fun _ hd => absurd hd (probeAccept_two rfl)) ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ hans₂
  have hfs₂' : s₂.funcs = fs := hfs₂.trans hfs₁'
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hml₁'
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F hfs₂' hml₂',
    fun a _ => hthrow s₂ F a hfs₂' hml₂'⟩
  obtain rfl := (hshape res hr).2 (.inl rfl)
  subst hr
  have hleaf : Rd.ok ρ (d.q₃ c) (d.a₃ ⟨.values [], memOf (some 0) s₂⟩ 0) := by
    have hd : probeRead d (calloutIn ⟨d.ix.leaf.1, d.ix.leaf.2, .func ⟨1⟩⟩ (some 0) s₁
        [.i32 c, .i32 0]) ⟨.values [], memOf (some 0) s₂⟩ =
        some (.read (d.q₃ c) (d.a₃ ⟨.values [], memOf (some 0) s₂⟩ 0)) := by
      simp [probeRead, calloutIn, Val.i32, hne]
    exact (hans₂ _ hd _ _ rfl).2
  -- accept(h)
  refine X.localGet (us := []) hv ?_
  refine hwp_call (us := []) (args := [v]) (x := ⟨2⟩) (k := 2) (fk := f₂)
    (i := ⟨d.ix.accept.1, d.ix.accept.2, .func ⟨2⟩⟩) (by rw [hFf]; rfl)
    (by rw [hfs₂', hfs]; rfl) hc₂ he₂ (by simp [hn₂]) rfl ?_ ?_
  · intro h hd t ht
    exact hL ρ h c _ t (hfact h (probeAccept_inv rfl hd)) hleaf ht
  rintro s₃ r ⟨⟨hfs₃, hml₃⟩, hshape⟩ -
  have hfs₃' : s₃.funcs = fs := hfs₃.trans hfs₂'
  have hml₃' : s₃.mems.length = 1 := hml₃.trans hml₂'
  refine ⟨fun res hr => ?_, fun _ => htrap s₃ F hfs₃' hml₃',
    fun a _ => hthrow s₃ F a hfs₃' hml₃'⟩
  obtain rfl := (hshape res hr).2 (.inr rfl)
  exact X.done (hQ s₃ (hinv s₃ hfs₃' hml₃') F).1

/-- **`probeMod d.ix` meets the reader contract** in every fixed environment, for every
profile. -/
theorem probe_sat (P : Profile) {Rd : Reader Qy An (BitVec 32) Y} {d : ProbeDec Qy An}
    (hok : probeOk d.ix = true) {L : Set Y} (hL : ProbeFacts Rd d L)
    (ρ : Env (BitVec 32) Y) :
    MemSat P (probeMod d.ix) 0 (probeRoles d) (probeK Rd d L ρ) (probeInv d.ix) := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨hne, rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, hf, h0, h1, h2, h3⟩ :=
    probe_facts hok hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 3 := by simpa using ha
  obtain ⟨code, ps, rs, hcode3, hloc, hbody, he, hps, hrs, hfuncs, -, -⟩ := fnOk_spec h3
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → probeInv d.ix s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, probeInv d.ix s → s.funcs = c.store.funcs := by
    rintro s ⟨c', st', hp', hfs, _⟩
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc]
  refine export_valid (fi := f₃) (fun s hs => by rw [hfi s hs, hf]; rfl) hcode3 he hrs ?_
  intro s args hs hok' Q hQ
  have hlen1 : args.length = 1 := by
    have := args_length (by rw [hfi s hs, hf]; rfl) he hok'
    rw [hps] at this
    exact this
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen1
  rw [hbody]
  have hml' : s.mems.length = 1 := by obtain ⟨_, _, _, _, h⟩ := hs; exact h
  have hFl : (Frame.forCall f₃.module [v] code.locals).locals = [some v] := by
    unfold Frame.forCall
    dsimp only
    rw [hloc]
    rfl
  exact probe_body (v := v) hL hne h0 h1 h2 (by simp [Frame.forCall, hfuncs]) hFl
    (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs) hml' hinv hQ

/-! ## The reader bridge -/

/-- **The probe reader bridge**: under the trapping read policy and no accept UB, the reader
language over every set of fixed environments is included in `L`. -/
theorem probeLang_subset {P : Numerics.Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {Rd : Reader Qy An (BitVec 32) Y} {d : ProbeDec Qy An}
    {L : Set Y} {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (probeRoles d) (probeContract Rd d ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Env (BitVec 32) Y)) :
    probeLang P Envs memIdx m Rd d .trap oa Rhos ⊆ L := by
  refine readerLang_trap_subset hoa (cert := fun hist h =>
      ∀ ρ : Env (BitVec 32) Y, (∀ p ∈ hist, Rd.valid ρ p.1 ∧ Rd.ok ρ p.1 p.2) →
        ∀ t, ρ h = some t → t ∈ L)
    (fun ρ hist h hh hc => hc ρ hh) ?_ Rhos
  rintro _ ⟨ts, hts, rfl⟩ u v h hu ρ hreads
  obtain ⟨u', v', hd, rfl⟩ := inputsOf_split (e := REv.enter) (by simp) hu
  have hall : ∀ y, Tag.inp y ∈ u' → (probeContract Rd d ρ L reply).ans y := by
    rintro y hy q a rfl
    exact hreads (q, a) (mem_reads (mem_inputsOf_of_inp hy))
  obtain ⟨o, hpre, hc | ⟨w, hd'⟩⟩ := tagTraces_pre (hsat ρ) hE hts hd hall
  · exact hpre h hc
  · exact absurd hd' probeRead_ne_accept

/-- **The probe accepts only members of `L`**, for every profile, every accept policy without
undefined behaviour and every set of fixed environments. -/
theorem probe_sound (P : Profile) {Rd : Reader Qy An (BitVec 32) Y} {d : ProbeDec Qy An}
    (hok : probeOk d.ix = true) {L : Set Y} (hL : ProbeFacts Rd d L) {oa : OnInvalid}
    (hoa : oa ≠ .ub) (Rhos : Set (Env (BitVec 32) Y)) :
    probeLang P (ReplyEnvs probeReply) 0 (probeMod d.ix) Rd d .trap oa Rhos ⊆ L :=
  probeLang_subset (fun ρ => probe_sat P hok hL ρ) (fun _ _ h => h) hoa Rhos

/-! ## The three probes -/

theorem nary_facts (pay : Payload α) :
    ProbeFacts (sexpR α (BitVec 32)) (naryProbe pay) (firstAtoms α) := by
  intro ρ h c w t h₂ h₃ ht
  obtain ⟨cs, x, hρ, hx, hc⟩ := h₂
  simp only [naryProbe] at hx h₃
  split at h₃
  · rename_i a _
    change ρ c = some (.atom a) at h₃
    rw [hc] at h₃
    cases h₃
    rw [hρ] at ht
    cases ht
    exact ⟨cs, a, rfl, by simpa using hx⟩
  · exact h₃.elim

theorem cons_facts (pay : Payload α) :
    ProbeFacts (consR α (BitVec 32)) (consProbe pay) (carAtoms α) := by
  intro ρ h c w t h₂ h₃ ht
  simp only [consProbe, ↓reduceIte] at h₂ h₃
  obtain ⟨x, y, hρ, hc⟩ := h₂
  split at h₃
  · rename_i a _
    change ρ c = some (.atom a) at h₃
    rw [hc] at h₃
    cases h₃
    rw [hρ] at ht
    cases ht
    exact ⟨a, y, rfl⟩
  · exact h₃.elim

theorem ast_facts (pay : Payload α) :
    ProbeFacts (astR (sexpSig α) (BitVec 32)) (astProbe pay) (firstLeaves α) := by
  intro ρ h c w t h₂ h₃ ht
  obtain ⟨v, cs, x, hρ, hx, hc⟩ := h₂
  simp only [astProbe] at hx h₃
  split at h₃
  · rename_i a _
    obtain ⟨ds, hd⟩ := h₃
    rw [hc] at hd
    cases hd
    rw [hρ] at ht
    cases ht
    exact ⟨v, cs, a, ds, rfl, by simpa using hx⟩
  · exact h₃.elim

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Probe
