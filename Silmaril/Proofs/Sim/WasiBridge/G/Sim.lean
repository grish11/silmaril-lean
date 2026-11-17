module

public import Silmaril.Proofs.Sim.WasiBridge.G.Method
public import Silmaril.Proofs.Sim.WasiBridge.G.Lps

/-!
# Process runs are simulator runs

**`procRun_wrun`**: every finite run of LPS's user machine with an `EnvS1` environment, on a
program of G instructions and `syscall`s, is matched by an interaction run of the simulator
code (environment answers by `S1Ans`, the `sys2wasi` adapter's), from any store encoding the
initial core, with the same observables, up to the part of the trace produced after the end of
the program.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.G

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec)
open Silmaril.X86 (Reg State MState Word Byte)
open Silmaril.Process (Memory)
open Silmaril.Process.LPS (Event)
open Silmaril.Process.LPS.Machines
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Sim.X86.G

variable {H : Type}

/-- Every instruction item is in the G fragment. -/
def GItems : List Item → Prop
  | [] => True
  | .ins i n :: p => (emit i n).isSome ∧ GItems p
  | .sys :: p => GItems p

theorem obsTrace_append (a b : List Event) : obsTrace (a ++ b) = obsTrace a ++ obsTrace b := by
  simp [obsTrace]

theorem evsObs_cons (mem : Memory) (e : HostEv) (evs : List HostEv) :
    evsObs mem (e :: evs) = evsObs mem [e] ++ evsObs mem evs := by
  simp [evsObs]

theorem obsTrace_writes (l : List Byte) (ch : Word) :
    obsTrace (l.map (.writeEv ch)) = l.map (.wr ch.toNat) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.map_cons, obsTrace, List.flatMap_cons, obsOfEvent] at ih ⊢; rw [ih]; rfl

theorem and255_lt (x : Nat) : x &&& 255 = (x &&& 255) % 256 :=
  (Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_right (by norm_num))).symm

theorem and255_toNat (x : Word) : (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and]
  have : (255#64).toNat = 2 ^ 8 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem sysArgs_list {s : Store H} {f : Frame} {σ : State} (hE : Enc s f σ) :
    sysArgs s f = some [σ.read .rax, σ.read .rdi, σ.read .rsi, σ.read .rdx, σ.read .r10,
      σ.read .r8, σ.read .r9] := sysArgs_enc hE

theorem lenWord_toNat {α : Type} {l : List α} (h : l.length < 2 ^ 63) :
    (Silmaril.Process.LPS.lenWord l).toNat = l.length := by
  simp only [Silmaril.Process.LPS.lenWord, Silmaril.Process.LPS.zw, BitVec.toNat_ofInt]
  omega

theorem wsrc_lt (mem : Memory) (buf n : Word) : (wsrc mem buf n).length < 2 ^ 63 := by
  have := wsrc_len mem buf n
  have h1 : Silmaril.Process.LPS.rwCountClamp n ≤ 0x7ffff000 := by
    simp only [Silmaril.Process.LPS.rwCountClamp, Silmaril.Process.LPS.MAX_RW_COUNT]; omega
  omega

/-- The run stopped at an unanswered `read` (not simulated: the G simulator has no memory). -/
def AtRead (evs : List HostEv) : Prop := ∃ args, evs.getLast? = some ⟨args, none⟩ ∧ args.head? = some 0

theorem atRead_cons {e : HostEv} {evs : List HostEv} (h : AtRead evs) : AtRead (e :: evs) := by
  obtain ⟨args, h1, h2⟩ := h
  refine ⟨args, ?_, h2⟩
  cases evs with
  | nil => simp at h1
  | cons x xs => rw [List.getLast?_cons_cons]; exact h1

/-- The conclusion of `procRun_wrun` for a store `s` and the remaining `items`. -/
private abbrev SimsAt (mem : Memory) (f : Frame) (s : Store H) (items : List Item)
    (tr : List Event) : Prop :=
  ∃ evs rest tr₁ tr₂, tr = tr₁ ++ tr₂ ∧ WRun (S1Ans mem) s f items evs rest ∧
    obsTrace tr₁ = evsObs mem evs ∧ (tr₂ = [] ∨ rest = [] ∨ AtRead evs)

/-- The induction motive of `procRun_wrun`. -/
private abbrev Sims {E : SysEnv} (Ok : E.Model → Prop) (mem : Memory) (f : Frame) (m : MState)
    (e : E.Model) (tr : List Event) : Prop :=
  ∀ (items : List Item) (s : Store H), Ok e → m.memory = mem → ItemsAt mem m.core.rip items →
    GItems items → Enc s f m.core → FlagsDef m.core → SimsAt mem f s items tr

private theorem sims_ins {E : SysEnv} {Ok : E.Model → Prop} {mem : Memory} {f : Frame}
    {m m' : MState} {e : E.Model} {tr : List Event} {i : Silmaril.X86.Ext.Instr} {n : Nat}
    {p : List Item} {s : Store H} (hs : lpsStep m = some m') (ih : Sims (H := H) Ok mem f m' e tr)
    (hok : Ok e) (hm : m.memory = mem) (hat : ItemsAt mem m.core.rip (.ins i n :: p))
    (hg : GItems (.ins i n :: p)) (hEnc : Enc s f m.core) (hσ : FlagsDef m.core) :
    SimsAt mem f s (.ins i n :: p) tr := by
  obtain ⟨hf, hns, hrest⟩ := hat
  obtain ⟨hemit, hgp⟩ := hg
  obtain ⟨code, hc⟩ := Option.isSome_iff_exists.mp hemit
  subst hm
  obtain ⟨σ', hx, hstep, hσ', hrip⟩ := lpsStep_ins hc hf hns hσ
  rw [hstep] at hs
  cases hs
  obtain ⟨-, s', he, hE', -⟩ := emit_sound hc hEnc hx
  obtain ⟨evs, rest, tr₁, tr₂, htr, hw, hobs, hend⟩ :=
    ih p s' hok rfl (by rw [hrip]; exact hrest) hgp hE' hσ'
  exact ⟨evs, rest, tr₁, tr₂, htr, .ins hc he hw, hobs, hend⟩

private theorem sims_step {E : SysEnv} {Ok : E.Model → Prop} {mem : Memory} {f : Frame}
    {m m' : MState} {e : E.Model} {tr : List Event} (hs : lpsStep m = some m')
    (ih : Sims (H := H) Ok mem f m' e tr) : Sims (H := H) Ok mem f m e tr := by
  intro items s hok hm hat hg hEnc hσ
  match items, hat, hg with
  | [], _, _ => exact ⟨[], [], [], tr, rfl, .stop s f [], rfl, .inr (.inl rfl)⟩
  | .ins i n :: p, hat, hg => exact sims_ins hs ih hok hm hat hg hEnc hσ
  | .sys :: p, ⟨hsys, _⟩, _ =>
    subst hm
    simp only [lpsStep, SysAt] at hs hsys
    simp only [hsys, ↓reduceIte] at hs
    cases hs

/-- A `write` answer: `ds` written, the process resumed with `rax = |ds|`. -/
private theorem sims_write {E : SysEnv} {Ok : E.Model → Prop} {mem : Memory} {f : Frame}
    {m : MState} {e' : E.Model} {ch : X86FlagChoices.Choice} {tr : List Event} {ds : List Byte}
    {p : List Item} {s : Store H}
    (ih : Sims (H := H) Ok mem f ⟨sysResume m.core ch (Silmaril.Process.LPS.lenWord ds), m.memory⟩
      e' tr)
    (hrax : m.core.read .rax = 1) (hok' : Ok e') (hne : ds ≠ [])
    (hpre : ds <+: wsrc m.memory (m.core.read .rsi) (m.core.read .rdx)) (hm : m.memory = mem)
    (hit : ItemsAt mem m.core.rip (.sys :: p)) (hg : GItems (.sys :: p)) (hEnc : Enc s f m.core)
    (hσ : FlagsDef m.core) :
    SimsAt mem f s (.sys :: p)
      (ds.map (.writeEv (Silmaril.Process.LPS.fd32 (m.core.read .rdi))) ++ tr) := by
  subst hm
  have hrest : ItemsAt m.memory (m.core.rip + 2) p := hit.2
  have hlen : ds.length ≤ (wsrc m.memory (m.core.read .rsi) (m.core.read .rdx)).length :=
    hpre.length_le
  have hlt : (wsrc m.memory (m.core.read .rsi) (m.core.read .rdx)).length < 2 ^ 63 :=
    wsrc_lt m.memory (m.core.read .rsi) (m.core.read .rdx)
  have hk : (Silmaril.Process.LPS.lenWord ds).toNat = ds.length := lenWord_toNat (by omega)
  let w : Word := (rflagsImage (X86FlagChoices.completeFlags m.core.flags ch)).getD 0
  have hE' : Enc (sysStore s f m.core.rip (Silmaril.Process.LPS.lenWord ds) w) f
      (sysResume m.core ch (Silmaril.Process.LPS.lenWord ds)) :=
    enc_sysStore hEnc hσ ch (Silmaril.Process.LPS.lenWord ds)
  obtain ⟨evs', rest, tr₁, tr₂, htr, hw, hobs, hend⟩ :=
    ih p (sysStore s f m.core.rip (Silmaril.Process.LPS.lenWord ds) w) hok' rfl hrest hg hE'
      (flagsDef_sysResume _ _ _)
  refine ⟨⟨_, some (Silmaril.Process.LPS.lenWord ds)⟩ :: evs', rest,
    ds.map (.writeEv (Silmaril.Process.LPS.fd32 (m.core.read .rdi))) ++ tr₁, tr₂,
    by rw [htr, List.append_assoc], .sys (sysArgs_list hEnc) hEnc.2.2.1 ?_ hw, ?_, ?_⟩
  · simp only [S1Ans, hrax, hk, true_and]
    exact ⟨List.length_pos_iff.2 hne, hlen⟩
  · rw [obsTrace_append, hobs, evsObs_cons, obsTrace_writes]
    congr 1
    simp only [evsObs, liftEv, hrax, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, sysObs, hk]
    rw [← List.prefix_iff_eq_take.1 hpre]
  · rcases hend with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (atRead_cons h))

private theorem sims_resume {E : SysEnv} {Ok : E.Model → Prop} {Chan : E.Model → Word → Prop}
    (hE : EnvS1 E Ok Chan) {mem : Memory} {f : Frame} {m m' : MState} {e e' : E.Model}
    {ch : X86FlagChoices.Choice} {evs tr : List Event} (hat : AtSyscall m)
    (harm : E.arm (trapped ⟨m, none⟩ ch) e (.resume m' e' evs))
    (ih : Sims (H := H) Ok mem f m' e' tr) : Sims (H := H) Ok mem f m e (evs ++ tr) := by
  intro items s hok hm hit hg hEnc hσ
  match items, hit, hg with
  | [], _, _ => exact ⟨[], [], [], evs ++ tr, rfl, .stop s f [], rfl, .inr (.inl rfl)⟩
  | .ins i n :: p, ⟨_, hns, _⟩, _ => exact (hns (hm ▸ hat)).elim
  | .sys :: p, hit, hg =>
    rcases hE.answers m e ch _ hok hat harm with ⟨hrax, ds, e'', hok', hne, hpre, ho⟩ |
      ⟨hrax, -⟩ | ⟨-, fs, ho⟩
    · obtain ⟨rfl, rfl, rfl⟩ := IoOut.resume.inj ho
      exact sims_write ih hrax hok' hne hpre hm hit hg hEnc hσ
    · subst hm
      exact ⟨[⟨_, none⟩], .sys :: p, [], evs ++ tr, rfl, .pending (sysArgs_list hEnc), by
        simp [evsObs, liftEv, hrax, obsTrace], .inr (.inr ⟨_, rfl, by simp [hrax]⟩)⟩
    · cases ho

private theorem sims_halt {E : SysEnv} {Ok : E.Model → Prop} {Chan : E.Model → Word → Prop}
    (hE : EnvS1 E Ok Chan) {mem : Memory} {f : Frame} {m : MState} {e : E.Model}
    {ch : X86FlagChoices.Choice} {evs : List Event} (hat : AtSyscall m)
    (harm : E.arm (trapped ⟨m, none⟩ ch) e (.halt evs)) : Sims (H := H) Ok mem f m e evs := by
  intro items s hok hm hit hg hEnc hσ
  match items, hit, hg with
  | [], _, _ => exact ⟨[], [], [], evs, rfl, .stop s f [], rfl, .inr (.inl rfl)⟩
  | .ins i n :: p, ⟨_, hns, _⟩, _ => exact (hns (hm ▸ hat)).elim
  | .sys :: p, ⟨_, _⟩, _ =>
    rcases hE.answers m e ch _ hok hat harm with ⟨_, _, _, _, _, _, ho⟩ | ⟨_, _, _, _, _, _, _, ho⟩ |
      ⟨hrax, fs, ho⟩
    · cases ho
    · cases ho
    · obtain rfl := IoOut.halt.inj ho
      refine ⟨[⟨_, none⟩], .sys :: p, _, [], (List.append_nil _).symm,
        .pending (sysArgs_list hEnc), ?_, .inl rfl⟩
      rcases hrax with h | h <;>
        simp [evsObs, liftEv, h, sysObs, obsTrace, obsOfEvent] <;> exact and255_lt _

/-- **Process runs are simulator runs**, up to the end of the program or a `read`. -/
theorem procRun_wrun {E : SysEnv} {Ok : E.Model → Prop} {Chan : E.Model → Word → Prop}
    (hE : EnvS1 E Ok Chan) {mem : Memory} {f : Frame}
    {m : MState} {e : E.Model} {tr : List Event} (hr : ProcRun lpsStep E m e tr) :
    ∀ (items : List Item) (s : Store H), Ok e → m.memory = mem → ItemsAt mem m.core.rip items →
      GItems items → Enc s f m.core → FlagsDef m.core →
      ∃ evs rest tr₁ tr₂, tr = tr₁ ++ tr₂ ∧ WRun (S1Ans mem) s f items evs rest ∧
        obsTrace tr₁ = evsObs mem evs ∧ (tr₂ = [] ∨ rest = [] ∨ AtRead evs) := by
  show Sims (H := H) Ok mem f m e tr
  induction hr with
  | stop m e =>
    exact fun items s _ _ _ _ _ _ => ⟨[], items, [], [], rfl, .stop s f items, rfl, .inl rfl⟩
  | step hs _ ih => exact sims_step hs ih
  | resume hat harm _ ih => exact sims_resume hE hat harm ih
  | halt hat harm => exact sims_halt hE hat harm

end Silmaril.Sim.WasiBridge.G
