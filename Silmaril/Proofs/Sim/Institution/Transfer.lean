module

public import Silmaril.Sim.Institution.Defs


/-!
# Proofs: transfer, linking and reductions in the institution of simulators

Names are in `Silmaril.Sim.Institution`, exported by `Silmaril/Sim/Institution/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.Institution

open CategoryTheory
open Silmaril.Sim (PState Prog Machine)
open scoped Silmaril.Inst

variable {V : Type}

/-! ## Transfer along model morphisms (soundness) -/

/-- **Sound simulators transfer angelic sentences**: a model morphism `A ⟶ B` (soundness)
carries every upward-closed angelic sentence from `A` to `B`. -/
theorem sat_of_hom {S : Sig V} {A B : Mod S} (f : A ⟶ B) {φ : Sen S} (hφ : φ.AngelicMono)
    (h : sat A φ) : sat B φ := by
  obtain ⟨s⟩ := f.down
  cases φ with
  | angelic P p Q => exact s.angelic hφ.1 hφ.2 h
  | demonic _ _ _ => exact hφ.elim

/-- **Complete simulators transfer demonic sentences.** -/
theorem sat_of_complete {S : Sig V} {A B : Mod S} (h : Silmaril.Sim.Complete A.machine B.machine)
    {φ : Sen S} (hφ : φ.IsDemonic) (hA : sat A φ) : sat B φ := by
  obtain ⟨s⟩ := h
  cases φ with
  | angelic _ _ _ => exact hφ.elim
  | demonic P p Q => exact s.demonic hA

/-- **The transfer theorem.** `A` is a simulator over the signature `S` (its forms,
syscalls, locations), `B` the reference ISA over `T`, `σ : S → T` says how the simulator's
commands are ISA programs and its locations ISA locations. If `A` is sound for the reduct of
`B` and satisfies the upward-closed angelic sentence `φ`, then `B` satisfies the translated
sentence: *a property of the simulator is a property of the ISA*. -/
theorem transfer {S T : Sig V} (σ : Sig.Hom S T) {A : Mod S} {B : Mod T}
    (hs : Silmaril.Sim.Sound A.machine ((Mod.reduct σ).obj B).machine) {φ : Sen S}
    (hφ : φ.AngelicMono) (h : sat A φ) : sat B (φ.map σ) :=
  (sat_map_iff σ B φ).2 (sat_of_hom (B := (Mod.reduct σ).obj B) ⟨hs⟩ hφ h)

/-- The transfer theorem in the facade's notation. -/
theorem transfer_inst {S T : Sig V} (σ : Sig.Hom S T) {A : (inst V).Mod S}
    {B : (inst V).Mod T} (hs : Silmaril.Sim.Sound (Mod.machine (S := S) A)
      ((Mod.reduct σ).obj B).machine) {φ : (inst V).Sen S} (hφ : Sen.AngelicMono (S := S) φ)
    (h : A ⊨[inst V] φ) : B ⊨[inst V] (inst V).map (S := S) (S' := T) σ φ :=
  transfer σ hs hφ h

/-- The transfer theorem for demonic sentences and complete simulators. -/
theorem transfer_demonic {S T : Sig V} (σ : Sig.Hom S T) {A : Mod S} {B : Mod T}
    (hc : Silmaril.Sim.Complete A.machine ((Mod.reduct σ).obj B).machine) {φ : Sen S}
    (hφ : φ.IsDemonic) (h : sat A φ) : sat B (φ.map σ) :=
  (sat_map_iff σ B φ).2 (sat_of_complete (B := (Mod.reduct σ).obj B) hc hφ h)

/-- **Transfer by an exact simulator**: every angelic sentence (guards and postcondition
arbitrary, e.g. branches on flags the simulator drew from the oracle). -/
theorem transfer_exact {S T : Sig V} (σ : Sig.Hom S T) {A : Mod S} {B : Mod T}
    (hs : Silmaril.Sim.ExactSound A.machine ((Mod.reduct σ).obj B).machine)
    {P : PState S.L V → Prop} {p : S.Program} {Q : PState S.L V → PState S.L V → Prop}
    (h : sat A (.angelic P p Q)) : sat B ((Sen.angelic P p Q).map σ) := by
  obtain ⟨Sm, hx⟩ := hs
  exact (sat_map_iff σ B _).2 (Sm.angelicExact hx h)

/-- Demonic partial correctness and progress give the angelic sentence. -/
theorem sat_angelic_of_demonic {S : Sig V} {A : Mod S} {P : PState S.L V → Prop}
    {p : S.Program} {Q : PState S.L V → PState S.L V → Prop}
    (hd : sat A (.demonic P p Q)) (hp : A.machine.Progress P p) : sat A (.angelic P p Q) :=
  Machine.angelic_of_demonic hd hp

/-! ## The semi-comorphism to certified simulators -/

/-- **Transfer as a semi-comorphism** `inst → certInst`: signatures and sentences unchanged; a
certified simulator is sent to its reference; on upward-closed angelic sentences,
satisfaction is *reflected*: what the simulator satisfies, the reference satisfies. -/
def transferSemi (V : Type) : Silmaril.Inst.SemiComorphism (inst V) (certInst V) where
  sig S := S
  sen _ φ := φ
  mod _ c := Cert.ref c
  cls S φ := Sen.AngelicMono (S := S) φ
  Fwd := False
  Bwd := True
  sat_fwd h := h.elim
  sat_bwd _ S c _ hφ h :=
    sat_of_hom (S := S) (A := Cert.sim (S := S) c) (B := Cert.ref (S := S) c) ⟨Cert.sound c⟩ hφ h

/-! ## Linking (assume-guarantee) and structured specifications -/

/-- **Linking.** If `Γ` entails `φ` over `S` (e.g. `Γ` the contracts of callees left opaque as
commands, `φ` the caller's property), and the model `B` satisfies every `σ`-translated
`ψ ∈ Γ` (each callee meets its contract once its body is substituted by `σ`), then `B`
satisfies the translated `φ`. -/
theorem link {S T : Sig V} (σ : Sig.Hom S T) {Γ : Set (Sen S)} {φ : Sen S}
    (hΓ : (room S).Entails Γ φ) {B : Mod T} (hB : ∀ ψ ∈ Γ, sat B (ψ.map σ)) :
    sat B (φ.map σ) :=
  (sat_map_iff σ B φ).2 (hΓ ((Mod.reduct σ).obj B) fun ψ hψ => (sat_map_iff σ B ψ).1 (hB ψ hψ))

/-- Entailment is preserved by translation (structured specifications: translation). -/
theorem entails_map {S T : Sig V} (σ : Sig.Hom S T) {Γ : Set (Sen S)} {φ : Sen S}
    (hΓ : (room S).Entails Γ φ) : (room T).Entails ((Sen.map σ) '' Γ) (φ.map σ) :=
  fun _ hB => link σ hΓ fun ψ hψ => hB _ ⟨ψ, hψ, rfl⟩

/-- Entailment is monotone (structured specifications: union). -/
theorem entails_mono {S : Sig V} {Γ Δ : Set (Sen S)} {φ : Sen S} (hΓ : (room S).Entails Γ φ)
    (h : Γ ⊆ Δ) : (room S).Entails Δ φ :=
  fun M hM => hΓ M fun ψ hψ => hM ψ (h hψ)

/-! ## Reductions -/

namespace Reduction

/-- A goal that is its own subproblem. -/
def self (g : Prop) : Reduction g := ⟨[g], fun h => h g (List.mem_singleton_self g)⟩

/-- **Composition**: refine each subproblem by a reduction of it. -/
def trans {g : Prop} (r : Reduction g) (rs : List (Σ p : Prop, Reduction p))
    (hcov : ∀ p ∈ r.subgoals, ∃ x ∈ rs, x.1 = p) : Reduction g where
  subgoals := rs.flatMap fun x => x.2.subgoals
  sound h := r.sound fun p hp => by
    obtain ⟨⟨q, rq⟩, hx, rfl⟩ := hcov p hp
    exact rq.sound fun s hs => h s (List.mem_flatMap.2 ⟨⟨q, rq⟩, hx, hs⟩)

/-- Weaken: a reduction of a stronger goal. -/
def mono {g g' : Prop} (r : Reduction g) (h : g → g') : Reduction g' :=
  ⟨r.subgoals, fun hs => h (r.sound hs)⟩

/-- **ISA problem → simulator problem + soundness problem** (the transfer theorem). -/
def transfer {S T : Sig V} (σ : Sig.Hom S T) (A : Mod S) (B : Mod T) (φ : Sen S)
    (hφ : φ.AngelicMono) : Reduction (sat B (φ.map σ)) where
  subgoals := [sat A φ, Silmaril.Sim.Sound A.machine ((Mod.reduct σ).obj B).machine]
  sound h := Silmaril.Sim.Institution.transfer σ
    (h (Silmaril.Sim.Sound A.machine ((Mod.reduct σ).obj B).machine) (by simp)) hφ
    (h (sat A φ) (by simp))

/-- **Linking**: the caller's assume-guarantee entailment plus one problem per callee. -/
def link {S T : Sig V} (σ : Sig.Hom S T) (Γ : List (Sen S)) (φ : Sen S) (B : Mod T) :
    Reduction (sat B (φ.map σ)) where
  subgoals := (room S).Entails {ψ | ψ ∈ Γ} φ :: Γ.map fun ψ => sat B (ψ.map σ)
  sound h := Silmaril.Sim.Institution.link σ (h _ (List.mem_cons_self ..))
    fun ψ hψ => h _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨ψ, hψ, rfl⟩))

/-- **Soundness per simulator method**: soundness of a partial-state simulator is one
problem per command, for a list of commands covering all of them. -/
def perCmd {C L : Type} (s : Silmaril.Sim.PRel C L V) (B : Machine C L V) (cs : List C)
    (hcs : ∀ c, c ∈ cs) : Reduction (s.Sound B) where
  subgoals := cs.map (s.SoundAt B)
  sound h := fun c => h _ (List.mem_map.2 ⟨c, hcs c, rfl⟩)

/-- **Across the lattice**: soundness of `A` for `B` from `A` sound for `A'` and `A'` for `B`
(e.g. `A'` a coarser simulator, or the other state representation: see `equiv`). -/
def chain {C L : Type} (A A' B : Machine C L V) : Reduction (Silmaril.Sim.Sound A B) where
  subgoals := [Silmaril.Sim.Sound A A', Silmaril.Sim.Sound A' B]
  sound h :=
    Silmaril.Sim.Sound.trans (h (Silmaril.Sim.Sound A A') (by simp)) (h (Silmaril.Sim.Sound A' B) (by simp))

/-- **G ≡ M**: soundness of one state representation from the other's and their
equivalence. -/
def equiv {C L : Type} (A A' B : Machine C L V) : Reduction (Silmaril.Sim.Sound A B) where
  subgoals := [Nonempty (Silmaril.Sim.Equiv A A'), Silmaril.Sim.Sound A' B]
  sound h := by
    obtain ⟨E⟩ := h (Nonempty (Silmaril.Sim.Equiv A A')) (by simp)
    exact Silmaril.Sim.Sound.trans ⟨E.toSimulation⟩ (h (Silmaril.Sim.Sound A' B) (by simp))

/-- **Soundness of a Wasm simulator → one partial-correctness problem per export**, plus the
`get` and loading conditions, for a fixed store relation `R` and a list of commands covering
all of them. -/
def wasmMethods {C L : Type} (W : Silmaril.Sim.WasmSim C L V) (B : Machine C L V)
    (R : W.Store → B.St → Prop) (cs : List C) (hcs : ∀ c, c ∈ cs) :
    Reduction (Silmaril.Sim.Sound W.toMachine B) where
  subgoals := (∀ a b, R a b → PState.Le (W.get a) (B.view b)) ::
    (∀ b, ∃ a, R a b ∧ W.get a = B.view b) ::
    cs.map fun c => ∀ b, W.toMachine.HDemonic (fun a => R a b) (.cmd c)
      (fun _ a' => ∃ b', B.step c b b' ∧ R a' b')
  sound h :=
    let O : W.Obligations B :=
      { R := R
        view_le := fun {a b} hab => h _ (List.mem_cons_self ..) a b hab
        load := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        method := fun c => h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map.2 ⟨c, hcs c, rfl⟩))) }
    O.sound

/-- One accessor kind (`$rget`, `$rset`, `$fget`, `$fset`, `$fset6`) agrees in both
representations: forward and backward step matching for every accessor command of that
kind (value-indexed commands, e.g. `rset r v`). -/
def AccessorAgrees {Acc L K : Type} (M G : Machine Acc L V) (R : M.St → G.St → Prop)
    (kind : Acc → K) (k : K) : Prop :=
  ∀ c, kind c = k →
    (∀ a a' b, R a b → M.step c a a' → ∃ b', G.step c b b' ∧ R a' b') ∧
    (∀ a b b', R a b → G.step c b b' → ∃ a', M.step c a a' ∧ R a' b')

/-- **G ≡ M → one problem per accessor kind** (plus view agreement and totality of the
store relation). With `Sound.of_repr`, soundness of the G simulator then gives the M
simulator's. -/
def accessors {Acc L K : Type} (M G : Machine Acc L V) (R : M.St → G.St → Prop)
    (kind : Acc → K) (ks : List K) (hks : ∀ k, k ∈ ks) :
    Reduction (Nonempty (Silmaril.Sim.Equiv M G)) where
  subgoals := (∀ a b, R a b → M.view a = G.view b) :: (∀ b, ∃ a, R a b) ::
    (∀ a, ∃ b, R a b) :: ks.map (AccessorAgrees M G R kind)
  sound h := by
    have hv := h _ (List.mem_cons_self ..)
    have hl := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hs := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hk : ∀ k, AccessorAgrees M G R kind k := fun k => h _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨k, hks k, rfl⟩))))
    exact ⟨{ R := R
             view_eq := fun {a b} hab => hv a b hab
             fwd := fun {c a a' b} hab hst => (hk (kind c) c rfl).1 a a' b hab hst
             bwd := fun {c a b b'} hab hst => (hk (kind c) c rfl).2 a b b' hab hst
             load := hl
             store := hs }⟩

end Reduction

end Silmaril.Sim.Institution

end
