module

public import Silmaril.Sim.Core.Thms
public import Silmaril.Logic.Inst.Defs

/-!
# The institution of simulators (header)

Built through the facade `Silmaril.Inst` (`Silmaril/Logic/Inst/Defs.lean`); the guide is
`docs/institutions-guide.md` §1 ("build the room functor directly").

* **Signatures** `Sig V`: instruction forms `F`, syscalls `Y`, locations `L` (values `V` fixed
  per institution). Commands are `F ⊕ Y`.
* **Signature morphisms** `Sig.Hom`: *derived* morphisms. Locations map `L → L'`; each command
  maps to a *program* over the target (`Prog`), with upward-closed guards. Inclusions of forms
  and locations, renamings, compiling an instruction to simulator calls (P-calls), and
  substituting a callee's body for a `call` command (linking) are all signature morphisms.
  Composition is substitution (`Prog.subst`).
* **Sentences** `Sen Σ`: properties of programs over `Σ` on views: `angelic P p Q` (some run
  of `p` from every `P`-view ends `Q`-related: the shape of `FnContract.Spec.Total`) and
  `demonic P p Q` (every run does: partial correctness, the shape of `FnSpec`/`FSpecValid`).
  `Sen.map` translates along a morphism (substitute, restrict views).
* **Models** `Mod Σ`: machines over the commands and locations of `Σ` (simulators and reference
  ISAs alike). A model morphism `A ⟶ B` is a proof that `A` is a **sound** simulator of `B`
  (`Silmaril.Sim.Sound`): the model category is the soundness preorder. The reduct along `σ` is
  `Machine.reduct` (run the substituted program, restrict the view).
* `sat` and the **satisfaction condition** (`sat_map_iff`, proved here); `room`, `corridor`,
  `functor`, and `inst : Silmaril.Inst.Institution₁₁`.
* `AngelicMono φ`: the sentences that sound simulators transfer (angelic, guards and
  postcondition upward closed). `Demonic φ`: the sentences complete simulators transfer.
* `Cert Σ`: **certified simulators**, a simulator with a reference and a soundness proof;
  `certInst` (satisfaction: the simulator's) and the semi-comorphism `transferSemi :
  SemiComorphism inst certInst` whose backward direction *is* the transfer theorem: what the
  simulator satisfies, the reference satisfies (`Silmaril/Sim/Institution/Thms.lean`).
* `Reduction goal`: a list of independent subproblems whose solutions give `goal`, with
  composition (`Reduction.refine`); the decompositions of `Thms` are `Reduction`s.
-/

@[expose] public section

namespace Silmaril.Sim.Institution

open CategoryTheory
open Silmaril.Sim (PState Prog Machine)

variable {V : Type}

/-! ## Signatures -/

/-- A signature: instruction forms, syscalls, locations. -/
structure Sig (V : Type) where
  /-- Instruction forms (with operands): the decoded instructions, or simulator methods. -/
  F : Type
  /-- System calls (environment interactions). -/
  Y : Type
  /-- Locations (registers, flags, memory cells, …). -/
  L : Type

namespace Sig

/-- Commands: instructions and syscalls. -/
abbrev Cmd (S : Sig V) : Type := S.F ⊕ S.Y

/-- Programs over a signature. -/
abbrev Program (S : Sig V) : Type := Prog S.Cmd S.L V

/-- A derived signature morphism: locations to locations, commands to programs. -/
structure Hom (S T : Sig V) where
  /-- The map of locations. -/
  loc : S.L → T.L
  /-- The program implementing each command. -/
  cmd : S.Cmd → T.Program
  /-- Guards of the implementing programs are upward closed. -/
  mono : ∀ c, (cmd c).MonoTests

theorem Hom.ext' {S T : Sig V} {σ τ : Hom S T} (h₁ : σ.loc = τ.loc) (h₂ : σ.cmd = τ.cmd) :
    σ = τ := by
  cases σ; cases τ; cases h₁; cases h₂; rfl

/-- The identity morphism. -/
def Hom.id (S : Sig V) : Hom S S := ⟨_root_.id, Prog.cmd, fun _ => trivial⟩

/-- Composition: substitution. -/
def Hom.comp {S T U : Sig V} (σ : Hom S T) (τ : Hom T U) : Hom S U where
  loc l := τ.loc (σ.loc l)
  cmd c := (σ.cmd c).subst τ.loc τ.cmd
  mono c := Prog.MonoTests.subst τ.mono (σ.mono c)

/-- An inclusion of forms, syscalls and locations (a plain renaming). -/
def Hom.ofMaps {S T : Sig V} (f : S.F → T.F) (y : S.Y → T.Y) (l : S.L → T.L) : Hom S T where
  loc := l
  cmd c := .cmd (Sum.elim (fun x => .inl (f x)) (fun x => .inr (y x)) c)
  mono _ := trivial

instance category : Category (Sig V) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext' rfl rfl
  comp_id σ := Hom.ext' rfl (funext fun c => Prog.subst_id (σ.cmd c))
  assoc σ _ _ := Hom.ext' rfl (funext fun c => Prog.subst_subst _ _ _ _ (σ.cmd c))

end Sig

/-! ## Sentences -/

/-- Sentences: angelic and demonic properties of programs, on views. -/
inductive Sen (S : Sig V) : Type where
  /-- From every `P`-view some run of `p` ends `Q`-related (angelic total correctness). -/
  | angelic (P : PState S.L V → Prop) (p : S.Program) (Q : PState S.L V → PState S.L V → Prop)
  /-- Every run of `p` from a `P`-view ends `Q`-related (demonic partial correctness). -/
  | demonic (P : PState S.L V → Prop) (p : S.Program) (Q : PState S.L V → PState S.L V → Prop)

/-- Sentence translation along a signature morphism. -/
def Sen.map {S T : Sig V} (σ : Sig.Hom S T) : Sen S → Sen T
  | .angelic P p Q => .angelic (fun q => P (PState.comap σ.loc q)) (p.subst σ.loc σ.cmd)
      (fun q q' => Q (PState.comap σ.loc q) (PState.comap σ.loc q'))
  | .demonic P p Q => .demonic (fun q => P (PState.comap σ.loc q)) (p.subst σ.loc σ.cmd)
      (fun q q' => Q (PState.comap σ.loc q) (PState.comap σ.loc q'))

/-- Angelic sentences with upward-closed guards and postcondition: transferred by sound
simulators. -/
def Sen.AngelicMono {S : Sig V} : Sen S → Prop
  | .angelic _ p Q => p.MonoTests ∧ ∀ x, PState.Mono (Q x)
  | .demonic _ _ _ => False

/-- Demonic sentences: transferred by complete simulators. -/
def Sen.IsDemonic {S : Sig V} : Sen S → Prop
  | .angelic _ _ _ => False
  | .demonic _ _ _ => True

/-! ## Models -/

/-- Models over `S`: machines (simulators, reference ISAs). The category is the soundness
preorder: `A ⟶ B` when `A` is a sound simulator of `B`. -/
def Mod (S : Sig V) : Type 1 := Machine S.Cmd S.L V

/-- The underlying machine. -/
abbrev Mod.machine {S : Sig V} (M : Mod S) : Machine S.Cmd S.L V := M

/-- A machine as a model. -/
abbrev Mod.of {S : Sig V} (M : Machine S.Cmd S.L V) : Mod S := M

instance Mod.category (S : Sig V) : Category.{0} (Mod S) where
  Hom A B := PLift (Silmaril.Sim.Sound A.machine B.machine)
  id A := ⟨Silmaril.Sim.Sound.refl A.machine⟩
  comp f g := ⟨f.down.trans g.down⟩

theorem Mod.hom_eq {S : Sig V} {A B : Mod S} (f g : A ⟶ B) : f = g := by
  cases f; cases g; rfl

/-- The reduct along a signature morphism, as a functor. -/
def Mod.reduct {S T : Sig V} (σ : Sig.Hom S T) : Mod T ⥤ Mod S where
  obj M := Mod.of (M.machine.reduct σ.loc σ.cmd)
  map f := ⟨let ⟨s⟩ := f.down; ⟨s.reduct σ.loc σ.cmd σ.mono⟩⟩
  map_id _ := Mod.hom_eq _ _
  map_comp _ _ := Mod.hom_eq _ _

/-! ## Satisfaction and the institution -/

/-- Satisfaction. -/
def sat {S : Sig V} (M : Mod S) : Sen S → Prop
  | .angelic P p Q => M.machine.Angelic P p Q
  | .demonic P p Q => M.machine.Demonic P p Q

/-- **The satisfaction condition.** -/
theorem sat_map_iff {S T : Sig V} (σ : Sig.Hom S T) (M : Mod T) (φ : Sen S) :
    sat M (φ.map σ) ↔ sat ((Mod.reduct σ).obj M) φ := by
  cases φ with
  | angelic P p Q =>
    simp only [sat, Sen.map, Machine.Angelic, Machine.HAngelic, Mod.reduct, Mod.of,
      Mod.machine]
    exact forall_congr' fun a => imp_congr_right fun _ => exists_congr fun b =>
      and_congr_left fun _ => (Machine.sem_reduct σ.loc σ.cmd M p a b).symm
  | demonic P p Q =>
    simp only [sat, Sen.map, Machine.Demonic, Machine.HDemonic, Mod.reduct, Mod.of,
      Mod.machine]
    exact forall_congr' fun a => forall_congr' fun b => imp_congr_right fun _ =>
      imp_congr_left (Machine.sem_reduct σ.loc σ.cmd M p a b).symm

/-- The room of a signature. -/
def room (S : Sig V) : Silmaril.Logic.Institution.Room.{0, 0, 1} :=
  ⟨Sen S, Cat.of (Mod S), fun M φ => sat M φ⟩

/-- The corridor of a signature morphism. -/
def corridor {S T : Sig V} (σ : Sig.Hom S T) : room S ⟶ room T :=
  ⟨Sen.map σ, Mod.reduct σ, fun M φ => sat_map_iff σ M φ⟩

theorem Sen.map_id {S : Sig V} (φ : Sen S) : φ.map (Sig.Hom.id S) = φ := by
  cases φ <;> simp only [Sen.map, Sig.Hom.id] <;> rw [Prog.subst_id] <;> rfl

theorem Sen.map_comp {S T U : Sig V} (σ : Sig.Hom S T) (τ : Sig.Hom T U) (φ : Sen S) :
    φ.map (σ.comp τ) = (φ.map σ).map τ := by
  cases φ <;> simp only [Sen.map, Sig.Hom.comp] <;> rw [Prog.subst_subst] <;> rfl

theorem Mod.reduct_id (S : Sig V) : Mod.reduct (Sig.Hom.id S) = 𝟭 (Mod S) :=
  Functor.ext (fun _ => rfl) (fun _ _ _ => Mod.hom_eq _ _)

theorem Mod.reduct_comp {S T U : Sig V} (σ : Sig.Hom S T) (τ : Sig.Hom T U) :
    Mod.reduct (σ.comp τ) = Mod.reduct τ ⋙ Mod.reduct σ :=
  Functor.ext (fun M => (Machine.reduct_reduct σ.loc σ.cmd τ.loc τ.cmd M.machine).symm)
    (fun _ _ _ => Mod.hom_eq _ _)

/-- The institution as a functor into rooms. -/
def functor : Sig V ⥤ Silmaril.Logic.Institution.Room.{0, 0, 1} where
  obj := room
  map σ := corridor σ
  map_id S := Silmaril.Logic.Institution.Room.hom_ext (funext Sen.map_id) (Mod.reduct_id S)
  map_comp σ τ := Silmaril.Logic.Institution.Room.hom_ext (funext (Sen.map_comp σ τ))
    (Mod.reduct_comp σ τ)

/-- **The institution of simulators** over values `V`. -/
def inst (V : Type) : Silmaril.Inst.Institution₁₁ := ⟨Sig V, functor⟩

/-! ## Certified simulators -/

/-- A **certified simulator** over `S`: a simulator, a reference, and a soundness proof. -/
structure Cert (S : Sig V) : Type 1 where
  /-- The simulator (e.g. a Wasm module ⊗ program, as a machine). -/
  sim : Mod S
  /-- The reference (the ISA, reduced to the simulator's signature). -/
  ref : Mod S
  /-- The simulator is sound. -/
  sound : Silmaril.Sim.Sound sim.machine ref.machine

instance Cert.category (S : Sig V) : Category.{0} (Cert S) where
  Hom c d := PLift (Silmaril.Sim.Sound c.sim.machine d.sim.machine)
  id c := ⟨Silmaril.Sim.Sound.refl c.sim.machine⟩
  comp f g := ⟨f.down.trans g.down⟩

theorem Cert.hom_eq {S : Sig V} {c d : Cert S} (f g : c ⟶ d) : f = g := by
  cases f; cases g; rfl

theorem Cert.ext' {S : Sig V} {c d : Cert S} (h₁ : c.sim = d.sim) (h₂ : c.ref = d.ref) :
    c = d := by
  cases c; cases d; cases h₁; cases h₂; rfl

/-- The reduct of a certified simulator. -/
def Cert.reduct {S T : Sig V} (σ : Sig.Hom S T) : Cert T ⥤ Cert S where
  obj c := ⟨(Mod.reduct σ).obj c.sim, (Mod.reduct σ).obj c.ref, ((Mod.reduct σ).map
    (⟨c.sound⟩ : c.sim ⟶ c.ref)).down⟩
  map {c d} f := ⟨((Mod.reduct σ).map (⟨f.down⟩ : c.sim ⟶ d.sim)).down⟩
  map_id _ := Cert.hom_eq _ _
  map_comp _ _ := Cert.hom_eq _ _

/-- The room of certified simulators: satisfaction is the simulator's. -/
def certRoom (S : Sig V) : Silmaril.Logic.Institution.Room.{0, 0, 1} :=
  ⟨Sen S, Cat.of (Cert S), fun c φ => sat c.sim φ⟩

/-- The corridor of certified simulators. -/
def certCorridor {S T : Sig V} (σ : Sig.Hom S T) : certRoom S ⟶ certRoom T :=
  ⟨Sen.map σ, Cert.reduct σ, fun c φ =>
    show sat c.sim _ ↔ sat ((Cert.reduct σ).obj c).sim φ from sat_map_iff σ c.sim φ⟩

theorem Cert.reduct_id (S : Sig V) : Cert.reduct (Sig.Hom.id S) = 𝟭 (Cert S) :=
  Functor.ext (fun _ => rfl) (fun _ _ _ => Cert.hom_eq _ _)

theorem Cert.reduct_comp {S T U : Sig V} (σ : Sig.Hom S T) (τ : Sig.Hom T U) :
    Cert.reduct (σ.comp τ) = Cert.reduct τ ⋙ Cert.reduct σ := by
  refine Functor.ext (fun c => ?_) (fun _ _ _ => Cert.hom_eq _ _)
  have h₁ := Machine.reduct_reduct σ.loc σ.cmd τ.loc τ.cmd c.sim.machine
  have h₂ := Machine.reduct_reduct σ.loc σ.cmd τ.loc τ.cmd c.ref.machine
  exact Cert.ext' h₁.symm h₂.symm

/-- The institution of certified simulators. -/
def certInst (V : Type) : Silmaril.Inst.Institution₁₁ :=
  ⟨Sig V, {
    obj := certRoom
    map := fun σ => certCorridor σ
    map_id := fun S => Silmaril.Logic.Institution.Room.hom_ext (funext Sen.map_id)
      (Cert.reduct_id S)
    map_comp := fun σ τ => Silmaril.Logic.Institution.Room.hom_ext
      (funext (Sen.map_comp σ τ)) (Cert.reduct_comp σ τ) }⟩

/-! ## Reductions -/

/-- A **reduction** of `goal` to independent subproblems: solving all of them solves `goal`.
The pieces are propositions (Wasm-level problems, soundness of one simulator method, a
G ≡ M equivalence, a callee contract, …). -/
structure Reduction (goal : Prop) where
  /-- The subproblems. -/
  subgoals : List Prop
  /-- The composition theorem. -/
  sound : (∀ p ∈ subgoals, p) → goal

end Silmaril.Sim.Institution

end
