module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Tab.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab.Pair

/-!
# Writers over atom tables: soundness and non-vacuity

For every profile, every atom type `α` and every atom table `T` whose entry for the import
`sexp.<name>` (`name ∈ atomNames`) decodes the bytes `68 69` to the atom `a`, and which names
none of the non-atom imports:

* **n-ary writer**: `tab_atom_sound`, `tab_atom_live`, `tab_atom_lang`: the writer language of
  `atomMod name` is `{a}` for policies without undefined behaviour (and contains `a` for every
  policy);
* **AST writer** at `sexpSig α`: `tab_ast_lang`: the AST writer language of the same module is
  `{SExp.toAST a}`, the leaf with payload `a` (the AST language is the image of the n-ary one,
  `tabAstWriterLang_eq`);
* **n-ary two-element list**: `tab_pair_sound`, `tab_pair_live`, `tab_pair_lang`: when `T`
  decodes `61` to `a` and `62` to `b` (and names neither `sexp` nor `accept`), the writer
  language of `pairAtomMod name` is `{(a b)}` for policies without sentinel and without undefined
  behaviour; `tab_pairAst_lang`: its AST writer language is `{SExp.toAST (a b)}`, a branch with
  two leaves;
* **cons writer**: `tab_cons_sound`, `tab_cons_live`, `tab_cons_lang`: the cons writer language
  of `consAtomMod name` is `{(a)}` = `cons(a, nil)`, for policies without sentinel and without
  undefined behaviour.

The admitted hosts are those of `hiMod` (`hiReply`) and `consMod` (`consReply`): they keep the
code and the number of memories, may rewrite memory, and return the import's result shape. The
upper bounds are the Hoare-logic proofs of `atomMod` (`atom_sat`, generic in the roles) and of
`consAtomMod` (`tabCons_sat`, generic in the table); the lower bounds traced sessions against
counting hosts.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Tab

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle
  Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Wasm.Game.HandleAccept.MemSound.Cons Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms
  Silmaril.Wasm.Game.HandleAccept.MemSound.Pair

variable {α : Type} {T : AtomTable α} {name : String} {dec : List UInt8 → Option α} {a : α}

/-- `atomMod name` writes only the atom `a`. -/
theorem tab_atom_sound (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hacc : T.lookup ("sexp", "accept") = none) {pol : Policy (BitVec 32)}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    tabWriterLang P (ReplyEnvs hiReply) 0 (atomMod name) T {} pol ⊆ {.atom a} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab.tab_atom_sound P hn hT hd hacc ha hw

/-- `atomMod name` writes the atom `a`, for every policy. -/
theorem tab_atom_live (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (pol : Policy (BitVec 32)) :
    .atom a ∈ tabWriterLang P (ReplyEnvs hiReply) 0 (atomMod name) T {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab.tab_atom_live P hn hT hd pol

/-- **The n-ary writer language of `atomMod name` is `{a}`.** -/
theorem tab_atom_lang (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hacc : T.lookup ("sexp", "accept") = none) {pol : Policy (BitVec 32)}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    tabWriterLang P (ReplyEnvs hiReply) 0 (atomMod name) T {} pol = {.atom a} :=
  Set.Subset.antisymm (tab_atom_sound P hn hT hd hacc ha hw)
    (Set.singleton_subset_iff.2 (tab_atom_live P hn hT hd pol))

/-- The AST writer language is the image of the n-ary one under `SExp.toAST`. -/
theorem tabAstWriterLang_eq {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat}
    {m : Module} {ix : TabImports} {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    tabAstWriterLang P Envs memIdx m T ix pol =
      SExp.toAST '' tabWriterLang P Envs memIdx m T ix pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab.tabAstWriterLang_eq ha hw

/-- **The AST writer language of `atomMod name` is the leaf `a`.** -/
theorem tab_ast_lang (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hacc : T.lookup ("sexp", "accept") = none) {pol : Policy (BitVec 32)}
    (ha : pol.onAccept ≠ .ub) (hw : pol.onWrite ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs hiReply) 0 (atomMod name) T {} pol =
      {SExp.toAST (.atom a)} := by
  rw [tabAstWriterLang_eq ha hw, tab_atom_lang P hn hT hd hacc ha hw, Set.image_singleton]

/-- `consAtomMod name` writes only `(a)`. -/
theorem tab_cons_sound (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hnil : T.lookup ("sexp", "nil") = none) (hcons : T.lookup ("sexp", "cons") = none)
    (hacc : T.lookup ("sexp", "accept") = none) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod name) T {} pol ⊆
      {.cons (.atom a) .nil} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab.tabCons_sound P hn hT hd
    ⟨hnil, hcons, hacc⟩ hs hw ha

/-- `consAtomMod name` writes `(a)`, for every policy. -/
theorem tab_cons_live (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hnil : T.lookup ("sexp", "nil") = none) (hcons : T.lookup ("sexp", "cons") = none)
    (hacc : T.lookup ("sexp", "accept") = none) (pol : Policy (BitVec 32)) :
    .cons (.atom a) .nil ∈ tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod name) T {}
      pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab.tabCons_live P hn hT hd
    ⟨hnil, hcons, hacc⟩ pol

/-- **The cons writer language of `consAtomMod name` is `{(a)}`.** -/
theorem tab_cons_lang (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hnil : T.lookup ("sexp", "nil") = none) (hcons : T.lookup ("sexp", "cons") = none)
    (hacc : T.lookup ("sexp", "accept") = none) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod name) T {} pol =
      {.cons (.atom a) .nil} :=
  Set.Subset.antisymm (tab_cons_sound P hn hT hd hnil hcons hacc hs hw ha)
    (Set.singleton_subset_iff.2 (tab_cons_live P hn hT hd hnil hcons hacc pol))

/-- `pairAtomMod name` writes only `(a b)`. -/
theorem tab_pair_sound (P : Profile) {b : α} (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (ha₁ : dec [0x61] = some a)
    (hb₁ : dec [0x62] = some b) (hsexp : T.lookup ("sexp", "sexp") = none)
    (hacc : T.lookup ("sexp", "accept") = none) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod name) T {} pol ⊆
      {SExp.ofList [.atom a, .atom b]} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab.tabPair_sound P
    ⟨hn, hT, ha₁, hb₁, hsexp, hacc⟩ hs hw ha

/-- `pairAtomMod name` writes `(a b)`, for every policy. -/
theorem tab_pair_live (P : Profile) {b : α} (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (ha₁ : dec [0x61] = some a)
    (hb₁ : dec [0x62] = some b) (hsexp : T.lookup ("sexp", "sexp") = none)
    (hacc : T.lookup ("sexp", "accept") = none) (pol : Policy (BitVec 32)) :
    SExp.ofList [.atom a, .atom b] ∈
      tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod name) T {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab.tabPair_live P
    ⟨hn, hT, ha₁, hb₁, hsexp, hacc⟩ pol

/-- **The n-ary writer language of `pairAtomMod name` is `{(a b)}`.** -/
theorem tab_pair_lang (P : Profile) {b : α} (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (ha₁ : dec [0x61] = some a)
    (hb₁ : dec [0x62] = some b) (hsexp : T.lookup ("sexp", "sexp") = none)
    (hacc : T.lookup ("sexp", "accept") = none) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod name) T {} pol =
      {SExp.ofList [.atom a, .atom b]} :=
  Set.Subset.antisymm (tab_pair_sound P hn hT ha₁ hb₁ hsexp hacc hs hw ha)
    (Set.singleton_subset_iff.2 (tab_pair_live P hn hT ha₁ hb₁ hsexp hacc pol))

/-- **The AST writer language of `pairAtomMod name` is the branch with leaves `a` and `b`.** -/
theorem tab_pairAst_lang (P : Profile) {b : α} (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (ha₁ : dec [0x61] = some a)
    (hb₁ : dec [0x62] = some b) (hsexp : T.lookup ("sexp", "sexp") = none)
    (hacc : T.lookup ("sexp", "accept") = none) {pol : Policy (BitVec 32)}
    (hs : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabAstWriterLang P (ReplyEnvs pairReply) 0 (pairAtomMod name) T {} pol =
      {SExp.toAST (SExp.ofList [.atom a, .atom b])} := by
  rw [tabAstWriterLang_eq ha hw, tab_pair_lang P hn hT ha₁ hb₁ hsexp hacc hs hw ha,
    Set.image_singleton]

end Silmaril.Wasm.Game.HandleAccept.MemSound.Tab
