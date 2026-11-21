module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Pair.Defs

/-!
# Writer decoders over any atom type: atom tables

`Silmaril.Wasm.Game.HandleAccept.Memory` and `Silmaril.Wasm.Game.HandleAccept.MemSound.Cons`
decode writers over the fixed atom type `MemAtom`. This topic decodes the three writer APIs
**over any atom type `α`**, given an atom table.

* `AtomTable α`: a list of atom imports, each with its decoder (`AtomDec α`), one entry per
  import name: `.seg dec` for `name(ptr, len) -> i32` (the bytes `[ptr, ptr + len)` of the memory
  at the call), `.seg2 dec` for `name(p₁, l₁, p₂, l₂) -> i32` (two segments, e.g. the hint and
  the octets of `hinted(hptr, hlen, ptr, len)`); `none` from the decoder or out-of-bounds
  segments: no event. The first entry naming the called import is used (`List.lookup`).
* **n-ary writer** (`sexpW α`): `tabWrite T ix` decodes an atom import of `T` answered with a
  handle `r` as `write (atom a) [] r`, and `sexp(ptr, len)` (a `list<i32>` of child handles in
  memory) as a list node; `accept(h)` at the call. `tabRoles`, `tabTraces`, `tabWriterLang`.
* **AST writer** (`astW (sexpSig α)`): the same imports read as `sexpSig` operations: every
  write `write op args r` is the write `write (SxOp.toAST op) args r` (an atom is a leaf with
  its payload, `sexp` a branch). `astTraces T` maps a set of n-ary writer traces;
  `tabAstWriterLang` is the AST writer language of `astTraces (tabTraces …)`.
* **cons writer** (`consW α`): `tabConsWrite T ix` decodes the atom imports of `T`, `nil()` and
  `cons(a, b)`; `tabConsRoles`, `tabConsTraces`, `tabConsWriterLang`.

## The examples `pairAtomMod name` and `consAtomMod name`

`Silmaril.Wasm.Game.HandleAccept.MemSound.Pair.pairMod` with its atom import renamed to
`sexp.<name>`: it stores `61` at `16` and calls `<name>(16, 1)`, stores `62` at `16` and calls
`<name>(16, 1)`, stores the two handles at `[0, 8)` and accepts `sexp(0, 2)`: the two-element
list of the atoms the table decodes from `61` and `62`. `pairAtomMod "symbol"` is `pairMod`.

`Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.consMod` with its atom import renamed to
`sexp.<name>`: it stores `68 69` at `[0, 2)` and accepts `cons(<name>(0, 2), nil())`, the
one-element list of the atom the table decodes from `68 69`. `consAtomMod "symbol"` is
`consMod`. The n-ary example is `Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms.atomMod name`.

`atomNames`: the atom import names the examples are proved for (`symbol`, `string`, `blob`,
`keyword`).

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Tab

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Wasm.Game.HandleAccept.MemSound.Cons

variable {α : Type}

/-- **The decoder of an atom import**, by its memory arguments. -/
inductive AtomDec (α : Type) where
  /-- `name(ptr, len) -> i32`: the bytes `[ptr, ptr + len)`. -/
  | seg (dec : List UInt8 → Option α)
  /-- `name(p₁, l₁, p₂, l₂) -> i32`: the bytes `[p₁, p₁ + l₁)` and `[p₂, p₂ + l₂)`. -/
  | seg2 (dec : List UInt8 → List UInt8 → Option α)

/-- `name(p₁, l₁, p₂, l₂)`: the two segments of the memory at the call, if in bounds. -/
def segs2 (o : Callout) : Option (List UInt8 × List UInt8) :=
  match o.args with
  | [.num ⟨.int .i32, p₁⟩, .num ⟨.int .i32, l₁⟩, .num ⟨.int .i32, p₂⟩, .num ⟨.int .i32, l₂⟩] =>
      (o.segment p₁.toNat l₁.toNat).bind fun x => (o.segment p₂.toNat l₂.toNat).map (x, ·)
  | _ => none

/-- The atom an atom import's call decodes to. -/
def AtomDec.decode : AtomDec α → Callout → Option α
  | .seg dec, o => o.bytes32.bind dec
  | .seg2 dec, o => (segs2 o).bind fun (x, y) => dec x y

/-- **An atom table**: atom imports with their decoders. -/
abbrev AtomTable (α : Type) := List ((String × String) × AtomDec α)

/-- The non-atom imports of the table writers. -/
structure TabImports where
  sexp : String × String := ("sexp", "sexp")
  nil : String × String := ("sexp", "nil")
  cons : String × String := ("sexp", "cons")
  accept : String × String := ("sexp", "accept")

/-- A call of `accept(h)`. -/
def tabAccept {Op : Type} (ix : TabImports) (o : Callout) : Option (WEv Op (BitVec 32)) :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-! ## The n-ary writer -/

/-- **The write of an answered call**: an atom import of `T`, or `sexp(ptr, len)`. -/
def tabWrite (T : AtomTable α) (ix : TabImports) (o : Callout) (w : HostReply) :
    Option (WEv (SxOp α) (BitVec 32)) := do
  let r ← replyI32 w
  match T.lookup o.imp with
  | some d => return .write (.atom (← d.decode o)) [] r
  | none => if o.imp = ix.sexp then return .write .list (← handles32 o) r else none

/-- The roles of the n-ary table writer. -/
def tabRoles (T : AtomTable α) (ix : TabImports) :
    Roles Unit (WEv (SxOp α) (BitVec 32)) Unit Unit where
  callIn := tabAccept ix
  answerIn := tabWrite T ix

/-- **The writer traces of a module** through the n-ary table writer. -/
def tabTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat) (m : Module)
    (T : AtomTable α) (ix : TabImports) : Set (List (WEv (SxOp α) (BitVec 32))) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (tabRoles T ix)

/-- **The n-ary writer language of a module** through an atom table. -/
def tabWriterLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (T : AtomTable α) (ix : TabImports) (pol : Policy (BitVec 32)) : Set (SExp α) :=
  writerLang (sexpW α) pol (tabTraces P Envs memIdx m T ix)

/-! ## The AST writer at `sexpSig α` -/

/-- **n-ary writer traces read as `sexpSig` writer traces.** -/
def astTraces (T : Set (List (WEv (SxOp α) (BitVec 32)))) :
    Set (List (WEv (Σ t, (sexpSig α).Arg t) (BitVec 32))) :=
  List.map (WEv.mapOp SxOp.toAST) '' T

/-- **The AST writer language of a module** through an atom table. -/
def tabAstWriterLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (T : AtomTable α) (ix : TabImports) (pol : Policy (BitVec 32)) :
    Set (AST (sexpSig α)) :=
  writerLang (astW (sexpSig α)) pol (astTraces (tabTraces P Envs memIdx m T ix))

/-! ## The cons writer -/

/-- **The write of an answered call**: an atom import of `T`, `nil()` or `cons(a, b)`. -/
def tabConsWrite (T : AtomTable α) (ix : TabImports) (o : Callout) (w : HostReply) :
    Option (WEv (ConsOp α) (BitVec 32)) := do
  let r ← replyI32 w
  match T.lookup o.imp with
  | some d => return .write (.atom (← d.decode o)) [] r
  | none =>
    if o.imp = ix.nil then
      if o.args = [] then return .write .nil [] r else none
    else if o.imp = ix.cons then
      let (a, b) ← Callout.args2 Callout.i32? o.args
      return .write .cons [a, b] r
    else none

/-- The roles of the cons table writer. -/
def tabConsRoles (T : AtomTable α) (ix : TabImports) :
    Roles Unit (WEv (ConsOp α) (BitVec 32)) Unit Unit where
  callIn := tabAccept ix
  answerIn := tabConsWrite T ix

/-- **The writer traces of a module** through the cons table writer. -/
def tabConsTraces (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (T : AtomTable α) (ix : TabImports) : Set (List (WEv (ConsOp α) (BitVec 32))) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (tabConsRoles T ix)

/-- **The cons writer language of a module** through an atom table. -/
def tabConsWriterLang (P : Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (T : AtomTable α) (ix : TabImports) (pol : Policy (BitVec 32)) :
    Set (SExp2 α) :=
  writerLang (consW α) pol (tabConsTraces P Envs memIdx m T ix)

/-! ## The examples -/

/-- The atom import names the examples are proved for. -/
def atomNames : List String := ["symbol", "string", "blob", "keyword"]

/-- **`pairMod` with the atom import `sexp.<name>`.** -/
def pairAtomMod (name : String) : Module where
  types := [tySym, tyAcc, tyRun]
  imports := [⟨"sexp", name, .func ⟨0⟩⟩, ⟨"sexp", "sexp", .func ⟨0⟩⟩,
    ⟨"sexp", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32, .i32], Pair.pairBody⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- **`consMod` with the atom import `sexp.<name>`.** -/
def consAtomMod (name : String) : Module where
  types := [tySym, tyAcc, tyRun, tyNil]
  imports := [⟨"sexp", name, .func ⟨0⟩⟩, ⟨"sexp", "nil", .func ⟨3⟩⟩,
    ⟨"sexp", "cons", .func ⟨0⟩⟩, ⟨"sexp", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [], consBody⟩]
  exports := [⟨"run", .func ⟨4⟩⟩]

end Silmaril.Wasm.Game.HandleAccept.MemSound.Tab
