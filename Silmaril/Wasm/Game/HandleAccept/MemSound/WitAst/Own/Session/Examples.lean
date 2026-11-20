module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own
import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Thms

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Examples

open Silmaril.Formats Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core

def signature : WitSig := ⟨Unit, fun _ => [.option (.own 7)], fun _ => .fixed 0⟩

noncomputable def contract : Contract signature Nat where
  code := 0
  name := ("wit", "node")
  tagOf := fun _ => some ()
  mode := {}
  node before op _ _ _ after :=
    let representation : Option Nat := op.2.1
    after = before + representation.getD 0
  other _ _ _ _ := False

def call (marker : UInt8) : UCall Nat :=
  ⟨0, { mems := [⟨⟨.i32, ⟨0, none⟩⟩, ⟨#[1, 0, 0, 0, 1, 0, 0, 0, marker]⟩⟩] },
    [.i32 0, .i32 0, .i32 0, .i32 0]⟩

def before : State Nat := ⟨RT.single 1 7 77, 0⟩

def afterMove : State Nat := ⟨before.resources.killAll [1], 77⟩

theorem resolved_owner_reaches_writer :
    Answer contract (some 0) before (call 0) ⟨(call 0).store, .values [.i32 3]⟩ afterMove :=
  .returnHandle (op := (⟨(), (some (77 : Nat), ())⟩ : Op signature)) (children := [])
    rfl rfl ⟨rfl, rfl⟩ rfl

theorem retry_traps_with_later_memory_and_consumed_owner :
    Answer contract (some 0) afterMove (call 99) ⟨(call 99).store, .trap⟩ afterMove :=
  .reject (issue := .resource (.dead 1)) rfl rfl

abbrev fixtureSig : WitSig :=
  ⟨BitVec 32, fun tag =>
    if tag = 0 then [.variant [("unit", none), ("hidden", some (.own 7)),
      ("borrowed", some (.option (.borrow 7)))]]
    else if tag = 1 then [.list (.option (.borrow 7))]
    else [.own 7, .char], fun _ => .fixed 0⟩

noncomputable def fixture (mode : NodeMode := {}) : Contract fixtureSig Nat where
  code := 0
  name := ("wit", "node")
  tagOf := some
  mode := mode
  node before _ _ _ _ after := after = before + 1
  other _ _ _ _ := False

def fixtureCall (tag : BitVec 32) (bytes : Array UInt8) (width : AddrType := .i32) : UCall Nat :=
  ⟨0, { mems := [⟨⟨width, ⟨0, none⟩⟩, ⟨bytes⟩⟩] }, [.i32 tag, .i32 0, .i32 0, .i32 0]⟩

theorem inactive_and_empty_unsupported_schemas_trap :
    let inactive := fixtureCall 0 #[0, 0, 0, 0, 0, 0, 0, 0]
    let emptyList := fixtureCall 1 #[0, 0, 0, 0, 0, 0, 0, 0]
    Answer (fixture {}) (some 0) before inactive ⟨inactive.store, .trap⟩ before ∧
    Answer (fixture {}) (some 0) before emptyList ⟨emptyList.store, .trap⟩ before :=
  ⟨.reject (issue := .payload (.storedBorrow 7)) rfl rfl,
   .reject (issue := .payload (.storedBorrow 7)) rfl rfl⟩

theorem bad_mode_and_memory_trap :
    let invalidWidth := fixtureCall 2 #[1, 0, 0, 0, 65, 0, 0, 0] .i64
    Answer (fixture {}) (some 0) before invalidWidth ⟨invalidWidth.store, .trap⟩ before ∧
    Answer (fixture {}) none before invalidWidth ⟨invalidWidth.store, .trap⟩ before ∧
    Answer (fixture { passing := .flat }) (some 0) before invalidWidth ⟨invalidWidth.store, .trap⟩ before :=
  ⟨.reject (issue := .addressWidth .i64) rfl rfl,
   .reject (issue := .missingMemory) rfl rfl,
   .reject (issue := .flatPayload) rfl rfl⟩

def twoOwners : State Nat :=
  ⟨fun handle => if handle = 2 then some ⟨7, 12, true⟩ else before.resources handle, 0⟩

def afterEarlierWrite : State Nat := ⟨twoOwners.resources.killAll [2], 1⟩

theorem malformed_later_field_preserves_prior_effects_and_allows_retry :
    let first := fixtureCall 2 #[2, 0, 0, 0, 66, 0, 0, 0]
    let malformed := fixtureCall 2 #[1, 0, 0, 0, 0, 216, 0, 0]
    let repaired := fixtureCall 2 #[1, 0, 0, 0, 65, 0, 0, 0]
    Answer (fixture {}) (some 0) twoOwners first ⟨first.store, .values [.i32 2]⟩ afterEarlierWrite ∧
    Answer (fixture {}) (some 0) afterEarlierWrite malformed ⟨malformed.store, .trap⟩ afterEarlierWrite ∧
    Answer (fixture {}) (some 0) afterEarlierWrite repaired ⟨repaired.store, .values [.i32 3]⟩
      ⟨afterEarlierWrite.resources.killAll [1], afterEarlierWrite.writer + 1⟩ :=
  ⟨.returnHandle (op := (⟨2, ((12 : Nat), 'B', ())⟩ : Op fixtureSig)) (children := []) rfl rfl ⟨rfl, rfl⟩ rfl,
   .reject (issue := .badPayload) rfl rfl,
   .returnHandle (op := (⟨2, ((77 : Nat), 'A', ())⟩ : Op fixtureSig)) (children := []) rfl rfl ⟨rfl, rfl⟩ rfl⟩

noncomputable def fixtureInstance : ScalarInstance :=
  ⟨[(fixture {}).importType, ⟨[.num (.int .i32)], []⟩], [], [], {}⟩

def fixtureInitial : Config Nat := ⟨{}, { module := { mems := [3] } }, []⟩

theorem links_instance_memory : (fixture {}).link ownMod fixtureInstance fixtureInitial 0 = .ok (some 3) := rfl

theorem links_missing_memory_without_fallback :
    (fixture {}).link ownMod fixtureInstance fixtureInitial 1 = .ok none := rfl

theorem rejects_wrong_core_import_type :
    (fixture {}).link ownMod { fixtureInstance with imports := [⟨[], []⟩] } fixtureInitial 0 =
      .error (.wrongType 0 (fixture {}).importType) := rfl

theorem rejects_duplicate_import_names :
    (fixture {}).link { ownMod with imports := ownMod.imports ++ ownMod.imports }
        fixtureInstance fixtureInitial 0 = .error (.duplicateImport ("wit", "node")) := rfl

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Examples
