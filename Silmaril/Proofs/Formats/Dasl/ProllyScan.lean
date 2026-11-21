module

public import Silmaril.Formats.Dasl.Prolly.Scan.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyScan

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly Silmaril.Semantics.Prolly
open Silmaril.Semantics (OrderedMap)

variable {Name Key Payload : Type}

private theorem mapM_sound {Item Result Error : Type} {items : List Item} {fetch : Item → Except Error Result}
    {truth : Item → Result} {results : List Result}
    (sound : ∀ item ∈ items, ∀ found, fetch item = .ok found → found = truth item)
    (checked : items.mapM fetch = .ok results) : results = items.map truth := by
  induction items generalizing results with
  | nil => exact (Except.ok.inj checked).symm
  | cons head tail ih =>
    cases first : fetch head with
    | error err => simp [List.mapM_cons, first, Bind.bind, Except.bind] at checked
    | ok item =>
      have correct := sound head (by simp) item first
      cases rest : tail.mapM fetch with
      | error err => simp [List.mapM_cons, first, rest, Bind.bind, Except.bind] at checked
      | ok items =>
        have tailCorrect := ih (fun next hit => sound next (List.mem_cons_of_mem _ hit)) rest
        simpa [List.mapM_cons, first, rest, Bind.bind, Except.bind, Pure.pure, Except.pure, correct, tailCorrect]
          using checked.symm

theorem scan_sound [DecidableEq Key] {read : Name → Except (Fault Name) (Block Name Key Payload)}
    (address : Block Name Key Payload → Name) (width fuel level : Nat) (node : Node Key Payload level)
    (agrees : ∀ block ∈ blockOccurrences address level node,
      ∀ actual, read (address block) = .ok actual → actual = block)
    {expected : Option Nat} {entries : List (Key × Payload)}
    (checked : scan read width fuel expected (address (nodeBlock address level node)) = .ok entries) :
    entries = flatten level node := by
  induction fuel generalizing level expected entries with
  | zero => simp [scan] at checked
  | succ fuel ih =>
    have memRoot : nodeBlock address level node ∈ blockOccurrences address level node := by
      cases level <;> simp [blockOccurrences]
    cases step : read (address (nodeBlock address level node)) with
    | error fault => simp [scan, step, Bind.bind, Except.bind] at checked
    | ok actual =>
      have same := agrees _ memRoot actual step
      subst actual
      simp only [scan, step, Bind.bind, Except.bind] at checked
      cases level with
      | zero =>
        simp only [nodeBlock] at checked
        split at checked
        · exact (Except.ok.inj checked).symm
        · contradiction
      | succ level =>
        simp only [nodeBlock] at checked
        split at checked
        · simp only [List.mapM_map, Nat.add_sub_cancel] at checked
          let getChild := fun (child : Key × Node Key Payload level) => do
            let found ← scan read width fuel (some level) (address (nodeBlock address level child.2))
            finishChild (address (nodeBlock address (level + 1) node)) child.1 found
          change (node.mapM getChild >>= fun groups => pure groups.flatten) = .ok entries at checked
          cases children : node.mapM getChild with
          | error fault => simp [children, Bind.bind, Except.bind] at checked
          | ok groups =>
            have correct : groups = node.map (fun child => flatten level child.2) := by
              apply mapM_sound (checked := children)
              intro child hit found readChild
              unfold getChild at readChild
              cases next : scan read width fuel (some level) (address (nodeBlock address level child.2)) with
              | error fault => simp [next, Bind.bind, Except.bind] at readChild
              | ok values =>
                have valuesCorrect : values = flatten level child.2 := ih level child.2 (fun block observed actual compatible =>
                  agrees block (by
                    apply List.mem_cons_of_mem
                    exact List.mem_flatMap.mpr ⟨child, hit, observed⟩) actual compatible) next
                simp only [next, Bind.bind, Except.bind, finishChild] at readChild
                split at readChild
                · exact (Except.ok.inj readChild).symm.trans valuesCorrect
                · contradiction
            have output : groups.flatten = entries := by simpa [children, Bind.bind, Except.bind, Pure.pure, Except.pure] using checked
            rw [← output, correct, flatten, List.flatMap_def]
        · contradiction

theorem readBlock_sound {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    {address : Block Name Key Payload → Name} {tree : Semantics.Prolly.Tree Key Payload} {store : Store Name}
    (stored : Stored codec address tree store) (bound : store.Binding) {read : Read Name} (sound : Read.Sound read store)
    {block : Block Name Key Payload} (hit : block ∈ blockOccurrences address tree.level tree.root)
    {actual : Block Name Key Payload} (readOk : readBlock codec read (address block) = .ok actual) : actual = block := by
  unfold readBlock at readOk
  cases query : read (address block) with
  | missing | invalidWire => simp [query] at readOk
  | found value =>
    simpa [query, stored.read_block bound hit (sound query)] using readOk.symm

theorem lookup_sound [LinearOrder Key] {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    (policy : Policy Key) {map : OrderedMap Key Payload} {address : Block Name Key Payload → Name} {store : Store Name}
    (stored : Stored codec address (build policy map) store) (bound : store.Binding) {read : Read Name}
    (sound : Read.Sound read store) {fuel : Nat} {key : Key} {result : Option Payload}
    (checked : lookup codec read policy.width fuel ((build policy map).rootName address) key = .ok result) :
    map.lookup? key = result := by
  unfold lookup at checked
  let tree := build policy map
  change (scan (readBlock codec read) policy.width fuel none (tree.rootName address) >>= _) = .ok result at checked
  cases observed : scan (readBlock codec read) policy.width fuel none (tree.rootName address) with
  | error fault => simp [observed, Bind.bind, Except.bind] at checked
  | ok entries =>
    have same := scan_sound address policy.width fuel tree.level tree.root
      (fun _ hit _ found => readBlock_sound stored bound sound hit found) observed
    change entries = (build policy map).entries at same
    rw [build_entries] at same
    simpa [observed, Bind.bind, Except.bind, same] using checked

end Silmaril.Proofs.Formats.Dasl.ProllyScan
