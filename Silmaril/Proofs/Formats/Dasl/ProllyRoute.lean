module

public import Silmaril.Formats.Dasl.Prolly.Route.Defs
public import Silmaril.Formats.Dasl.Prolly.Scan.Thms
public import Silmaril.Semantics.Prolly.Routing.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyRoute

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly Silmaril.Semantics.Prolly

variable {Name Key Payload : Type} [LinearOrder Key]

theorem route_sound {read : Name → Except (Fault Name) (Block Name Key Payload)}
    (address : Block Name Key Payload → Name) (width fuel level : Nat) (node : Node Key Payload level)
    (ordered : (flatten level node).Pairwise fun left right => left.1 < right.1)
    (separators : Node.Separators level node)
    (agrees : ∀ block ∈ blockOccurrences address level node,
      ∀ actual, read (address block) = .ok actual → actual = block)
    {expected : Option Nat} {key : Key} {result : Option Payload}
    (checked : route read width key fuel expected (address (nodeBlock address level node)) = .ok result) :
    (flatten level node).lookup key = result := by
  induction fuel generalizing level expected with
  | zero => simp [route] at checked
  | succ fuel ih =>
    have rootHit : nodeBlock address level node ∈ blockOccurrences address level node := by
      cases level <;> simp [blockOccurrences]
    cases step : read (address (nodeBlock address level node)) with
    | error fault => simp [route, step, Bind.bind, Except.bind] at checked
    | ok actual =>
      have same := agrees _ rootHit actual step
      subst actual
      simp only [route, step, Bind.bind, Except.bind] at checked
      cases level with
      | zero =>
        simp only [nodeBlock] at checked
        split at checked
        · exact Except.ok.inj checked
        · contradiction
      | succ level =>
        have lookupEq := lookup_children key node (flatten level) ordered (fun child hit => (separators.2 child hit).1)
        change (flatten (level + 1) node).lookup key = _ at lookupEq
        rw [lookupEq]
        simp only [nodeBlock] at checked
        split at checked
        · let locate := fun (child : Key × Node Key Payload level) =>
            (child.1, address (nodeBlock address level child.2))
          have mapped : selectChild key (node.map locate) = (selectChild key node).map locate := by
            simp [selectChild, locate, Function.comp_def]
          change (match selectChild key (node.map locate) with
            | none => Except.ok none
            | some child => route read width key fuel (some (level + 1 - 1)) child.2) = .ok result at checked
          rw [mapped] at checked
          cases next : selectChild key node with
          | none =>
            change none = result
            exact Except.ok.inj (by simpa only [next, Option.map_none] using checked)
          | some child =>
            simp only [next, Option.map_some, Nat.add_sub_cancel, locate] at checked
            change (flatten level child.2).lookup key = result
            have hit : child ∈ node := List.mem_of_find?_eq_some (by simpa only [selectChild] using next)
            have sub : List.Sublist (flatten level child.2) (flatten (level + 1) node) :=
              List.sublist_flatten_of_mem (List.mem_map.mpr ⟨child, hit, rfl⟩)
            exact ih level child.2 (ordered.sublist sub) (separators.2 child hit).2
              (fun block observed => agrees block (List.mem_cons_of_mem _ <|
                List.mem_flatMap.mpr ⟨child, hit, observed⟩)) checked
        · contradiction

theorem routedLookup_sound {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    {tree : Semantics.Prolly.Tree Key Payload} (routable : tree.Routable) {address : Block Name Key Payload → Name}
    {store : Store Name} (stored : Stored codec address tree store) (bound : store.Binding)
    {read : Read Name} (sound : Read.Sound read store) {width fuel : Nat} {key : Key} {result : Option Payload}
    (checked : routedLookup codec read width fuel (tree.rootName address) key = .ok result) :
    tree.entries.lookup key = result :=
  route_sound address width fuel tree.level tree.root routable.1 routable.2
    (fun _ hit _ step => readBlock_sound stored bound sound hit step) checked

end Silmaril.Proofs.Formats.Dasl.ProllyRoute
