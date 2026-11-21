module

meta import Silmaril.Formats.Bao.Defs
meta import Silmaril.Formats.Bao.Opening.Defs
meta import Silmaril.Formats.Iroh.Defs

meta section

namespace Silmaril.Formats.Iroh.Vectors

open Bao (Bytes Slot putLE64 digest?)

private def nibble (digit : Char) : Nat :=
  if digit ≤ '9' then digit.toNat - '0'.toNat else digit.toNat - 'a'.toNat + 10

private def hexChars : List Char → Bytes
  | hi :: lo :: tail => UInt8.ofNat (16 * nibble hi + nibble lo) :: hexChars tail
  | _ => []

private def hex (words : List String) : Bytes := words.flatMap (hexChars ∘ String.toList)
private def zeros (size : Nat) : Bytes := List.replicate size 0

private def baoRootPair : Bytes := hex [
  "a04fc7e7e6831a11965e686a56952b0830aadd1555beabcc79b8db5c93e680d3",
  "c37466bfff693873425adf2590fc7058f0f99b3d33103f87431d6fd1823e58da"]

private def baoLeftPair : Bytes := hex [
  "91715ad631c858232d522cc2ff678052288c8c540fc6ab6c5fa5104cb63e0d39",
  "f0eef3b0033abb623278828fcc75f90c65bde353141ec7c6854eae1c515b93ca"]

private def baoSource : Slot → Option Bytes
  | .pair span => some (if span.count == 3 then baoRootPair else baoLeftPair)
  | .data _ width => some (zeros width)

private def baoOutboard : Bytes := [1, 8, 0, 0, 0, 0, 0, 0] ++ baoRootPair ++ baoLeftPair
private def baoCombined : Bytes := baoOutboard ++ zeros 2049
private def baoInterior : Bytes := baoOutboard ++ zeros 1024
private def baoTail : Bytes := [1, 8, 0, 0, 0, 0, 0, 0] ++ baoRootPair ++ [0]
private def interior : Bao.RangeRequest := ⟨1024, 1⟩

#guard Bao.encode .combined 2049 baoSource == some baoCombined
#guard Bao.encode .outboard 2049 baoSource == some baoOutboard
#guard Bao.encode (.slice interior) 2049 baoSource == some baoInterior
#guard Bao.encode (.slice ⟨0, 2049⟩) 2049 baoSource == some baoCombined
#guard Bao.encode (.slice ⟨1024, 0⟩) 2049 baoSource == some baoInterior
#guard Bao.encode (.slice ⟨9999, 0⟩) 2049 baoSource == some baoTail
#guard Bao.fromCombined .outboard baoCombined == some baoOutboard
#guard Bao.fromCombined (.slice interior) baoCombined == some baoInterior
#guard Bao.fromOutboard .combined baoOutboard (zeros 2049) == some baoCombined
#guard Bao.fromOutboard (.slice interior) baoOutboard (zeros 2049) == some baoInterior
#guard (Bao.fromOutboard .combined baoOutboard (zeros 2048)).isNone
#guard (Bao.decode .combined (baoCombined ++ [0])).isNone
#guard (Bao.decode .combined (baoCombined.take 2184)).isNone
#guard (Bao.decode .outboard (baoOutboard.take 135)).isNone
#guard (Bao.decode .combined (zeros 7)).isNone
#guard (Bao.decode .combined (List.replicate 8 255)).isNone
#guard (Bao.encode .combined Bao.u64Limit baoSource).isNone
#guard (Bao.encode (.slice ⟨Bao.u64Limit, 1⟩) 10 baoSource).isNone
#guard Bao.encode (.slice ⟨Bao.u64Limit - 1, Bao.u64Limit - 1⟩) 2049 baoSource == some baoTail
#guard Bao.decode .combined (putLE64 0) == some (0, [[]])
#guard Bao.decode .outboard (putLE64 0) == some (0, [])
#guard Bao.decode .combined (putLE64 1 ++ [23]) == some (1, [[23]])

private def baoRoot : Bytes := hex ["b982335435308f3f5f5f51f5d45ecae6194641975e7b0bcaa1facd48ebabb28e"]

/-- Only the recorded oracle entries are filled. This is not a BLAKE3 implementation. -/
private def fixtureHash : Bao.HashOps where
  parent root left right :=
    let input := left.toArray.toList ++ right.toArray.toList
    if root && input == baoRootPair then (digest? baoRoot).getD default
    else if !root && input == baoLeftPair then (digest? (baoRootPair.take 32)).getD default
    else default
  subtree root index input :=
    if root then default else
      match index with
      | 0 => if input == zeros 1024 then (digest? (baoLeftPair.take 32)).getD default else default
      | 1 => if input == zeros 1024 then (digest? (baoLeftPair.drop 32)).getD default else default
      | 2 => if input == [0] then (digest? (baoRootPair.drop 32)).getD default else default
      | _ => default

private def verifyInterior (claim : Nat) : Option (Option Nat) :=
  (Bao.verifyFrame fixtureHash claim (Bao.slicePlan claim interior) ((digest? baoRoot).getD default)
    (baoInterior.drop 8)).map Prod.snd

#guard verifyInterior 2048 == none
#guard verifyInterior 2049 == some none
#guard verifyInterior 2050 == some none
#guard verifyInterior 3073 == some none
#guard (Bao.verifyFrame fixtureHash 2049 (Bao.fullPlan 2049 1) ((digest? baoRoot).getD default)
  (baoCombined.drop 8)).map Prod.snd == some (some 2049)
#guard (Bao.verifyFrame fixtureHash 2049 (Bao.fullPlan 2049 1) ((digest? baoRoot).getD default)
  ((baoCombined.drop 8).take 2176)).isNone

private def streamingPrefix : Option (List UInt8 × Bool × Bool) := do
  let state := Bao.start (Bao.fullPlan 2049 1) ((digest? baoRoot).getD default)
  let (afterRoot, _, more) ← Bao.readStep fixtureHash 2049 state (baoCombined.drop 8)
  let (afterLeft, _, more) ← Bao.readStep fixtureHash 2049 afterRoot more
  let (afterData, data, _) ← Bao.readStep fixtureHash 2049 afterLeft more
  return (Bao.requestedBytes ⟨5, 1⟩ data, afterData.rightEdge, Bao.finished afterData [] true)

#guard streamingPrefix == some ([0], false, false)

private def rootDigest : Bao.Digest := (digest? baoRoot).getD default

#guard (Bao.lowerPrefix (Bao.fullPlan 2049 1) rootDigest []).isNone
#guard (Bao.lowerPrefix (Bao.fullPlan 2049 1) rootDigest
  [baoRootPair, baoLeftPair, zeros 1024]).map (Bao.Frontier.edgeAt 2049) == some false
#guard (Bao.lowerPrefix (Bao.slicePlan 2049 ⟨2048, 1⟩) rootDigest
  [baoRootPair, [0]]).map (Bao.Frontier.edgeAt 2049) == some true
#guard (Bao.lowerPrefix (Bao.slicePlan 2049 ⟨2048, 1⟩) rootDigest
  [baoRootPair, [0], []]).isNone
#guard (Bao.lowerPrefix (Bao.fullPlan 0 1) rootDigest [[]]).map (Bao.Frontier.edgeAt 0) == some true

private def staged : Bao.StagedRange (fun _ _ _ _ => True) rootDigest 2049 :=
  ⟨1024, [0], trivial⟩

#guard Bao.releaseRanges (Trusted := fun _ _ => True) (EOF := fun _ _ => False)
  none [staged] == none
#guard Bao.releaseRanges (Trusted := fun _ _ => True) (EOF := fun _ _ => False)
  (some ⟨.trusted trivial⟩) [staged] == some [(1024, [0])]

private def irohRootPair : Bytes := hex [
  "ee30137d2224ac86f79680abb2e7a033b746753664993356b8f05cbe11e99772",
  "e03d344a44e5d75dd69eed75e4284eb4ca4a7a4dcd061c4ca79850c5359e9115"]

private def irohLeftPair : Bytes := hex [
  "97d5904f808b1050b96e65fd7d254feafc434931da41d1215415bb2adc890475",
  "1bbec3b0da531ff4151be9809d18c7a4da37e75ca806a08c9635c5d53057043e"]

private def irohInnerPairs : List Bytes := [
  hex ["8f1dc9cbc6a28285f11e986c79ba3a41b85c219111c034740eda6d95b8302850",
       "43273bfcda2f6c0de8ac2bc08c7f65d8e5f89e8ae716143c36178171bd763831"],
  hex ["3694b08b169d1c322ef5e9d4dee1a3d2536233851fffd7977a8c1b5a0d51628f",
       "64b687935a6f38f68a040817d157412bf934ec48790e6b34d85825252979e5be"],
  hex ["a04fc7e7e6831a11965e686a56952b0830aadd1555beabcc79b8db5c93e680d3",
       "580f4b19f0952c41fccedc302ae73758cfa2ab094deead97b2c25b6f6829ecd1"],
  baoLeftPair]

private def irohRoot : Hash := ⟨(digest? (hex [
  "e50c14417d5f1eb8ff357630021170d5c73e5abc353f5c66eca12ebbd1f5718a"])).getD default⟩

private def irohHead : Bytes := [1, 128, 0, 0, 0, 0, 0, 0]
private def irohPre : Bytes := irohHead ++ irohRootPair ++ irohLeftPair
private def irohPost : Bytes := irohLeftPair ++ irohRootPair ++ irohHead
private def irohFull : Bytes := irohPre ++ zeros 32769
private def irohPartial : Bytes := irohPre ++ irohInnerPairs.flatten ++ zeros 1024
private def irohPast : Bytes := irohHead ++ irohRootPair ++ [0]

#guard [irohRootPair.length, irohLeftPair.length] == [64, 64]
#guard irohInnerPairs.map List.length == [64, 64, 64, 64]
#guard [0, 1, 1024, 1025, 16384, 16385, 32769].map outboardSize == [0, 0, 0, 0, 0, 64, 128]
#guard ((readPortable irohRoot .pre irohPre >>= reorder .post).map writePortable) == some irohPost
#guard ((readPortable irohRoot .post irohPost >>= reorder .pre).map writePortable) == some irohPre
#guard ((readMemory irohRoot 32769 .pre (irohPre.drop 8)).map writePortable) == some irohPre
#guard (readPortable irohRoot .post (irohPost.take 135)).isNone
#guard (readResponse [0] irohFull) == some (32769, [irohRootPair, irohLeftPair, zeros 16384,
  zeros 16384, [0]], [])
#guard (readResponse [1, 2] irohPartial) ==
  some (32769, [irohRootPair, irohLeftPair] ++ irohInnerPairs ++ [zeros 1024], [])
#guard (readResponse [99, 100] (irohPast ++ [20, 21])) == some (32769, [irohRootPair, [0]], [20, 21])
#guard (readResponse [0, 32] (irohFull.take 32904)) ==
  some (32769, [irohRootPair, irohLeftPair, zeros 16384, zeros 16384], [])
#guard (readResponse [16, 32, 99, 100] (irohPre ++ zeros 16385)) ==
  some (32769, [irohRootPair, irohLeftPair, zeros 16384, [0]], [])
#guard (readResponse [1, 2] (irohPartial.take 1415)).isNone
#guard (readResponse [] irohHead) == some (32769, [], [])
#guard (readResponse [99] (putLE64 0)) == some (0, [[]], [])
#guard (readResponse endProbe irohPast) == some (32769, [irohRootPair, [0]], [])
#guard byteRange 1023 1025 == some [0, 2]
#guard byteRange 1024 1024 == some []
#guard byteRange Bao.u64Limit Bao.u64Limit == none

private def irohEdge (query : Boundaries) (bytes : Bytes) : Option Bool := do
  let (claim, fields, _) ← readResponse query bytes
  let frontier ← Bao.lowerPrefix (responsePlan claim query) irohRoot.bytes fields
  return frontier.edgeAt claim

#guard irohEdge [1, 2] irohPartial == some false
#guard irohEdge endProbe irohPast == some true
#guard irohEdge [0] irohFull == some true

private def postcardHash : Hash := ⟨(digest? (List.replicate 32 218)).getD default⟩
private def requestPrefix : Bytes := 0 :: List.replicate 32 218
private def rawGet : Bytes := requestPrefix ++ [2, 0, 1, 0, 1, 0]
private def allGet : Bytes := requestPrefix ++ [1, 0, 1, 0]

#guard writeGet (Get.blob postcardHash) == rawGet
#guard writeGet (Get.all postcardHash) == allGet
#guard (readGet rawGet).map writeGet == some rawGet
#guard (readGet allGet).map writeGet == some allGet
#guard (readGet (rawGet ++ [0])).isNone
#guard (readGet (requestPrefix ++ [1, 0, 2, 0, 0])).isNone
#guard (readGet (requestPrefix ++ [2, 0, 1, 0, 0, 0])).isNone
#guard (readVar [128, 0]).isNone
#guard readVar (writeVar (Bao.u64Limit - 1)) == some (Bao.u64Limit - 1, [])
#guard (readVar (List.replicate 9 255 ++ [2])).isNone
#guard ((transfers (Get.blob postcardHash) [irohRoot]).map Transfer.offset) == [0]
#guard ((transfers (Get.all postcardHash) [irohRoot]).map Transfer.offset) == [0, 1]
#guard ((readHashSeq (List.replicate 64 218)).map List.length) == some 2
#guard (readHashSeq (zeros 63)).isNone

private def collectionHeader : Bytes := "CollectionV0.".toUTF8.data.toList
#guard readCollectionNames (collectionHeader ++ [2, 1, 97, 2, 195, 169]) == some ["a", "é"]
#guard readCollectionNames (collectionHeader ++ [1, 1, 255]) == none
#guard collectionItems [irohRoot, postcardHash] (collectionHeader ++ [1, 1, 97]) ==
  some [("a", postcardHash)]
#guard (collectionItems [irohRoot, postcardHash] (collectionHeader ++ [0])).isNone

end Silmaril.Formats.Iroh.Vectors

end
