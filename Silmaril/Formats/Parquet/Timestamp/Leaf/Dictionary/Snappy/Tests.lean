module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Defs

open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp.Leaf

#guard ChunkEncoding.snappyDictionary.admitsCodec {} 1
#guard !(ChunkEncoding.snappyDictionary.admitsCodec {allowSnappy := true} 0)
#guard !(ChunkEncoding.dictionary.admitsCodec {allowSnappy := true} 1)
#guard (Dictionary.Snappy.convert .modernOnly {} {maxFileBytes := 1} {} (.ofList [0, 1]) 1)
  matches .error (.fileByteLimit 1 2)
