module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Defs

open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp.Leaf

#guard ChunkEncoding.dictionary.admitsCodec {} 0
#guard !(ChunkEncoding.dictionary.admitsCodec {allowSnappy := true} 1)
#guard (Dictionary.convert .modernOnly {} {maxFileBytes := 1} {} (.ofList [0, 1]) 1)
  matches .error (.fileByteLimit 1 2)
