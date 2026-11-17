import EthCLSpecs.Tests.ChainReplay

/-!
# `EthCLSpecs.Tests.ChainData`: decode a chain the upstream pyspec dumped

The reproduction scripts under `scripts/` build chains on the upstream pyspec and write them
to a data file: the genesis state and each signed block, as SSZ in hex, one `name hex` line
each. A pins module reads its file with `include_str` and replays the chain through
`ChainReplay`. This module holds the decoding both steps share: hex to bytes, lines to named
objects, objects to states and blocks, and blocks to replay steps.

No theorem depends on where a data file came from. The theorems of a pins module are about
the decoded values.
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.ChainData

open EthCLLib.Spec
open SizzLean
open EthCLSpecs
open EthCLSpecs.Tests.ChainReplay
open scoped EthCLSpecs.Gloas.Downgrade

/-- The value of one lowercase hex digit. -/
def hexDigit (c : Char) : UInt8 :=
  if c.isDigit then (c.toNat - '0'.toNat).toUInt8 else (c.toNat - 'a'.toNat + 10).toUInt8

/-- The bytes a hex string spells, two digits per byte. -/
def ofHex (s : String) : ByteArray :=
  go s.toList ByteArray.empty
where
  go : List Char → ByteArray → ByteArray
    | a :: b :: rest, acc => go rest (acc.push (hexDigit a * 16 + hexDigit b))
    | _, acc => acc

/-- The objects of a data file, in order: one `name hex` line each. -/
def parseDump (text : String) : List (String × ByteArray) :=
  (text.splitOn "\n").filterMap fun line =>
    match line.splitOn " " with
    | [name, hex] => some (name, ofHex hex)
    | _ => none

/-- The objects of a dump with the given name, in file order. -/
def objects (dump : List (String × ByteArray)) (name : String) : List ByteArray :=
  (dump.filter (·.1 == name)).map (·.2)

section

variable [Gloas.Preset] [HasherTag]

/-- The genesis state of a dump: the one object named `genesis`. A decode failure gives the
default state, which a replay then rejects at the first block. -/
def genesisOf (dump : List (String × ByteArray)) : Fulu.BeaconState :=
  match objects dump "genesis" with
  | [bytes] => (SSZ.deserialize (T := Fulu.BeaconState) bytes).toOption.getD default
  | _ => default

/-- The signed Fulu blocks of a dump with the given name. -/
def fuluBlocks (dump : List (String × ByteArray)) (name : String) :
    List Fulu.SignedBeaconBlock :=
  (objects dump name).filterMap fun bytes =>
    (SSZ.deserialize (T := Fulu.SignedBeaconBlock) bytes).toOption

/-- The signed Gloas blocks of a dump with the given name. -/
def gloasBlocks (dump : List (String × ByteArray)) (name : String) :
    List Gloas.SignedBeaconBlock :=
  (objects dump name).filterMap fun bytes =>
    (SSZ.deserialize (T := Gloas.SignedBeaconBlock) bytes).toOption

/-- `state_transition` for each block: advance to the block's slot, then apply the block. -/
def fuluSteps (blocks : List Fulu.SignedBeaconBlock) : List FuluStep :=
  blocks.flatMap fun sb => [.slots sb.message.slot, .block sb]

/-- `state_transition` for each Gloas block, as `fuluSteps`. -/
def gloasSteps (blocks : List Gloas.SignedBeaconBlock) : List GloasStep :=
  blocks.flatMap fun sb => [.slots sb.message.slot, .block sb]

end

end EthCLSpecs.Tests.ChainData
