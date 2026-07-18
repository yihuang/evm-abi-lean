import EvmAbi.Codec
import EvmAbi.Keccak

namespace EvmAbi

open Ty

/-!
# EvmAbi.Calldata

Call data for a contract call `sig(args)`: the four-byte selector of the
canonical signature followed by the tuple encoding of the arguments.

The selector stays abstract (`EvmAbi.Keccak.keccak256` is opaque); the
argument layer is exactly the node-8 codec, so the calldata roundtrip is a
one-line corollary of the unified `roundtrip`.
-/

/-- Calldata for a call `sig(vs)`: selector ++ tuple encoding of the
arguments. -/
noncomputable def encodeCall (sig : String) (ts : List Ty) (vs : TupleVal ts) : List UInt8 :=
  selector sig ++ encode (.tuple ts) vs

/-- Decode the arguments of calldata (selector stripped) as a tuple. -/
def decodeCall (ts : List Ty) (data : List UInt8) : Option (TupleVal ts) :=
  decode (.tuple ts) (data.drop 4)

/-- **Calldata roundtrip**: decoding a call's arguments returns them,
provided every length word stays below `2^256`. -/
theorem roundtrip_call (sig : String) (ts : List Ty) (hv : AllValid ts)
    (vs : TupleVal ts) (hl : TupleLenBounds ts vs)
    (hb : (encode (.tuple ts) vs).length < 2 ^ 256) :
    decodeCall ts (encodeCall sig ts vs) = some vs := by
  unfold decodeCall encodeCall
  rw [drop_append_of_length (length_selector sig)]
  exact roundtrip (.tuple ts) hv vs (by simpa [LenBound] using hl) hb

end EvmAbi
