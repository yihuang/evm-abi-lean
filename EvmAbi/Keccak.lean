import EvmAbi.Word

namespace EvmAbi

open Binary

/-!
# EvmAbi.Keccak

The Keccak-256 hash, isolated behind an opaque signature.

The ABI only ever consumes the hash through the four-byte function
selector, so this layer fixes *no* implementation: `keccak256` is an opaque
constant (a 256-bit word), and every downstream theorem is stated so that
its proof never needs to look inside.  A concrete implementation (or a
verified binding to one) can later replace the opaque constant without
touching the call-encoding layer.
-/

/-- `UInt256` is nonempty (needed to keep `keccak256` an opaque constant). -/
instance : Nonempty UInt256 := ⟨⟨0#256⟩⟩

/-- Keccak-256 as a 256-bit word (implementation deliberately not given at
this layer). -/
opaque keccak256 (bs : List UInt8) : UInt256

/-- The four-byte function selector of a canonical signature: the first four
bytes of its Keccak-256 hash. -/
noncomputable def selector (sig : String) : List UInt8 :=
  (bytesOfWord (keccak256 sig.toUTF8.data.toList)).take 4

/-- A selector is exactly four bytes. -/
theorem length_selector (sig : String) : (selector sig).length = 4 := by
  rw [selector, List.length_take, length_bytesOfWord]; rfl

end EvmAbi
