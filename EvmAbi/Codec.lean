import EvmAbi.Ty
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Align
import EvmAbi.Word

/-!
# EvmAbi.Codec

The `Ty`-indexed encode/decode dispatch layer (roadmap design decisions
1 & 2): turns the standalone per-type functions of `Static`/`Dynamic` into
a single `encode : (t : Ty) → t.Val → List UInt8` / `decode : (t : Ty) →
List UInt8 → Option t.Val` that dispatches by type index.

This is the "试运行" of the type-indexed proof machine (node 4).  Every
static type is handled, and the roundtrip theorem for dynamic `bytes`/`string`
is unified under the same `decode t (encode t v) = some v` statement via
`LenBound`.
-/

namespace EvmAbi

open Ty
open Binary

/-! ## Ty-indexed encode / decode -/

/-- ABI encoder (type-indexed; thin wrapper around the standalone codecs). -/
def encode (t : Ty) (v : t.Val) : List UInt8 :=
  match t, v with
  | .uint _, ⟨n, _⟩   => encodeUint n
  | .int _,  ⟨i, _⟩   => encodeInt i
  | .bool,   b         => encodeBool b
  | .address, ⟨n, _⟩  => encodeAddress n
  | .bytesN _, ⟨bs, _⟩ => encodeBytesN bs
  | .bytes,   bs       => encodeBytes bs
  | .string,  s        => encodeString s

/-- ABI decoder (type-indexed): reads a value from the buffer, then
refines it through the type's range / length constraints encoded in
`t.Val`.  A malformed buffer or an out-of-range value yields `none`.

Because `Val` is `@[reducible]`, the subtype patterns (`⟨n, h⟩`) are
accepted directly by the elaborator. -/
def decode (t : Ty) (buf : List UInt8) : Option t.Val :=
  match t with
  | .uint m =>
    match decodeUint buf with
    | some n => if h : n < 2 ^ m then some ⟨n, h⟩ else none
    | none   => none
  | .int m =>
    match decodeInt buf with
    | some i =>
      if h : -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) then
        some ⟨i, h⟩
      else none
    | none   => none
  | .bool    => decodeBool buf
  | .address =>
    match decodeAddress buf with
    | some n => if h : n < 2 ^ 160 then some ⟨n, h⟩ else none
    | none   => none
  | .bytesN m =>
    match decodeBytesN m buf with
    | some bs => if h : bs.length = m then some ⟨bs, h⟩ else none
    | none    => none
  | .bytes   => decodeBytes buf
  | .string  => decodeString buf

/-! ## Roundtrip for static types (node 4) -/

/-- **Node 4 roundtrip**: every static base type decodes its own encoding
    without any length-bound side condition. -/
theorem roundtrip_static (t : Ty) (hs : t.IsStatic) (hv : t.Valid) (v : t.Val) :
    decode t (encode t v) = some v := by
  cases t
  case uint m =>
    obtain ⟨n, hn⟩ := v
    have hdec : decodeUint (encodeUint n) = some n :=
      decodeUint_encodeUint_of_lt hv.2.1 hn
    simp [encode, decode, hdec, hn]
  case int m =>
    obtain ⟨i, hi⟩ := v
    have ⟨hl0, hu0⟩ := hi
    have h0 : 0 < m := by
      have h8 := hv.1
      omega
    have hcast := (Int.natCast_pow 2 (m - 1)).symm
    have hl : -(2 : Int) ^ (m - 1) ≤ i := by
      simpa [hcast] using hl0
    have hu : i < (2 : Int) ^ (m - 1) := by
      simpa [hcast] using hu0
    have hdec : decodeInt (encodeInt i) = some i :=
      decodeInt_encodeInt h0 hv.2.1 hl hu
    simpa [encode, decode, hdec, hi]
  case bool =>
    simp only [encode, decode]
    exact decodeBool_encodeBool v
  case address =>
    obtain ⟨n, hn⟩ := v
    have hdec : decodeAddress (encodeAddress n) = some n :=
      decodeAddress_encodeAddress hn
    simp [encode, decode, hdec, hn]
  case bytesN m =>
    obtain ⟨bs, hbs⟩ := v
    have hdec : decodeBytesN m (encodeBytesN bs) = some bs :=
      decodeBytesN_encodeBytesN hbs
    simp [encode, decode, hdec, hbs]
  case bytes =>
    simp [Ty.IsStatic] at hs
  case string =>
    simp [Ty.IsStatic] at hs

/-- Static encodings are exactly one 32-byte word (node 4). -/
theorem encodeStatic_length (t : Ty) (hs : t.IsStatic) (hv : t.Valid) (v : t.Val) :
    (encode t v).length = 32 := by
  cases t
  case uint m =>
    obtain ⟨n, -⟩ := v; simp [encode, length_encodeUint]
  case int m =>
    obtain ⟨i, -⟩ := v; simp [encode, encodeInt, length_encodeUint]
  case bool =>
    simp [encode, encodeBool, length_encodeUint]
  case address =>
    obtain ⟨n, -⟩ := v; simp [encode, encodeAddress, length_encodeUint]
  case bytesN m =>
    obtain ⟨bs, hbs⟩ := v
    obtain ⟨h1, h32⟩ := hv
    simp [encode, encodeBytesN]
    rw [hbs]
    omega
  case bytes =>
    simp [Ty.IsStatic] at hs
  case string =>
    simp [Ty.IsStatic] at hs

/-! ## Roundtrip for dynamic types (node 5) -/

/-- **Node 5 roundtrip** for `bytes` (requires the length word not to wrap). -/
theorem roundtrip_bytes (bs : List UInt8) (h : bs.length < 2 ^ 256) :
    decode .bytes (encode .bytes bs) = some bs := by
  simp only [encode, decode]
  exact decodeBytes_encodeBytes h

/-- **Node 5 roundtrip** for `string`. -/
theorem roundtrip_string (s : String) (h : s.toUTF8.size < 2 ^ 256) :
    decode .string (encode .string s) = some s := by
  have hb : s.toUTF8.data.toList.length < 2 ^ 256 := by
    rw [← Binary.ByteArray.size_eq_toList_length s.toUTF8]
    exact h
  simp only [encode, decode]
  exact decodeString_encodeString hb

/-- Every encoding is 32-byte aligned. -/
theorem encode_length_aligned (t : Ty) (hv : t.Valid) (v : t.Val) :
    Aligned (encode t v).length := by
  by_cases hs : t.IsStatic
  · rw [encodeStatic_length t hs hv v]
    exact aligned_mul 1
  · cases t <;> simp [Ty.IsStatic] at hs
    case bytes =>
      simp only [encode, encodeBytes, List.length_append, length_encodeUint]
      exact aligned_add (aligned_mul 1) (dvd_length_pad32 _)
    case string =>
      simp only [encode, encodeString, encodeBytes, List.length_append, length_encodeUint]
      exact aligned_add (aligned_mul 1) (dvd_length_pad32 _)

/-! ## Unified roundtrip -/

/-- **Roundtrip (nodes 4–5)**: decoding an encoding returns the value for
every valid base type whose dynamic payload fits the length word. -/
theorem roundtrip (t : Ty) (hv : t.Valid) (v : t.Val) (hb : LenBound t v) :
    decode t (encode t v) = some v := by
  by_cases hs : t.IsStatic
  · exact roundtrip_static t hs hv v
  · -- only bytes / string can be here (IsStatic = false)
    cases t <;> simp [Ty.IsStatic] at hs
    case bytes =>
      exact roundtrip_bytes v hb
    case string =>
      exact roundtrip_string v hb

end EvmAbi
