import EvmAbi

/-!
# Bench

A benchmark for the executable codec — `encodeByteArray` and
`decodeStrictBA` — against the `List UInt8` specification each is proved
equal to.  Build and run with

```bash
lake build bench && ./.lake/build/bin/bench
```

Two shapes are measured, because they fail differently:

* **flat `bytes[]`** — both encoders are linear here, so this measures the
  constant factor: the specification builds the whole buffer as a
  `List UInt8` (a cons cell and a boxed byte per byte) and converts at the
  end, while the builder writes into a pre-sized `ByteArray`.

* **nested tuples** `(bytes, (bytes, (…)))` — this measures the asymptotics.
  `encode` concatenates with `++` at every level, so a `d`-deep value has
  its bytes re-copied `d` times (`O(n · d)`); the builder makes
  concatenation an `O(1)` constructor, so it stays linear.

Run this interpreted (`lake env lean --run Bench.lean`) and the numbers
invert: `ByteArray.emptyWithCapacity` and `ByteArray.push` are `@[extern]`,
so the builder only pays off in compiled code.
-/

open EvmAbi
open EvmAbi.Ty

/-- A `bytes` value of `n` bytes. -/
def mkBytes (n : Nat) (h : n < 2 ^ 256) : Ty.Val .bytes :=
  ⟨List.replicate n 7, by simpa using h⟩

/-- A flat `bytes[]`. -/
def flatTy : Ty := .array .bytes

def flatVal (n : Nat) (h : n < 2 ^ 256) : flatTy.Val :=
  ⟨List.replicate n (mkBytes 256 (by decide)), by simpa using h⟩

/-- A `uint256[]` of full-width values — token amounts, hashes and addresses
are all above `2 ^ 63`, so every word goes through `Nat`'s bignum path.  This
is the case `Binary.Fast`'s chunked encoder exists for. -/
def wideTy : Ty := .array (.uint 256)

def wideVal (n : Nat) (h : n < 2 ^ 256) : wideTy.Val :=
  ⟨List.replicate n ⟨0x123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0,
    by decide⟩, by simpa using h⟩

/-- `nest k = (bytes, (bytes, … ))`, `k` tuples deep. -/
def nest : Nat → Ty
  | 0 => .tuple [.bytes]
  | k + 1 => .tuple [.bytes, nest k]

def nestVal : (k : Nat) → (nest k).Val
  | 0 => (mkBytes 256 (by decide), ())
  | k + 1 => (mkBytes 256 (by decide), nestVal k, ())

def reps : Nat := 20

def timeIt (label : String) (act : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [0:reps] do
    checksum := checksum + act ()
  let t1 ← IO.monoNanosNow
  IO.println s!"  {label}: {(t1 - t0) / (1000 * reps)} us/op  ({checksum / reps} bytes)"

def benchTy (label : String) (t : Ty) (v : t.Val) : IO Unit := do
  IO.println label
  timeIt "spec  encode ++ toByteArray" (fun _ => (encode t v).toByteArray.size)
  timeIt "fast  encodeByteArray      " (fun _ => (encodeByteArray t v).size)

/-- Decode the same buffer both ways; the `bytes` count is the buffer size. -/
def benchDecode (label : String) (ba : ByteArray) : IO Unit := do
  IO.println s!"{label} ({ba.size} bytes)"
  timeIt "spec  decodeStrict   (list)" (fun _ =>
    if (decodeStrict flatTy ba.data.toList).isSome then ba.size else 0)
  timeIt "fast  decodeStrictBA       " (fun _ =>
    if (decodeStrictBA flatTy ba).isSome then ba.size else 0)

def main : IO Unit := do
  IO.println "== flat bytes[], 256-byte elements (constant factor) =="
  benchTy "-- 500 elements"  flatTy (flatVal 500 (by decide))
  benchTy "-- 2000 elements" flatTy (flatVal 2000 (by decide))
  IO.println "== uint256[], full-width values (bignum word encoding) =="
  benchTy "-- 1000 words" wideTy (wideVal 1000 (by decide))
  IO.println "== nested tuples (bytes, (bytes, ...)) (asymptotics) =="
  benchTy "-- depth 50"  (nest 50)  (nestVal 50)
  benchTy "-- depth 200" (nest 200) (nestVal 200)
  -- the two encoders must agree byte for byte — this is `encodeByteArray_eq`
  let v := flatVal 50 (by decide)
  let w := nestVal 20
  IO.println "== decode: list cursors vs offset cursors =="
  -- `decodeStrict` converts the buffer to a list and slices it; `decodeStrictBA`
  -- walks the same buffer by offset.  Same theorem, same answer.
  benchDecode "-- 500 elements"  (encodeByteArray flatTy (flatVal 500 (by decide)))
  benchDecode "-- 2000 elements" (encodeByteArray flatTy (flatVal 2000 (by decide)))
  IO.println s!"agree(flat)   = {(encode flatTy v).toByteArray == encodeByteArray flatTy v}"
  IO.println s!"agree(nested) = {(encode (nest 20) w).toByteArray == encodeByteArray (nest 20) w}"
