import EvmAbi
import EvmAbi.Compile.Meta

/-!
# Bench

A benchmark for the executable codec — `Spec.encodeByteArray` and
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
  `Spec.encode` concatenates with `++` at every level, so a `d`-deep value has
  its bytes re-copied `d` times (`O(n · d)`); the builder makes
  concatenation an `O(1)` constructor, so it stays linear.

Run this interpreted (`lake env lean --run Bench.lean`) and the numbers
invert: `ByteArray.emptyWithCapacity` and `ByteArray.push` are `@[extern]`,
so the builder only pays off in compiled code.
-/

open EvmAbi
open EvmAbi.Ty

/-- A `bytes` payload as a packed `ByteArray` (the `ValBA` value family). -/
def mkBytesBA (n : Nat) : ByteArray :=
  (List.replicate n 7).toByteArray

def mkBytesBA256 : {bs : ByteArray // bs.size < 2 ^ 256} := ⟨mkBytesBA 256, by native_decide⟩

/-- A flat `bytes[]` of packed payloads. -/
def flatValBA (n : Nat) (h : n < 2 ^ 256) : {vs : List (ValBA .bytes) // vs.length < 2 ^ 256} :=
  ⟨List.replicate n mkBytesBA256, by simpa using h⟩

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

/-- Run `act` `n` times; report nanoseconds and bytes per operation. -/
def timed (n : Nat) (act : Unit → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [0:n] do
    checksum := checksum + act ()
  let t1 ← IO.monoNanosNow
  return ((t1 - t0) / n, checksum / n)

def timeIt (label : String) (act : Unit → Nat) : IO Unit := do
  let (ns, sz) ← timed reps act
  IO.println s!"  {label}: {ns / 1000} us/op  ({sz} bytes)"

def benchTy (label : String) (t : Ty) (v : t.Val) : IO Unit := do
  IO.println label
  timeIt "spec  Spec.encode ++ toByteArray" (fun _ => (Spec.encode t v).toByteArray.size)
  timeIt "fast  Spec.encodeByteArray      " (fun _ => (Spec.encodeByteArray t v).size)

/-- Decode the same buffer both ways; the `bytes` count is the buffer size. -/
def benchDecode (label : String) (ba : ByteArray) : IO Unit := do
  IO.println s!"{label} ({ba.size} bytes)"
  timeIt "spec  Spec.decodeStrict   (list)" (fun _ =>
    if (Spec.decodeStrict flatTy ba.data.toList).isSome then ba.size else 0)
  timeIt "fast  decodeStrictBA       " (fun _ =>
    if (decodeStrictBA flatTy ba).isSome then ba.size else 0)

def benchValBA (n : Nat) (h : n < 2 ^ 256) : IO Unit := do
  let v := flatVal n h
  let vba := flatValBA n h
  -- Not `Spec.encodeByteArray flatTy v`: that shares the subexpression with the
  -- encode row below, which then times a field read and prints 0 us/op.  Same
  -- bytes by `Spec.encodeByteArray_eq`.
  let ba := (Spec.encode flatTy v).toByteArray
  IO.println s!"-- {n} elements ({ba.size} bytes)"
  timeIt "decodeStrictBA (List)  " (fun _ =>
    if (decodeStrictBA flatTy ba).isSome then ba.size else 0)
  timeIt "decodeStrict (BA)    " (fun _ =>
    if (decodeStrict flatTy ba).isSome then ba.size else 0)
  timeIt "Spec.encodeByteArray (List) " (fun _ => (Spec.encodeByteArray flatTy v).size)
  timeIt "encode (BA)          " (fun _ => (encode flatTy vba).size)
  IO.println s!"  agree: {(encode flatTy vba) == (Spec.encodeByteArray flatTy v)} ∧ {(decodeStrict flatTy ba).isSome == (decodeStrictBA flatTy ba).isSome}" 

/-! ## the compiled encoder (`EvmAbi.Compile.Meta`)

The compiled encoder writes the same bytes as `encode` (that is `foo_eq`), so
what these rows measure is only what compilation removed: the `Ty` match per
value, the `isStatic` test per component *and per array element*, the
`List Part` a tuple or array allocates, and the three walks `putParts` makes
over it.  Small values show it best — there the per-call work is the work. -/

open EvmAbi.Compile.Meta

abi_codec callArgs "transfer(address to, uint256 amount)"
abi_codec callArgsDyn "submit(address to, uint256 amount, bytes data)"
abi_codec wordArray "uint256[]"
abi_codec bytesArray "bytes[]"
abi_codec pairArray "(uint256,bool)[]"
abi_codec flags "(bool,bool,bool,bool,bool,bool,bool,bool)"
abi_codec flagArray "bool[]"

def wideWord : ValBA (.uint 256) :=
  ⟨0x123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0, by decide⟩

def callVal : ValBA callArgs.ty := (⟨0xdead, by decide⟩, wideWord, ())

def callDynVal : ValBA callArgsDyn.ty :=
  (⟨0xdead, by decide⟩, wideWord, ⟨mkBytesBA 100, by native_decide⟩, ())

def flagsVal : ValBA flags.ty := (true, false, true, false, true, false, true, false, ())

def flagArrayVal (n : Nat) (h : n < 2 ^ 256) : ValBA flagArray.ty :=
  ⟨List.replicate n true, by simpa using h⟩

def wordArrayVal (n : Nat) (h : n < 2 ^ 256) : ValBA wordArray.ty :=
  ⟨List.replicate n wideWord, by simpa using h⟩

def bytesArrayVal (n : Nat) (h : n < 2 ^ 256) : ValBA bytesArray.ty :=
  ⟨List.replicate n mkBytesBA256, by simpa using h⟩

def pairArrayVal (n : Nat) (h : n < 2 ^ 256) : ValBA pairArray.ty :=
  ⟨List.replicate n (wideWord, true, ()), by simpa using h⟩

/-- Time `n` repetitions (the compiled rows are nanoseconds apart, so the
small shapes need many more than `reps`). -/
def timeItN (n : Nat) (label : String) (act : Unit → Nat) : IO Unit := do
  let (ns, sz) ← timed n act
  IO.println s!"  {label}: {ns} ns/op  ({sz} bytes)"

def benchCompiled (label : String) (n : Nat) (t : Ty) (v : ValBA t)
    (compiled : ValBA t → ByteArray) : IO Unit := do
  IO.println label
  timeItN n "generic  encode " (fun _ => (encode t v).size)
  timeItN n "compiled        " (fun _ => (compiled v).size)
  IO.println s!"  agree: {compiled v == encode t v}"

/-- The same for the decoder: both walk the buffer the compiled encoder
wrote, and must accept or reject it identically. -/
def benchCompiledDecode (label : String) (n : Nat) (t : Ty) (ba : ByteArray)
    (compiled : ByteArray → Option (ValBA t)) : IO Unit := do
  IO.println label
  timeItN n "generic  decodeStrict " (fun _ => if (decodeStrict t ba).isSome then ba.size else 0)
  timeItN n "compiled              " (fun _ => if (compiled ba).isSome then ba.size else 0)
  IO.println s!"  agree: {(compiled ba).isSome == (decodeStrict t ba).isSome}"

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
  -- `Spec.decodeStrict` converts the buffer to a list and slices it; `decodeStrictBA`
  -- walks the same buffer by offset.  Same theorem, same answer.
  benchDecode "-- 500 elements"  (Spec.encodeByteArray flatTy (flatVal 500 (by decide)))
  benchDecode "-- 2000 elements" (Spec.encodeByteArray flatTy (flatVal 2000 (by decide)))
  IO.println s!"agree(flat)   = {(Spec.encode flatTy v).toByteArray == Spec.encodeByteArray flatTy v}"
  IO.println s!"agree(nested) = {(Spec.encode (nest 20) w).toByteArray == Spec.encodeByteArray (nest 20) w}"
  IO.println "== ValBA (packed payloads) vs Val (List payloads) =="
  benchValBA 500 (by decide)
  benchValBA 2000 (by decide)
  IO.println "== compiled encoder vs generic encoder =="
  benchCompiled "-- (address, uint256): one call's arguments" 200000
    callArgs.ty callVal callArgs.encode
  benchCompiled "-- (address, uint256, bytes): one call's arguments, dynamic" 100000
    callArgsDyn.ty callDynVal callArgsDyn.encode
  benchCompiled "-- uint256[], 100 elements" 20000
    wordArray.ty (wordArrayVal 100 (by decide)) wordArray.encode
  benchCompiled "-- (uint256, bool)[], 100 elements" 10000
    pairArray.ty (pairArrayVal 100 (by decide)) pairArray.encode
  benchCompiled "-- bytes[], 100 × 256 B" 5000
    bytesArray.ty (bytesArrayVal 100 (by decide)) bytesArray.encode
  benchCompiled "-- (bool × 8): cheap words, layout-bound" 200000
    flags.ty flagsVal flags.encode
  benchCompiled "-- bool[], 100 elements: cheap words, layout-bound" 20000
    flagArray.ty (flagArrayVal 100 (by decide)) flagArray.encode
  IO.println "== compiled decoder vs generic decoder =="
  benchCompiledDecode "-- (address, uint256): one call's arguments" 200000
    callArgs.ty (callArgs.encode callVal) callArgs.decode
  benchCompiledDecode "-- (bool × 8): cheap words, layout-bound" 200000
    flags.ty (flags.encode flagsVal) flags.decode
  benchCompiledDecode "-- bool[], 100 elements" 20000
    flagArray.ty (flagArray.encode (flagArrayVal 100 (by decide))) flagArray.decode
  benchCompiledDecode "-- uint256[], 100 elements" 20000
    wordArray.ty (wordArray.encode (wordArrayVal 100 (by decide))) wordArray.decode
  benchCompiledDecode "-- (uint256, bool)[], 100 elements" 10000
    pairArray.ty (pairArray.encode (pairArrayVal 100 (by decide))) pairArray.decode
  benchCompiledDecode "-- bytes[], 100 × 256 B" 5000
    bytesArray.ty (bytesArray.encode (bytesArrayVal 100 (by decide))) bytesArray.decode
