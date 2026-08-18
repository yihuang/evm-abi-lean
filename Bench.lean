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

* **ValBA vs Val** — the runtime value family (`ValBA`) against the list
  payloads of `Ty.Val`, on flat `bytes[]`: aligned 256-byte elements (the
  zero padding is empty) and unaligned 100-byte elements (padding 28 per
  element).  Both decoders check that padding by index — `allZerosBA`, no
  list — so what the unaligned row still measures is the payload: a packed
  `ByteArray` window against a cons list.

Run this interpreted (`lake env lean --run Bench.lean`) and the numbers
invert: `ByteArray.emptyWithCapacity` and `ByteArray.push` are `@[extern]`,
so the builder only pays off in compiled code.
-/

open EvmAbi
open EvmAbi.Ty
open EvmAbi.Codec.ByteArray

def flatTy : Ty := .array .bytes

/-- A `bytes` value of `payload` bytes, packed (`ValBA` family). -/
def mkBytesBAOf (payload : Nat) (p : payload < 2 ^ 256) : {bs : ByteArray // bs.size < 2 ^ 256} :=
  ⟨(List.replicate payload 7).toByteArray, by
    simp [Binary.ByteArray.size_eq_toList_length, List.length_replicate]
    exact p⟩

/-- A flat `bytes[]` of `payload`-byte packed payloads. -/
def flatValBAOf (payload : Nat) (p : payload < 2 ^ 256)
    (n : Nat) (h : n < 2 ^ 256) : {vs : List (ValBA .bytes) // vs.length < 2 ^ 256} :=
  ⟨List.replicate n (mkBytesBAOf payload p), by simpa using h⟩

/-- A `bytes` value of `payload` bytes. -/
def mkBytesOf (payload : Nat) (p : payload < 2 ^ 256) : Ty.Val .bytes :=
  ⟨List.replicate payload 7, by simpa using p⟩

/-- A flat `bytes[]` of `payload`-byte elements. -/
def flatValOf (payload : Nat) (p : payload < 2 ^ 256)
    (n : Nat) (h : n < 2 ^ 256) : flatTy.Val :=
  ⟨List.replicate n (mkBytesOf payload p), by simpa using h⟩

/-- A `bytes` value of `n` bytes. -/
def mkBytes (n : Nat) (h : n < 2 ^ 256) : Ty.Val .bytes :=
  ⟨List.replicate n 7, by simpa using h⟩

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

/-- Run `act` `n` times; report nanoseconds and bytes per operation.

`act` takes the iteration index, and it has to be *reachable from the work*.
Lean floats closed subterms to cached top-level constants, so an `act` that
applies a function to top-level data is evaluated once and the loop then times
a field read — an early draft of the word-codec section below reported 32000
`ByteArray.push`es in "3 ns" this way.  A row that closes over a function
parameter (`benchTy`'s `t` and `v`, say) is safe because the closure is not
closed; a row written against top-level definitions must thread the index. -/
def timed (n : Nat) (act : Nat → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let mut checksum := 0
  for i in [0:n] do
    checksum := checksum + act i
  let t1 ← IO.monoNanosNow
  return ((t1 - t0) / n, checksum / n)

def timeIt (label : String) (act : Nat → Nat) : IO Unit := do
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

def benchValBA (payload : Nat) (p : payload < 2 ^ 256) (n : Nat) (h : n < 2 ^ 256) : IO Unit := do
  let v := flatValOf payload p n h
  let vba := flatValBAOf payload p n h
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

/-- `bytesN` payloads — the fixed-word decode.  `decodeStrictBA` reads each
payload as a ≤32-cell cons list (`windowList`) and repacks it;
`decodeStrict` now extracts the payload in one `copySlice` with the padding
checked by index (`allZerosBA`), so this row isolates the list round-trip. -/
def benchBytesN (n : Nat) (h : n < 2 ^ 256) : IO Unit := do
  let t : Ty := .array (.bytesN 32)
  let el : Ty.Val (.bytesN 32) := ⟨List.replicate 32 7, by simp⟩
  let v : t.Val := ⟨List.replicate n el, by simpa using h⟩
  let ba := Spec.encodeByteArray t v
  let elba : ValBA (.bytesN 32) := ⟨(List.replicate 32 7).toByteArray, by
    simp [Binary.ByteArray.size_eq_toList_length]⟩
  let vba : ValBA t := ⟨List.replicate n elba, by simpa using h⟩
  IO.println s!"-- bytes32[] × {n} ({ba.size} bytes)"
  timeIt "decodeStrictBA (List)  " (fun _ =>
    if (decodeStrictBA t ba).isSome then ba.size else 0)
  timeIt "decodeStrict (BA)    " (fun _ =>
    if (decodeStrict t ba).isSome then ba.size else 0)
  timeIt "encode (BA)          " (fun _ => (encode t vba).size)
  IO.println s!"  agree: {(decodeStrict t ba).isSome == (decodeStrictBA t ba).isSome}"

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
  (⟨0xdead, by decide⟩, wideWord, mkBytesBAOf 100 (by decide), ())

def flagsVal : ValBA flags.ty := (true, false, true, false, true, false, true, false, ())

def flagArrayVal (n : Nat) (h : n < 2 ^ 256) : ValBA flagArray.ty :=
  ⟨List.replicate n true, by simpa using h⟩

def wordArrayVal (n : Nat) (h : n < 2 ^ 256) : ValBA wordArray.ty :=
  ⟨List.replicate n wideWord, by simpa using h⟩

def bytesArrayVal (n : Nat) (h : n < 2 ^ 256) : ValBA bytesArray.ty :=
  ⟨List.replicate n (mkBytesBAOf 256 (by decide)), by simpa using h⟩

def pairArrayVal (n : Nat) (h : n < 2 ^ 256) : ValBA pairArray.ty :=
  ⟨List.replicate n (wideWord, true, ()), by simpa using h⟩

/-- Time `n` repetitions (the compiled rows are nanoseconds apart, so the
small shapes need many more than `reps`). -/
def timeItN (n : Nat) (label : String) (act : Nat → Nat) : IO Unit := do
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

/-! ## the word codec: where a full-width word's time goes

Every row above compares two ways of assembling the same bytes — they measure
*layout*.  These rows ask what the bytes themselves cost, which is the other
half of the encoder and, for ordinary calldata, much the larger half:
addresses, token amounts and hashes are all full-width, and `uint256[]` runs
~20× the per-element cost of `bool[]` through the very same layout.

An ABI word is a `UInt256`, which wraps `BitVec 256` = `Fin (2 ^ 256)` =
`Nat`.  Above `2 ^ 63` that is a heap GMP bignum, so each of the four
`n >>> 64` steps `Binary.Fast`'s chunked codec takes per word allocates, as
does each `acc <<< 64` on the way back in.

The rows isolate that:

* **wide** — full-width words, the case the rest of the benchmark uses.
* **small** — the same codec on words below `2 ^ 63`, where `Nat` is
  unboxed.  Wide minus small is the bignum cost and nothing else.
* **limbs** (read only) — the ceiling: the same 32 bytes read straight into
  four `UInt64`s, i.e. what the codec would cost if `UInt256` were a
  four-limb structure rather than a `Nat`.  This is a `lean-binary`
  question, not an `EvmAbi` one, which is why it is a ceiling here and not a
  patch.  There is no matching *write* row because it would not say
  anything: with the bignum gone, writing is 32 `ByteArray.push`es either
  way, which is what the floors below measure.

Then three local groups: what `Chunks.emitZeros` pays to write a dynamic
payload's padding against one `copySlice` out of a zero buffer, what an
*empty* padding run costs, and the two ways of moving 32 bytes.

Two of them are regression guards.  `emitZeros_eq_fast` makes the padding
pair the same code, so the two rows should agree, and a gap means the
`@[csimp]` swap stopped reaching `emit`.  `Builder.appendZeros` should put
the empty run on the floor row, and drifting up towards the `zeros 0` row
means the skip stopped happening. -/

open Binary

def wordCount : Nat := 1000

/-- Full-width words — every one a bignum. -/
def wideWords : Array UInt256 :=
  (Array.range wordCount).map fun i =>
    UInt256.ofNat (0x123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0 + i)

/-- The same count of words below `2 ^ 63` — every one an unboxed `Nat`. -/
def smallWords : Array UInt256 :=
  (Array.range wordCount).map fun i => UInt256.ofNat (0x1234567 + i)

def wordBuf (ws : Array UInt256) : ByteArray :=
  ws.foldl (init := ByteArray.emptyWithCapacity (32 * wordCount)) fun acc w =>
    acc ++ UInt256.toBEByteArray w

def wideBuf : ByteArray := wordBuf wideWords
def smallBuf : ByteArray := wordBuf smallWords

/-- `wordCount` words encoded the way `putUint` does, one fresh 32-byte
`ByteArray` each.  The fold starts at `seed`, so it cannot be hoisted. -/
def encodeWords (ws : Array UInt256) (seed : Nat) : Nat :=
  ws.foldl (init := seed) fun s w => s + (UInt256.toBEByteArray w)[31]!.toNat

/-- `wordCount` words read the way `natAtBA` reads them.  The result is
consumed by a comparison rather than arithmetic: `% 251` on a 256-bit result
is itself a bignum operation, and would be timed as part of the read. -/
def decodeWords (ba : ByteArray) (seed : Nat) : Nat := Id.run do
  let mut s := seed
  for i in [0:wordCount] do
    if decodeBEBytesFrom ba (32 * i) 32 == 0 then s := s + 1
  return s

/-- The ceiling for the row above: the same 32 bytes read into four `UInt64`
limbs, with no 256-bit `Nat` ever built. -/
def decodeWordLimbs (ba : ByteArray) (seed : Nat) : Nat := Id.run do
  let mut s := seed
  for i in [0:wordCount] do
    let o := 32 * i
    let a := beWord8 ba[o]!    ba[o+1]!  ba[o+2]!  ba[o+3]!  ba[o+4]!  ba[o+5]!  ba[o+6]!  ba[o+7]!
    let b := beWord8 ba[o+8]!  ba[o+9]!  ba[o+10]! ba[o+11]! ba[o+12]! ba[o+13]! ba[o+14]! ba[o+15]!
    let c := beWord8 ba[o+16]! ba[o+17]! ba[o+18]! ba[o+19]! ba[o+20]! ba[o+21]! ba[o+22]! ba[o+23]!
    let d := beWord8 ba[o+24]! ba[o+25]! ba[o+26]! ba[o+27]! ba[o+28]! ba[o+29]! ba[o+30]! ba[o+31]!
    if (a ||| b ||| c ||| d) == 0 then s := s + 1
  return s

/-- Padding as the encoder writes it, through `Chunks.emitZeros`.  The seeded
first push makes the accumulator — and so the whole loop — depend on the
iteration. -/
def padByEmitZeros (n seed : Nat) : Nat := Id.run do
  let mut acc := (ByteArray.emptyWithCapacity (n * wordCount + 1)).push (UInt8.ofNat seed)
  for _ in [0:wordCount] do
    acc := Chunks.emitZeros acc n
  return acc.size % 7

/-- The same padding as one `copySlice` out of `Chunks.zeroBuf` — which is
what `emitZeros` now compiles to, and at `n = 32` is also the floor for
moving a word's worth of bytes at all. -/
def padByCopy (n seed : Nat) : Nat := Id.run do
  let mut acc := (ByteArray.emptyWithCapacity (n * wordCount + 1)).push (UInt8.ofNat seed)
  for _ in [0:wordCount] do
    acc := Chunks.zeroBuf.copySlice 0 acc acc.size n false
  return acc.size % 7

/-! ### the empty padding run

A `bytesN 32`, and any `bytes` or `string` already a multiple of 32 long,
pads by nothing — which is most values, since payloads are usually word
aligned.  `Builder.appendZeros` skips the run there; these rows are what it
skips. -/

/-- 1000 distinct 32-byte payloads, so `32 - bs.size` is zero only at *run*
time: as a literal the padding — and then the whole builder — would fold
away. -/
def padPayloads : Array ByteArray :=
  (Array.range wordCount).map fun i => (List.replicate 32 (UInt8.ofNat i)).toByteArray

/-- Write each payload with `mk` and run the builder.  The rows below vary
only `mk`: the same bytes reached with the padding run built, skipped, or
never asked for.

`@[specialize]` is load-bearing.  Without it `mk` stays a closure called once
per payload, which costs ~3 ns/word on rows that are 27 to 45 — enough to
lift the floor and blur the guard. -/
@[specialize] def padEmpty (mk : ByteArray → Builder) (seed : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:wordCount] do
    s := s + (mk padPayloads[(seed + i) % wordCount]!).run.size
  return s

/-- The other way to move 32 bytes: one `push` each.  The byte is hoisted out
of the inner loop so the row times the pushes, not the arithmetic. -/
def pushFloor (seed : Nat) : Nat := Id.run do
  let mut s := 0
  for _ in [0:wordCount] do
    let byte := UInt8.ofNat seed
    let mut b := ByteArray.emptyWithCapacity 32
    for _ in [0:32] do
      b := b.push byte
    s := s + b[31]!.toNat
  return s

/-- Report nanoseconds per word rather than per operation. -/
def timeWord (label : String) (n : Nat) (act : Nat → Nat) : IO Unit := do
  let (ns, _) ← timed n act
  IO.println s!"  {label}: {ns / wordCount} ns/word"

def benchWordCodec : IO Unit := do
  IO.println s!"== the word codec ({wordCount} words per op) =="
  IO.println "-- write one uint256 as 32 big-endian bytes"
  timeWord "wide  (bignum)          " 200 (encodeWords wideWords)
  timeWord "small (< 2^63)          " 200 (encodeWords smallWords)
  IO.println "-- read one uint256 from 32 big-endian bytes"
  timeWord "wide  (bignum)          " 200 (decodeWords wideBuf)
  timeWord "small (< 2^63)          " 200 (decodeWords smallBuf)
  timeWord "limbs (ceiling)         " 200 (decodeWordLimbs wideBuf)
  IO.println "-- 28 bytes of zero padding (the unaligned `bytes` tail)"
  timeWord "Chunks.emitZeros        " 200 (padByEmitZeros 28)
  timeWord "copySlice from zero buf " 200 (padByCopy 28)
  IO.println "-- an empty padding run (the word-aligned payload)"
  timeWord "b ++ zeros 0            " 200
    (padEmpty fun bs => Builder.chunk bs ++ Builder.zeros (32 - bs.size))
  timeWord "appendZeros b 0         " 200
    (padEmpty fun bs => Builder.appendZeros (Builder.chunk bs) (32 - bs.size))
  timeWord "payload alone (floor)   " 200 (padEmpty Builder.chunk)
  IO.println "-- the two ways of moving 32 bytes"
  timeWord "32x ByteArray.push      " 200 pushFloor
  timeWord "1x 32-byte copySlice    " 200 (padByCopy 32)

def main : IO Unit := do
  IO.println "== flat bytes[], 256-byte elements (constant factor) =="
  benchTy "-- 500 elements"  flatTy (flatValOf 256 (by decide) 500 (by decide))
  benchTy "-- 2000 elements" flatTy (flatValOf 256 (by decide) 2000 (by decide))
  IO.println "== uint256[], full-width values (bignum word encoding) =="
  benchTy "-- 1000 words" wideTy (wideVal 1000 (by decide))
  IO.println "== nested tuples (bytes, (bytes, ...)) (asymptotics) =="
  benchTy "-- depth 50"  (nest 50)  (nestVal 50)
  benchTy "-- depth 200" (nest 200) (nestVal 200)
  -- the two encoders must agree byte for byte — this is `encodeByteArray_eq`
  let v := flatValOf 256 (by decide) 50 (by decide)
  let w := nestVal 20
  IO.println "== decode: list cursors vs offset cursors =="
  -- `Spec.decodeStrict` converts the buffer to a list and slices it; `decodeStrictBA`
  -- walks the same buffer by offset.  Same theorem, same answer.
  benchDecode "-- 500 elements"  (Spec.encodeByteArray flatTy (flatValOf 256 (by decide) 500 (by decide)))
  benchDecode "-- 2000 elements" (Spec.encodeByteArray flatTy (flatValOf 256 (by decide) 2000 (by decide)))
  IO.println s!"agree(flat)   = {(Spec.encode flatTy v).toByteArray == Spec.encodeByteArray flatTy v}"
  IO.println s!"agree(nested) = {(Spec.encode (nest 20) w).toByteArray == Spec.encodeByteArray (nest 20) w}"
  IO.println "== ValBA vs Val: aligned 256-byte payloads (pad 0) =="
  benchValBA 256 (by decide) 500 (by decide)
  benchValBA 256 (by decide) 2000 (by decide)
  IO.println "== ValBA vs Val: unaligned 100-byte payloads (pad 28 — the list-free pad check) =="
  benchValBA 100 (by decide) 2000 (by decide)
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
    callArgs.ty (callArgs.encode callVal) callArgs.decodeStrict
  benchCompiledDecode "-- (bool × 8): cheap words, layout-bound" 200000
    flags.ty (flags.encode flagsVal) flags.decodeStrict
  benchCompiledDecode "-- bool[], 100 elements" 20000
    flagArray.ty (flagArray.encode (flagArrayVal 100 (by decide))) flagArray.decodeStrict
  benchCompiledDecode "-- uint256[], 100 elements" 20000
    wordArray.ty (wordArray.encode (wordArrayVal 100 (by decide))) wordArray.decodeStrict
  benchCompiledDecode "-- (uint256, bool)[], 100 elements" 10000
    pairArray.ty (pairArray.encode (pairArrayVal 100 (by decide))) pairArray.decodeStrict
  benchCompiledDecode "-- bytes[], 100 × 256 B" 5000
    bytesArray.ty (bytesArray.encode (bytesArrayVal 100 (by decide))) bytesArray.decodeStrict
  IO.println "== bytesN: fixed-word payloads (list round-trip vs one extract) =="
  benchBytesN 2000 (by decide)
  benchWordCodec
