import EvmAbi

/-!
# BenchRegress

The regression bench: one keyed row per code path the encoder dispatches to,
and nothing else.  `Bench.lean` is the exploratory one and prints prose with
labels that repeat and cannot be joined on; this prints only

```
BENCH <key> <ns/op> <bytes>
```

Three things follow from being what CI compares.

The row set comes from the `match` in `Codec/Stream.lean`, not from what is
interesting to look at: an arm with no row is an arm whose regression is
invisible.

Nanoseconds, not microseconds.  Rounded to whole microseconds a row at
11 µs/op moves in steps of 9%, so a 5% regression is unrepresentable.

Reps come from a time budget, not a constant, so every row carries the same
amount of noise rather than 220 µs of work on one and 7 ms on another.

`--once` runs a single rep and skips the probe, for
`valgrind --tool=callgrind`, where the count is deterministic and repetition
buys nothing.  Naming keys runs only those rows.
-/

open EvmAbi
open EvmAbi.Ty
open EvmAbi.Codec
open EvmAbi.Codec.ByteArray

/-! ## harness -/

/-- Nanoseconds and bytes per operation over `n` reps.

`act` takes the iteration index and must be *reachable from the work*: Lean
floats closed subterms to cached top-level constants, so an `act` applied to
top-level data is evaluated once and the loop then times a field read.  Every
row below closes over a function parameter, which is not closed and so is
safe. -/
def timed (n : Nat) (act : Nat → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let mut checksum := 0
  for i in [0:n] do
    checksum := checksum + act i
  let t1 ← IO.monoNanosNow
  return ((t1 - t0) / n, checksum / n)

/-- How long each row runs once it is past the probe. -/
def budgetNs : Nat := 50000000

/-- Ceiling on the rep count, so a row that probes at 0 ns does not spin. -/
def maxReps : Nat := 4000000

structure Opts where
  /-- One rep, no probe: the shape a deterministic profiler wants. -/
  once : Bool := false
  /-- Run only these keys; empty runs all of them. -/
  keys : List String := []
  deriving Inhabited

def parseArgs (args : List String) : Opts :=
  args.foldl (init := {}) fun o a =>
    if a == "--once" then { o with once := true } else { o with keys := o.keys ++ [a] }

def Opts.wants (o : Opts) (key : String) : Bool :=
  o.keys.isEmpty || o.keys.contains key

/-- Time one row and print it.  The caller has already checked `wants`, so
that the values a skipped row would need are never built. -/
def Opts.emit (o : Opts) (key : String) (act : Nat → Nat) : IO Unit := do
  let n ← if o.once then pure 1 else do
    -- one untimed rep pays the first-touch page faults, then a short probe
    -- sizes the real run
    let _ ← timed 1 act
    let (probe, _) ← timed 8 act
    pure (min maxReps (max 8 (budgetNs / max probe 1)))
  let (ns, sz) ← timed n act
  IO.println s!"BENCH {key} {ns} {sz}"

/-! ## values

Each builder is a function, never a top-level constant: Lean initialises
closed constants at module load, so a constant would be built even by a run
that asks for a different row. -/

/-- A `bytes` payload of `n` bytes. -/
def bytesBA (n : Nat) (h : n < 2 ^ 64) : ValBA .bytes :=
  ⟨(List.replicate n 7).toByteArray, by
    simp [Binary.ByteArray.size_eq_toList_length, List.length_replicate]
    exact h⟩

/-- The same payload as the specification's list family, for building decode
inputs.  Never timed. -/
def bytesVal (n : Nat) (h : n < 2 ^ 64) : Ty.Val .bytes :=
  ⟨List.replicate n 7, by simpa using h⟩

/-- A full-width word: token amounts, hashes and addresses all sit above
`2 ^ 63`, so this is the case the limb encoder exists for. -/
def wideWord : ValBA (.uint 32) :=
  ⟨0x123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0, by decide⟩

def wideInt : ValBA (.int 32) :=
  ⟨0x123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef, by decide⟩

/-- A real 160-bit address.  `0xdead` would leave `Nat` unboxed and hide the
cost this row exists to watch. -/
def wideAddress : ValBA .address :=
  ⟨(List.replicate 20 0xab).toByteArray, by
    simp [Binary.ByteArray.size_eq_toList_length]⟩

/-- The payload bound is stated against `Width.bytes`, which `simp` does not
unfold on its own. -/
def word32 : ValBA (.bytesN 32) :=
  ⟨(List.replicate 32 7).toByteArray, by
    simp [Binary.ByteArray.size_eq_toList_length]; decide⟩

def text : ValBA .string := ⟨"".pushn 'a' 256, by native_decide⟩

/-- `n` copies of `v`, as the array value of `t[]`. -/
def arrayOf {t : Ty} (v : ValBA t) (n : Nat) (h : n < 2 ^ 64) : ValBA (.array t) :=
  ⟨List.replicate n v, by simpa using h⟩

/-- `nest k = (bytes, (bytes, …))`, `k` tuples deep — the dynamic general
path, where go-ethereum's re-append is `O(n · d)` and the size tree is not. -/
def nest : Nat → Ty
  | 0 => .tuple .bytes []
  | k + 1 => .tuple .bytes [nest k]

def nestVal : (k : Nat) → ValBA (nest k)
  | 0 => (bytesBA 256 (by decide), ())
  | k + 1 => (bytesBA 256 (by decide), nestVal k, ())

/-- A statically sized tuple: the one arm of `encodeFast` that is neither an
array nor `emitAnyRun`, reached through `t.isStatic`. -/
def staticTy : Ty := .tuple (.uint 32) [.bool, .bytesN 32, .address]

def staticVal : ValBA staticTy := (wideWord, true, word32, wideAddress, ())

/-! ## rows

Values arrive as thunks: a row that is not selected never builds its own, so
a per-row instruction count is not diluted by the others' setup.  `mk ()` is
bound once, outside the timing loop, and the closure then captures a local —
never a closed term, which Lean would float to a cached constant and leave
the loop timing a field read. -/

def encodeRow (o : Opts) (key : String) (t : Ty) (mk : Unit → ValBA t) : IO Unit := do
  if o.wants key then
    let v := mk ()
    o.emit key (fun _ => (encode t v).size)

def decodeRow (o : Opts) (key : String) (t : Ty) (mk : Unit → ByteArray) : IO Unit := do
  if o.wants key then
    let ba := mk ()
    o.emit key (fun _ => if (decodeStrict t ba).isSome then ba.size else 0)

/-- A `bytes[]` encode row.  256 pads by nothing, 100 by 28 per element. -/
def bytesArrayEncode (o : Opts) (key : String) (payload : Nat) (hp : payload < 2 ^ 64)
    (n : Nat) (h : n < 2 ^ 64) : IO Unit :=
  encodeRow o key (.array .bytes) fun _ => arrayOf (bytesBA payload hp) n h

/-- The matching decode row.  The buffer comes from the specification, not
from `encode`: sharing the subexpression would leave the encode row timing a
field read. -/
def bytesArrayDecode (o : Opts) (key : String) (payload : Nat) (hp : payload < 2 ^ 64)
    (n : Nat) (h : n < 2 ^ 64) : IO Unit :=
  decodeRow o key (.array .bytes) fun _ =>
    Spec.encodeByteArray (.array .bytes) ⟨List.replicate n (bytesVal payload hp), by simpa using h⟩

/-- An array's encode and decode rows.  `t` is explicit because `ValBA`
reduces at several of these (`ValBA .bool` *is* `Bool`), so an implicit would
have nothing to unify against. -/
def staticArrayRows (o : Opts) (encKey decKey : String) (t : Ty) (v : ValBA t)
    (n : Nat) (h : n < 2 ^ 64) : IO Unit := do
  encodeRow o encKey (.array t) fun _ => arrayOf v n h
  decodeRow o decKey (.array t) fun _ => encode (.array t) (arrayOf v n h)

def main (args : List String) : IO Unit := do
  let o := parseArgs args

  -- `.array .bytes` — the dynamic-element arm, with and without padding
  bytesArrayEncode o "encode/bytes-array/500"       256 (by decide) 500  (by decide)
  bytesArrayEncode o "encode/bytes-array/2000"      256 (by decide) 2000 (by decide)
  bytesArrayEncode o "encode/bytes-unaligned/2000"  100 (by decide) 2000 (by decide)
  bytesArrayDecode o "decode/bytes-array/500"       256 (by decide) 500  (by decide)
  bytesArrayDecode o "decode/bytes-unaligned/2000"  100 (by decide) 2000 (by decide)

  -- `.array .string` — the second dynamic-element arm
  encodeRow o "encode/string-array/500" (.array .string) fun _ =>
    arrayOf text 500 (by decide)

  -- the four fused static-element arms
  staticArrayRows o "encode/uint256-array/1000" "decode/uint256-array/1000"
    (.uint 32) wideWord 1000 (by decide)
  staticArrayRows o "encode/int256-array/1000" "decode/int256-array/1000"
    (.int 32) wideInt 1000 (by decide)
  staticArrayRows o "encode/bool-array/2000" "decode/bool-array/2000"
    .bool true 2000 (by decide)
  staticArrayRows o "encode/bytes32-array/2000" "decode/bytes32-array/2000"
    (.bytesN 32) word32 2000 (by decide)

  -- `address[]` has no fused arm: its payload once cost two orders of
  -- magnitude more than the match one would remove.  This is the row that
  -- says when that stops being true.
  staticArrayRows o "encode/address-array/500" "decode/address-array/500"
    .address wideAddress 500 (by decide)

  -- the general paths: static through `emitVal`, dynamic through `emitAnyRun`
  encodeRow o "encode/static-tuple" staticTy fun _ => staticVal
  decodeRow o "decode/static-tuple" staticTy fun _ => encode staticTy staticVal
  encodeRow o "encode/nest/50"  (nest 50)  fun _ => nestVal 50
  encodeRow o "encode/nest/200" (nest 200) fun _ => nestVal 200
