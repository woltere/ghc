## next (edit as necessary)

- `magicDict` has been renamed to `withDict` and is now defined in
  `GHC.Magic.Dict` instead of `GHC.Prim`. `withDict` now has the type:

  ```
  withDict :: forall {rr :: RuntimeRep} st dt (r :: TYPE rr). st -> (dt => r) -> r
  ```

  Unlike `magicDict`, `withDict` can be used without defining an
  intermediate data type. For example, the `withTypeable` function from the
  `Data.Typeable` module can now be defined as:

  ```
  withTypeable :: forall k (a :: k) rep (r :: TYPE rep). ()
               => TypeRep a -> (Typeable a => r) -> r
  withTypeable rep k = withDict @(TypeRep a) @(Typeable a) rep k
  ```

  Note that the explicit type applications are required, as the call to
  `withDict` would be ambiguous otherwise.

## 0.8.0 (edit as necessary)

- Change array access primops to use type with size maxing the element size:

   - `index{Int,Word}<N>Array# :: ByteArray# -> Int# -> {Int,Word}<N>#`
   - `indexWord8ArrayAs{Int,Word}<N># :: ByteArray# -> Int# -> {Int,Word}<N>#`
   - `read{Int,Word}<N>Array# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, {Int,Word}<N># #)`
   - `write{Int,Word}<N>Array# :: MutableByteArray# s -> Int# -> {Int,Word}<N># -> State# s -> State# s`
   - `readWord8ArrayAs{Int,Word}<N># :: MutableByteArray# s -> Int# -> State# s -> (# State# s, {Int,Word}<N># #)`
   - `writeWord8ArrayAs{Int,Word}<N># :: MutableByteArray# s -> Int# -> {Int,Word}<N># -> State# s -> State# s`

  This was already the for the 64-bit access primops, but not the smaller ones.

- Rename some numeric prim type conversion primops:

   - `extend{Int,Word}<N>#` -> `extend<N>To{Int,Word}#`
   - `narrow{Int,Word}<N>#` -> `intTo{Int,Word}<N>#`

- Add primops for atomic compare and swap for sizes other that wordsize:

   	casInt8Array# :: MutableByteArray# s -> Int# -> Int8# -> Int8# -> State# s -> (# State# s, Int8# #)
	casInt16Array# :: MutableByteArray# s -> Int# -> Int16# -> Int16# -> State# s -> (# State# s, Int16# #)
	casInt32Array# :: MutableByteArray# s -> Int# -> Int32# -> Int32# -> State# s -> (# State# s, Int32# #)
	casInt64Array# :: MutableByteArray# s -> Int# -> Int64# -> Int64# -> State# s -> (# State# s, Int64# #)
	atomicCasWord8Addr# :: Addr# -> Word8# -> Word8# -> State# s -> (# State# s, Word8# #)
	atomicCasWord16Addr# :: Addr# -> Word16# -> Word16# -> State# s -> (# State# s, Word16# #)
	atomicCasWord32Addr# :: Addr# -> Word32# -> Word32# -> State# s -> (# State# s, Word32# #)
	atomicCasWord64Addr# :: Addr# -> WORD64 -> WORD64 -> State# s -> (# State# s, WORD64 #)

## 0.7.0 (edit as necessary)

- Shipped with GHC 9.0.1

- Add known-key `cstringLength#` to `GHC.CString`. This is just the
  C function `strlen`, but a built-in rewrite rule allows GHC to
  compute the result at compile time when the argument is known.

- In order to support unicode better the following functions in `GHC.CString`
  gained UTF8 counterparts:

        unpackAppendCStringUtf8# :: Addr# -> [Char] -> [Char]
        unpackFoldrCStringUtf8# :: Addr# -> (Char -> a -> a) -> a -> a

- unpackFoldrCString* variants can now inline in phase [0].

  If the folding function is known this allows for unboxing of the
  Char argument resulting in much faster code.

- Renamed the singleton tuple `GHC.Tuple.Unit` to `GHC.Tuple.Solo`.

- Add primops for atomic exchange:

        atomicExchangeAddrAddr# :: Addr# -> Addr# -> State# s -> (# State# s, Addr# #)
        atomicExchangeWordAddr# :: Addr# -> Word# -> State# s -> (# State# s, Word# #)

- Add primops for atomic compare and swap at a given Addr#:

        atomicCasAddrAddr# :: Addr# -> Addr# -> Addr# -> State# s -> (# State# s, Addr# #)
        atomicCasWordAddr# :: Addr# -> Word# -> Word# -> State# s -> (# State# s, Word# #)

- Add an explicit fixity for `(~)` and `(~~)`:

        infix 4 ~, ~~

- Introduce `keepAlive#` to replace `touch#` in controlling object lifetime without
  the soundness issues of the latter (see
  [#17760](https://gitlab.haskell.org/ghc/ghc/-/issues/17760)).

## 0.6.1 (edit as necessary)

- Shipped with GHC 8.10.1

- Add primop for shrinking `SmallMutableArray#`
  to `GHC.Prim`:

        shrinkSmallMutableArray# :: SmallMutableArray# s a -> Int# -> State# s -> State# s

  Note that `resizeSmallMutableArray#` is not included as
  as primitive. It has been implemented in library space in
  `GHC.Exts`. See the release notes of `base`.

- Added to `GHC.Prim`:

        closureSize# :: a -> Int#

- Added to `GHC.Prim`:

        bitReverse# :: Word# -> Word#
        bitReverse8# :: Word# -> Word#
        bitReverse16# :: Word# -> Word#
        bitReverse32# :: Word# -> Word#
        bitReverse64# :: Word# -> Word#

  `bitReverse#` is a primop that, for a `Word` of 8, 16, 32 or 64 bits,
  reverses the order of its bits e.g. `0b110001` becomes `0b100011`.
  These primitives use optimized machine instructions when available.

- Add Int# multiplication primop:

      timesInt2# :: Int# -> Int# -> (# Int#, Int#, Int# #)

   `timesInt2#` computes the multiplication of its two parameters and returns a
   triple (isHighNeeded,high,low) where high and low are respectively the high
   and low bits of the double-word result. isHighNeeded is a cheap way to test
   if the high word is a sign-extension of the low word (isHighNeeded = 0#) or
   not (isHighNeeded = 1#).

## 0.6.0

- Shipped with GHC 8.8.1

- Added to `GHC.Prim`:

        traceBinaryEvent# :: Addr# -> Int# -> State# s -> State# s

## 0.5.3

- Shipped with GHC 8.6.1

- Added to `GHC.Prim`:

        addWordC# :: Word# -> Word# -> (# Word#, Int# #)

- `unpackClosure#` can now unpack any valid Haskell closure.
  Previously it returned empty pointer and non-pointer arrays
  for thunks.

- Add unaligned bytearray access primops (#4442)

         readWord8ArrayAsChar# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Char# #)
         readWord8ArrayAsAddr# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Addr# #)
         readWord8ArrayAsFloat# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Float# #)
         readWord8ArrayAsDouble# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Double# #)
         readWord8ArrayAsStablePtr# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, StablePtr# #)
         readWord8ArrayAsInt16# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Int16# #)
         readWord8ArrayAsInt32# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Int32# #)
         readWord8ArrayAsInt64# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Int64# #)
         readWord8ArrayAsInt# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Int# #)

         readWord8ArrayAsWord16# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Word16# #)
         readWord8ArrayAsWord32# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Word32# #)
         readWord8ArrayAsWord64# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Word64# #)
         readWord8ArrayAsWord# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, Word# #)

         writeWord8ArrayAsChar# :: MutableByteArray# s -> Int# -> Char# -> State# s -> State# s
         writeWord8ArrayAsAddr# :: MutableByteArray# s -> Int# -> Addr# -> State# s -> State# s
         writeWord8ArrayAsFloat# :: MutableByteArray# s -> Int# -> Float# -> State# s -> State# s
         writeWord8ArrayAsDouble# :: MutableByteArray# s -> Int# -> Double# -> State# s -> State# s
         writeWord8ArrayAsStablePtr# :: MutableByteArray# s -> Int# -> StablePtr# -> State# s -> State# s

         writeWord8ArrayAsInt16# :: MutableByteArray# s -> Int# -> Int16# -> State# s -> State# s
         writeWord8ArrayAsInt32# :: MutableByteArray# s -> Int# -> Int32# -> State# s -> State# s
         writeWord8ArrayAsInt64# :: MutableByteArray# s -> Int# -> Int64# -> State# s -> State# s
         writeWord8ArrayAsInt# :: MutableByteArray# s -> Int# -> Int# -> State# s -> State# s

         writeWord8ArrayAsWord16# :: MutableByteArray# s -> Int# -> Word16# -> State# s -> State# s
         writeWord8ArrayAsWord32# :: MutableByteArray# s -> Int# -> Word32# -> State# s -> State# s
         writeWord8ArrayAsWord64# :: MutableByteArray# s -> Int# -> Word64# -> State# s -> State# s
         writeWord8ArrayAsWord# :: MutableByteArray# s -> Int# -> Word# -> State# s -> State# s

## 0.5.2.0

- Shipped with GHC 8.4.1

- Added to `GHC.Prim`:

        compareByteArrays# :: ByteArray# -> Int# -> ByteArray# -> Int# -> Int# -> Int#

- Don't allocate a thunk for each unpacked UTF-8 character in `unpackCStringUtf8#`

## 0.5.1.1 *November 2017*

- Shipped with GHC 8.2.2

- Changed strictness properties of `catchRetry#` (#14171)

## 0.5.1.0 *July 2017*

- Shipped with GHC 8.2.1

- Added to `GHC.Prim`:

        fabsDouble# :: Double# -> Double#
        fabsFloat# :: Float# -> Float#
        isByteArrayPinned# :: ByteArray# -> Int#
        isMutableByteArrayPinned# :: MutableByteArray# s -> Int#
        anyToAddr# :: a -> State# (RealWorld) -> (# State# (RealWorld),Addr# #)

- New primitives for compact regions in `GHC.Prim`:

        Compact#
        compactNew#
        compactResize#
        compactContains#
        compactContainsAny#
        compactGetFirstBlock#
        compactGetNextBlock#
        compactAllocateBlock#
        compactFixupPointers#
        compactAdd#
        compactAddWithSharing#
        compactSize#

- Generalised `noDuplicate#` from

        noDuplicate# :: State# (RealWorld) -> State# (RealWorld)

    to

        noDuplicate# :: State# s -> State# s


## 0.5.0.0

- Shipped with GHC 8.0.1

- `GHC.Classes`: new `class IP (a :: Symbol) b | a -> b`

- `GHC.Prim`: changed type signatures from

        check# :: (State# RealWorld -> (# State# RealWorld, a #)) -> State# RealWorld -> (# State# RealWorld, () #)
        finalizeWeak# :: Weak# a -> State# RealWorld -> (# State# RealWorld, Int#, State# RealWorld -> (# State# RealWorld, () #) #)
        mkWeak# :: a -> b -> c -> State# RealWorld -> (# State# RealWorld, Weak# b #)

    to

        check# :: (State# RealWorld -> (# State# RealWorld, a #)) -> State# RealWorld -> State# RealWorld
        finalizeWeak# :: Weak# a -> State# RealWorld -> (# State# RealWorld, Int#, State# RealWorld -> (# State# RealWorld, b #) #)
        mkWeak# :: a -> b -> (State# RealWorld -> (# State# RealWorld, c #)) -> State# RealWorld -> (# State# RealWorld, Weak# b #)

- Removed from `GHC.Prim`:

        parAt# :: b -> a -> Int# -> Int# -> Int# -> Int# -> c -> Int#
        parAtAbs# :: a -> Int# -> Int# -> Int# -> Int# -> Int# -> b -> Int#
        parAtForNow# :: b -> a -> Int# -> Int# -> Int# -> Int# -> c -> Int#
        parAtRel# :: a -> Int# -> Int# -> Int# -> Int# -> Int# -> b -> Int#
        parGlobal# :: a -> Int# -> Int# -> Int# -> Int# -> b -> Int#
        parLocal# :: a -> Int# -> Int# -> Int# -> Int# -> b -> Int#

- Added to `GHC.Prim`:

        getSizeofMutableByteArray# :: MutableByteArray# d -> State# d -> (# State# d, Int# #)
        subWordC# :: Word# -> Word# -> (# Word#, Int# #)
        runRW# :: (State# RealWorld -> (# State# RealWorld, o #)) -> (# State# RealWorld, o #)

- Added to `GHC.Types`:

        data Module = Module TrName TrName
        data Nat
        data Symbol
        data TrName = TrNameS Addr# | TrNameD [Char]
        data TyCon = TyCon Word# Word# Module TrName
