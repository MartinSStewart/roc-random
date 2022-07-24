interface Random
    exposes [
        initialSeed,
        i16,
        i32,
        #u8,
        #u16,
        #u32,
        generate,
        finish,
        Seed,
        Generator,
        generate
    ]
    imports []

Generator a := Seed -> { value: a, seed: Seed }

Seed := U64

initialSeed : U64 -> Seed
initialSeed = \seed -> @Seed seed |> nextSeed

i16 : I16, I16, (I16 -> Generator a) -> Generator a
i16 = \low, high, func ->
    @Generator
        \(@Seed seed) ->
            range = high - low |> Num.toI64
            value = permute (@Seed seed) |> mapToI16 |> Num.toI64 |> Num.sub (Num.toI64 Num.minI16) |> modWithNonzero range
            generate (nextSeed (@Seed seed)) (func (Num.intCast seed % (high - low) + low))

i32 : I32, I32, (I32 -> Generator a) -> Generator a
i32 = \low, high, func ->
    @Generator
        \(@Seed seed) ->
            range = high - low |> Num.toI64
            value = permute (@Seed seed) |> mapToI32 |> Num.toI64 |> Num.sub (Num.toI64 Num.minI32) |> modWithNonzero range
            generate (nextSeed (@Seed seed)) (func (Num.intCast seed % (high - low) + low))

#u8 : U8, U8, (U8 -> Generator a) -> Generator a
#u8 = \low, high, func ->
#    @Generator
#        \(@Seed seed) ->
#            generate (nextSeed (@Seed seed)) (func (betweenUnsigned high low))

#u16 : U16, U16, (U16 -> Generator a) -> Generator a
#u16 = \low, high, func ->
#    @Generator
#        \(@Seed seed) ->
#            generate (nextSeed (@Seed seed)) (func (betweenUnsigned high low))

#u32 : U32, U32, (U32 -> Generator a) -> Generator a
#u32 = \low, high, func ->
#    @Generator
#        \(@Seed seed) ->
#            generate (nextSeed (@Seed seed)) (func (betweenUnsigned high low))

list : Nat, Generator a, (List a -> Generator a) -> Generator a
list = \length, listGenerator, func ->
    @Generator
        \seed ->
            newState2 : { value: List a, seed: Seed }
            newState2 =
                List.repeat {} length
                |> List.walk
                    { value: [], seed: seed }
                    (\state, {} ->
                        newState = generate state.seed listGenerator
                        { value: List.append state.value newState.value, seed: newState.seed }
                    )

            generate (nextSeed newState2.seed) (func newState2.value)

generate : Seed, Generator a -> { value: a, seed: Seed }
generate = \seed, @Generator generator ->
    generator seed

finish : a -> Generator a
finish = \value ->
    @Generator \seed -> { value: value, seed : seed }

# Example user code

#point : Generator { x: U32, y: U32 }
#point =
#    x <- u32 0 9
#    y <- u32 10 19
#    finish { x, y }

#run =
#    generate (initialSeed 123) point

#### Helpers for the above constructors

betweenUnsigned = \x, y ->
    Pair minimum maximum = sort x y
    range = maximum - minimum + 1
    \seed ->
        # TODO: Analyze this. The mod-ing might be biased towards a smaller offset!
        value = minimum + modWithNonzero (permute seed) range
        { value, seed: nextSeed seed }

sort = \x, y ->
    if x < y then
        Pair x y
    else
        Pair y x

mapToI8 : U64 -> I8
mapToI8 = \x ->
    x2 = Num.toU8 x
    middle = Num.toU8 Num.maxI8
    if x2 <= middle then
        Num.minI8 + Num.toI8 x
    else
        Num.toI8 (x2 - middle - 1)

mapToI16 : U64 -> I16
mapToI16 = \x ->
    x2 = Num.toU16 x
    middle = Num.toU16 Num.maxI16
    if x2 <= middle then
        Num.minI16 + Num.toI16 x
    else
        Num.toI16 (x2 - middle - 1)

mapToI32 : U64 -> I32
mapToI32 = \x ->
    x2 = Num.toU32 x
    middle = Num.toU32 Num.maxI32
    if x2 <= middle then
        Num.minI32 + Num.toI32 x
    else
        Num.toI32 (x2 - middle - 1)

# Warning: y must never equal 0. The `123` fallback is nonsense for typechecking only.
modWithNonzero = \x, y -> x % y

#### PCG algorithms, constants, and wrappers
#
# Based on this paper: https://www.pcg-random.org/pdf/hmc-cs-2014-0905.pdf
# Based on this C++ header: https://github.com/imneme/pcg-c/blob/master/include/pcg_variants.h
# Abbreviations:
#     M = Multiplication (see section 6.3.4 on page 45 in the paper)
#     PCG = Permuted Congruential Generator
#     RXS = Random XorShift (see section 5.5.1 on page 36 in the paper)
#     XS = XorShift (see section 5.5 on page 34 in the paper)

# See `RXS M XS` constants (line 168?)
# and `_DEFAULT_` constants (line 276?)
# in the PCG C++ header (see link above).
permuteMultiplier = 12_605_985_483_714_917_081
permuteRandomXorShift = 59
permuteRandomXorShiftIncrement = 5
permuteXorShift = 43
updateIncrement = 1_442_695_040_888_963_407
updateMultiplier = 6_364_136_223_846_793_005

# See `pcg_output_rxs_m_xs_8_8` (on line 170?) in the PCG C++ header (see link above).
permute = \@Seed s ->
    pcgRxsMXs s

# See section 6.3.4 on page 45 in the PCG paper (see link above).
pcgRxsMXs = \state ->
    partial = Num.mulWrap permuteMultiplier (
        Num.bitwiseXor state (
            Num.shiftRightZfBy (
                Num.addWrap (Num.shiftRightZfBy permuteRandomXorShift state) permuteRandomXorShiftIncrement
            ) state
        ))
    Num.bitwiseXor partial (Num.shiftRightZfBy permuteXorShift partial)

# See section 4.1 on page 20 in the PCG paper (see link above).
pcgStep = \state, multiplier, increment ->
    Num.addWrap (Num.mulWrap state multiplier) increment

# See `pcg_oneseq_8_step_r` (line 409?) in the PCG C++ header (see link above).
nextSeed : Seed -> Seed
nextSeed = \@Seed seed ->
    @Seed (pcgStep seed updateMultiplier updateIncrement)