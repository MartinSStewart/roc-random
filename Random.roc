interface Random
    exposes [
        initialSeed,
        i16,
        i32,
        u8,
        u16,
        u32,
        generate,
        finish,
        Seed,
        Generator,
        run
    ]
    imports []

Generator a := Seed -> { value: a, seed: Seed }

Seed := U32

initialSeed : U32 -> Seed
initialSeed = \seed -> @Seed seed

i16 : I16, I16, (I16 -> Generator a) -> Generator a
i16 = \low, high, func ->
    @Generator
        \(@Seed seed) ->
            generate (nextSeed (@Seed seed)) (func (Num.intCast seed % (high - low) + low))

i32 : I32, I32, (I32 -> Generator a) -> Generator a
i32 = \low, high, func ->
    @Generator
        \(@Seed seed) ->
            generate (nextSeed (@Seed seed)) (func (Num.intCast seed % (high - low) + low))

u8 : U8, U8, (U8 -> Generator a) -> Generator a
u8 = \low, high, func ->
    @Generator
        \(@Seed seed) ->
            generate (nextSeed (@Seed seed)) (func (Num.intCast seed % (high - low) + low))

u16 : U16, U16, (U16 -> Generator a) -> Generator a
u16 = \low, high, func ->
    @Generator
        \(@Seed seed) ->
            generate (nextSeed (@Seed seed)) (func (Num.intCast seed % (high - low) + low))

u32 : U32, U32, (U32 -> Generator a) -> Generator a
u32 = \low, high, func ->
    @Generator
        \(@Seed seed) ->
            generate (nextSeed (@Seed seed)) (func (seed % (high - low) + low))

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

nextSeed : Seed -> Seed
nextSeed = \@Seed seed ->
    @Seed (seed + 1)

finish : a -> Generator a
finish = \value ->
    @Generator \seed -> { value: value, seed : seed }

# Example user code

point : Generator { x: U32, y: U32 }
point =
    x <- u32 0 9
    y <- u32 10 19
    finish { x, y }

run =
    generate (initialSeed 123) point
