We thank the reviewers for their feedback, and will address all minor suggestions in the revision.

# Key points

> **A:** The paper fails to clearly convey what makes Applicative functors (strictly) weaker than Selective functors.

The `Applicative` operator `<*>` composes *independent computations*. The `Selective` interface adds the operator `select` to compose *dependent computations*, where **a computation can depend on the value produced by a previous computation**. This makes the `Selective` interface strictly more powerful. While we already state this at the beginning of S2 (line 137), we'll make this key insight more prominent in the revision.

> **A:** I was not entirely convinced about the interface, laws or the relationship with Applicative Functors. [...] Is there any type constructor f, which is Applicative but not Selective?

The answer is "No", as we say in line 192.

> **A:** this is odd because the authors argue that Applicative < Selective < Monad. Thus I would have expected some things to be Applicative, but not Selective.

The relationship between `Applicative` and `Selective` is different from the relationship between `Applicative` and `Monad`. Not every `Applicative` is a `Monad`, but every `Applicative` is a `Selective`. The subclass relationship `Applicative < Selective` is justified by the extra method `select` in `Selective`. While `select = selectA` is a valid implementation of `select`, **it is not the only possible implementation**, as demonstrated by `Selective` instances `Over` and `Under`: indeed, `Over` uses `select = selectA`, but `Under` doesn't.

One should interpret the hierarchy as method set inclusion `{<*>}` < `{<*>, select}` < `{<*>, select, >>=}`. Different applications require different sets of methods. For example, **Haxl requires all three**: `<*>` gives parallelism, `select` gives speculative execution, and `>>=` gives arbitrary dynamic effects.

We'll clarify this subtle point in the revision.

> **B:** In the implementation of `write` you evaluate the value to get the associated effects. It's clear that this is needed for the static analysis, but I worry that it will lead to quadratic or exponential blowup in the simulation.

Thank you for pointing out this performance problem! Indeed, the implementation of `write` presented in S5.3 causes an exponential blowup when simulating `write` chains, such as `write k0 (write k1 (write k2 (read k3)))`, performing `read k3` 2^3=8 times.

Fortunately, we can fix the problem as follows. We simplify the implementation of `write` in line 919 to:

```
write k fv = liftSelect (Write k fv id)
```

Static analysis (`getProgramEffects` below) is then performed via the natural transformation `toOver` that records effects in `fv` plus the write effect `Write k` itself:

```
toOver :: RW a -> Over [RW ()] a
toOver (Read  k _   ) = Over [Read k (const ())]
toOver (Write k fv _) = runSelect toOver fv *> Over [Write k fv (const ())]

getProgramEffects :: Program a -> [RW ()]
getProgramEffects = getOver . runSelect toOver
```

The natural transformation `toState` needs no changes. This fix not only improves performance, but also makes the implementation more consistent. We'll happily make the fix in the revision.

> **C:** At least, I would like to see a concrete instance that is Selective but (at least believed) not (to be) ArrowChoice. [...] I do not believe that we "could use arrows to solve our static analysis and speculative execution examples"

A `Selective` instance cannot be an instance of `ArrowChoice` because of kind mismatch, so the first comment is unclear. Below is an example of doing static analysis of `ArrowChoice` in the spirit of S5:

```
newtype FreeArrowChoice f a b = FreeArrowChoice {
    runFreeArrowChoice :: forall arr. ArrowChoice arr =>
        (forall i o. f i o -> arr i o) -> arr a b }

newtype ConstArrow m a b = ConstArrow { getConstArrow :: m }

foldArrowChoice :: Monoid m => (forall i o. f i o -> m) -> FreeArrowChoice f a b -> m
foldArrowChoice t arr = getConstArrow $ runFreeArrowChoice arr (ConstArrow . t)
```

`ConstArrow` plays the same role as the `Const` functor: we convert the "base arrow" `f` to `ConstArrow` using the function `t`, and statically accumulate the resulting monoidal effect labels.

To execute a `FreeArrowChoice` we can use the `Kleisli` arrow. We'll provide the full implementation as supplementary material and link to it.

# Details

> **A:** Wouldn't there also be quite a few advantages of having selective in the Applicative instance?

One advantage is that adding `select` to `Applicative` avoids breaking the existing `Applicative => Monad` hierarchy. However, that would still break some code, because `select` would clash with existing definitions with the same name. We can elaborate on this point in the revision.

> **A:** Laws: The associativity law does indeed look rather ugly. I do wonder if an alternative interface would have not indeed be a better option.

The `biselect` method (S6.2) has a simpler associativity law, but is more complex in other aspects. While future implementations of selective functors may use `biselect`, we believe that `select` is more appropriate for introducing the concept of selective functors to the FP community.

> **B:** You write "parametricity dictates that, when given a `Left a`, we must execute the effects in `f (a -> b)`". It should be pointed out that this is only true if you are required to produce a `b`.

> **B:** [l:439] Validation does in fact satisfy both the pure Left and pure Right laws

Indeed! We'll fix both issues.

> **C:** Maybe, I have missed some descriptions, but the rigidness is the key insight for Section 5, the discussions about typical reasons for a selective functor to be not rigid would strengthen the paper.

> **C:** It is hard to understand the program presented here [in Fig. 6]

We agree and will address these suggestions.

> **C:** "Interestingly, adding the ability to branch on infinite number of cases makes selective functors equivalent to a monad" -- Is it really true? How can we perform such a branching for a function for example without breaking parametricity?

Daniel Peebles pointed out the following variation of `branch`, which is `>>=` in disguise:

```
branch :: f (Sigma h) -> (forall a. h a -> f (a -> b)) -> f b
```

`Sigma h` is a "tagged union" with generalised "tags" `h`, which can in particular be functions. We'll provide the full implementation as supplementary material.
