We thank the reviewers for their feedback, and will address all minor suggestions in the revision.

# Key points

> **A:** The paper fails to clearly convey what makes Applicative functors (strictly) weaker than Selective functors.

The `Applicative` operator `<*>` composes *independent computations*. The `Selective` interface introduces the additional operator `select` to compose *dependent computations*, where **a computation can depend on the value produced by a previous computation**. This is what makes the `Selective` interface strictly more powerful. While we already state this at the beginning of S2 (line 137), we will make this key insight more prominent in the revision.

> **A:** The theoretical treatment doesn't feel very strong to me. [...] In the end I was not entirely convinced about the interface, laws or the relationship with Applicative Functors. [...] Is there any type constructor f, which is Applicative but not Selective?

The answer is "No", as we say in line 192.

> **A:** this is odd because the authors argue that Applicative < Selective < Monad. Thus I would have expected some things to be Applicative, but not Selective.

The relationship between `Applicative` and `Selective` is different from the relationship between `Applicative` and `Monad`. Not every `Applicative` is a `Monad`, but every `Applicative` is a `Selective`. The subclass relationship `Applicative < Selective` is justified by the extra method `select` required by `Selective`. While `select = selectA` is a valid implementation of `select`, **it is not the only possible implementation**, as demonstrated by `Selective` instances `Over` and `Under`: indeed, `Over` uses `select = selectA`, but `Under` doesn't.

One should interpret the hierarchy as method set inclusion `{<*>}` < `{<*>, select}` < `{<*>, select, >>=}`. Different applications require different sets of methods. For example, Haxl requires all three: `<*>` gives parallelism, `select` gives speculative execution, and `>>=` gives arbitrary dynamic effects.

We will clarify this subtle point in the revision.

> **B:** [l:921] In the implementation of `write` you evaluate the value to get the associated effects. It's clear that this is needed for the static analysis, but I worry that it will lead to quadratic or exponential blowup in the simulation. Is there an argument to be made that this is not the case? (**Please address this in rebuttal**)

Thank you for pointing out a serious performance problem! Indeed, the implementation of `write` presented in S5.3 causes an exponential blowup when simulating `write` chains, such as `write k0 (write k1 (write k2 (read k3)))`, where `read k3` is performed 2^3 times.

Fortunately, the problem can be fixed as follows. We simplify the implementation of `write` in line 919 to:

```
write k fv = liftSelect (Write k fv id)
```

Static analysis (`getProgramEffects`) is then performed via the natural transformation `toOver` that records effects in `fv` plus the write effect `Write k` itself:

```
toOver :: RW a -> Over [RW ()] a
toOver (R k _   ) = Over [R k (const ())]
toOver (W k fv _) = runSelect toOver fv *> Over [W k fv (const ())]

getProgramEffects :: Program a -> [RW ()]
getProgramEffects = getOver . runSelect toOver
```

The natural transformation `toState` needs no changes. This fix not only improves performance, but also makes the implementation more consistent. We will happily implement it in the revision.

> **C:** At least, I would like to see a concrete instance that is Selective but (at least believed) not (to be) ArrowChoice. [...] I do not believe that we "could use arrows to solve our static analysis and speculative execution examples"

**TODO: Andrey**

We hope the above argument will convince reviewer that ArrowChoice is indeed a viable alternative for selective functors.

# Details

> **A:** [...] Now that I read more on the paper I see that such an alternative is briefly discussed in Section 6. Wouldn't there also be quite a few advantages of having selective in the Applicative instance?

One advantage is that adding `select` to `Applicative` makes it possible to avoid breaking the existing `Applicative => Monad` type class hierarchy. That would still be a breaking change however, because `select` would clash with existing definitions with the same name. We can elaborate on this point in the revision.

> **A:** Laws: The associativity law does indeed look rather ugly. I do wonder if an alternative interface would have not indeed be a better option.

The alternative definition based on `biselect` (S6.2) does give a much nicer associativity law but at the cost of complexity. While future implementations of selective functors may indeed be based on `biselect`, we believe that `select` is more appropriate for introducing selective functors to the ICFP community.

> **B:** You write "parametricity dictates that, when given a `Left a`, we must execute the effects in `f (a -> b)`". It should be pointed out that this is only true if you are required to produce a `b`. For instance, the `Under` functor never executes the second argument.
> **B:** [l:439] Validation does in fact satisfy both the pure Left and pure Right laws

Indeed! We will address both points.

> **C:** Maybe, I have missed some descriptions, but the rigidness is the key insight for Section 5, the discussions about typical reasons for a selective functor to be not rigid would strengthen the paper.
> **C:** It is hard to understand the program presented here [in Fig. 6] especially for ones who do not Haxl like me.

We agree, and will address these suggestions in the revision.

> **C:** "Interestingly, adding the ability to branch on infinite number of cases makes selective functors equivalent to a monad" -- Is it really true? How can we perform such a branching for a function for example without breaking parametricity?

The trick, suggested by Daniel Peebles, is to use the following variation of `branch`:

```
branch :: f (Sigma h) -> (forall a. h a -> f (a -> c)) -> f c
```

where `Sigma h` is a "tagged union" with generalised "tag" `h`, which can be infinite, and in particular be a function. We can include the actual implementation into supplementary material.
