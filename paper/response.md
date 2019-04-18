We thank the reviewers for their comments and suggestions. We will address all minor suggestions in the revision.

# Key points

> **A:** The paper fails to clearly convey what makes Applicative functors (strictly) weaker than Selective functors.

In `Applicative`, the operator `<*>` composes *independent* computations, but in `Selective`, the additional operator `select` composes *dependent* computations. The fact that **a computation can depend on the value produced by a previous computation** is what makes the `Selective` interface strictly more powerful. While we already state this at the beginning of S2 (line 137), we will make this key insight more prominent in the revision.

> **A:** The theoretical treatment doesn't feel very strong to me. [...] In the end I was not entirely convinced about the interface, laws or the relationship with Applicative Functors. [...] Is there any type constructor f, which is Applicative but not Selective?

No. We say this in line 192: "Any Applicative instance can thus be given a Selective instance".

> **A:** this is odd because the authors argue that Applicative < Selective < Monad. Thus I would have expected some things to be Applicative, but not Selective.

`Selective` requires one extra method `select` to be implemented compared to the `Applicative` type class, hence the subclass relation. Note also that while `select = selectA` is a perfectly valid implementation of `select`, **it is not the only one**, as demonstrated by `Selective` instances `Over` and `Under`: indeed, `Over` uses `select = selectA`, but `Under` does not.

> **B:** [l:921] In the implementation of write you evaluate the value to get the associated effects. It's clear that this is needed for the static analysis, but I worry that it will lead to quadratic or exponential blowup in the simulation. Is there an argument to be made that this is not the case? (**Please address this in rebuttal**)

**TODO: Andrey & Georgy**

> **C:** At least, I would like to see a concrete instance that is Selective but (at least believed) not (to be) ArrowChoice.

Such an instance does not exist... **TODO: Andrey**

> **C:** [...] so I do not believe that we "could use arrows to solve our static analysis and speculative execution examples"

We hope the above argument will convince reviewer that ArrowChoice is indeed a viable alternative for selective functors.

# Details

> **A:** [...] Now that I read more on the paper I see that such an alternative is briefly discussed in Section 6. Wouldn't there also be quite a few advantages of having selective in the Applicative instance?

One advantage we see is that adding `select` to `Applicative` makes it possible to avoid breaking the existing `Applicative => Monad` type class hierarchy. Note however that it would still be a breaking change because `select` would clash with existing definitions with the same name. We can elaborate on this point in the revision.

> **A:** Laws: The associativity law does indeed look rather ugly. I do wonder if an alternative interface would have not indeed be a better option.

The alternative definition based on `biselect` (S6.2) does give a much nicer associativity law but at the cost of complexity. While future implementations of selective functors may indeed be based on `biselect`, we believe that `select` is a more appropriate choice for introducing the concept of selective functors to the functional programming community.

> **B:** You write "parametricity dictates that, when given a `Left a`, we must execute the effects in `f (a -> b)`". It should be pointed out that this is only true if you are required to produce a `b`. For instance, the `Under` functor never executes the second argument.

Good point, we will add a note on this.

> **B:** [l:439] Validation does in fact satisfy both the pure Left and pure Right laws

Indeed! We will remove "and `Validation`" from this line.

> **C:** Maybe, I have missed some descriptions, but the rigidness is the key insight for Section 5, the discussions about typical reasons for a selective functor to be not rigid would strengthen the paper.

We agree, and will address this in a revision.

> **C:** It is hard to understand the program presented here [in Fig. 6] especially for ones who do not Haxl like me.

We will add an explanation in the revision.


> **C:** "Interestingly, adding the ability to branch on infinite number of cases makes selective functors equivalent to a monad" -- Is it really true? How can we perform such a branching for a function for example without breaking parametricity?

**TODO: Andrey**
