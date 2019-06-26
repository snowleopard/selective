# Things to think about and try to squeeze into the paper

## Connections/applications

* Build systems: Bazel is also a selective build system built on top of monadic build engine. Also, selective
  functors are relevant for shallow builds, when one can materialise the end target by providing a hash
  of an over-approximation of all possible dependencies.

* Connections to linear logic: https://twitter.com/phadej/status/1102660761938284544

* Connections to lenses/traversable functors: https://twitter.com/andreymokhov/status/1102733512812232704

* Connections to probabilistic programming: http://mlg.eng.cam.ac.uk/pub/pdf/SciGhaGor15.pdf.
  Also: https://www.quora.com/Can-you-give-some-exampes-of-Applicative-Functors-which-are-not-Monads.

* `Selective ZipList` and SIMT execution model: https://en.wikipedia.org/wiki/Single_instruction,_multiple_threads

  > to handle an IF-ELSE block where various threads of a processor execute
  > different paths, all threads must actually process both paths (as all threads
  > of a processor always execute in lock-step), but masking is used to disable
  > and enable the various threads as appropriate

* Connections to FRP: https://discuss.ocaml.org/t/an-intermediate-abstraction-between-applicatives-and-monads/3441/3

* ISA modelling: https://discuss.ocaml.org/t/an-intermediate-abstraction-between-applicatives-and-monads/3441/13

* Go's `select` statement: https://golangbot.com/select/, as suggested
  [in this Tweet](https://twitter.com/igstan/status/1102560124726583297).

## Existing similar abstractions

* Mirage's configuration DSL: https://docs.mirage.io/mirage/Mirage/index.html#val-if_impl

* The Typed Tagless Final paper has type class `BoolSYM` with method `if_`: http://okmij.org/ftp/tagless-final/course/lecture.pdf

  > > Good point! Typed Tagless Final deserves a discussion. Actually, I think our approach is an example of Typed
  > > Tagless Final: it’s a type class that gives you a (generalised version of) if statement, which you can
  > > mix&match with other capabilities! In fact, one of the examples in Typed Tagless Final is the type class
  > > BoolSYM with if_ method.

  > That’s exactly how I’m seeing it. Not to diminish the value of the work, but just to fit into the
  > mathematical framework, I would say that Selective is a signature of a particular language (structure)
  > and you’re applying the tagless-final approach to investigate its behavior and capabilities.

## Towards monadic bind

* @sclv: https://www.reddit.com/r/haskell/comments/axje88/selective_applicative_functors/ehw5x6l/

  > one could actually use `unsafePerformIO` to very unsafely actually get the binary representation
  > of the thunk, and "read it out" byte by byte, then based on branching on that, only enter actual
  > "proper" value. (i.e. since we're inside a machine, we actually only have finitary representations,
  > even if our data structures "look" infinite -- this is actually a form of "Skolem's Paradox"!).
  > (The idea of this bitwise testing thing is inspired by some of the tricks used in the classic
  > "Implicit Configurations" paper: http://okmij.org/ftp/Haskell/tr-15-04.pdf)
  > So in "real" terms, bind is by a series of dirty hacks, fully recoverable from select.


## Remaining bits and pieces from reviews: address if enough space

> You omit various performance improvements for clarity, but can you say something about the performance of the free selective functors. It looks like there would be a lot of book-keeping overhead from all the nested sum types.

> Now that I read more on the paper I see that such an alternative is briefly discussed in Section 6. Wouldn't there also be quite a few advantages of having selective in the Applicative instance?

* One advantage is that adding select to Applicative avoids breaking the Applicative => Monad hierarchy. However, that would still break some code, because select would clash with existing definitions with the same name. We can elaborate on this in the revision.
