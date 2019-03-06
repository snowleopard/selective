# Things to think about and try to squeeze into the paper

## Connections/applications

* Connections to linear logic: https://twitter.com/phadej/status/1102660761938284544

* Connections to lenses/traversable functors: https://twitter.com/andreymokhov/status/1102733512812232704

* Connections to probabilistic programming: http://mlg.eng.cam.ac.uk/pub/pdf/SciGhaGor15.pdf

* `Selective ZipList` and SIMT execution model: https://en.wikipedia.org/wiki/Single_instruction,_multiple_threads

  > to handle an IF-ELSE block where various threads of a processor execute
  > different paths, all threads must actually process both paths (as all threads
  > of a processor always execute in lock-step), but masking is used to disable
  > and enable the various threads as appropriate

* Connections to FRP: https://discuss.ocaml.org/t/an-intermediate-abstraction-between-applicatives-and-monads/3441/3

## Existing similar abstractions

* Evgenyi Permyakov's `Branching` type class: https://mail.haskell.org/pipermail/haskell-cafe/2012-July/102518.html

* Jeremy Yallop's `DynamicIdiom` type class: https://www.cl.cam.ac.uk/~jdy22/papers/dissertation.pdf
