# ICFP 2019 Artefact Evaluation submission

This image contains a snapshot of the software packages related to the paper
"Selective Applicative Functors" and all their dependencies.

## Running the image

To run it interactively use the command: `docker run -it geo2a/selective-icfp19`.
You will find yourself in the directory `/home/coq`.

The Haskell package contains an comprehensive suite of QuickCheck properties and
working examples, and is the most informative part of the artefact. We recommend
taking a look at it first.

## Haskell implementation

Change into the Haskell directory:

```
cd ~/selective-haskell
```

And run tests with `stack`:

```
stack test
```

Then you may take a look at the code and documentation in the top-level module
`src/Control/Selective.hs`, which provides the `Selective` type class and
auxiliary combinators. The free construction for rigid selective functors can be
found in `src/Control/Selective/Free/Rigid.hs`. Another free construction for
general selective functors is also available in `src/Control/Selective/Free.hs`.

Also see the Hackage package: http://hackage.haskell.org/package/selective.

## Check Coq proofs

To access the Coq development, execute the following command:

```
cd ~/selective-coq
```

To typecheck all the Coq files in the development and verify the Coq proofs of
several Selective instances being lawful, execute:

```
make
```

You may take a look at the simple instances in the files `src/Data/Over.v`,
`src/Data/Under.v` and `src/Data/Validation.v`.

## OCaml implementation

Change into the OCaml directory:

```
cd ~/selective-ocaml
```

The file `src/selective_intf.ml` contains the signature of the module definition
`Selective.S` module, which provides the interface comprising all the Selective
combinators.

You can take a look at an example S-expression parser, List instance, and
the Task abstraction from section 3.2 in the `examples/` directory.

Also see the OPAM package: https://opam.ocaml.org/packages/selective/.
