# ICFP 2019 Artifact Evaluation submission

This image contains a snapshot of the software packages related to the paper "Selective Applicative Functors" and all their dependencies.

## Running the image

To run it interactively use the command: `docker run -it geo2a/selective-icfp19`.
You will find yourself in the directory `/home/coq`.

The Haskell package contains an extensive set of QuickCheck properties, thus it is
the most informative part of the artefact. We recommend taking a look at it first.

## Run Haskell tests

Change into the Haskell directory:

```
cd ~/selective-haskell
```

And run tests with `stack`:

```
stack test
```

Then you may take a look at the code in the top-level module
`src/Control/Selective.hs`, which provides the `Selective` typeclass and auxiliary
combinators.
The free construction for rigid selective functors can be found in the
`src/Control/Selective/Free/Rigid.hs'` file.

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

## Take a look at the OCaml implementation

Change into the OCaml directory:

```
cd ~/selective-ocaml
```

The file `src/selective_intf.ml` contains the signature of the module definition
`Selective.S` module, which provides the interface comprising all the Selective
combinators.

You may take a look at the example S-expression parser, List instance and
the Task Abstraction from
["Build Systems à la Carte"](https://dl.acm.org/citation.cfm?id=3236774)
([PDF](https://dl.acm.org/ft_gateway.cfm?id=3236774)) in the `examples/` directory.
