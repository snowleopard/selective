# Selective Applicative Functors: ICFP 2019 Artefact

This Docker image contains a snapshot of the software packages related to the
paper "Selective Applicative Functors" and all their dependencies.

The image and this description are also available at Docker Hub:

https://hub.docker.com/r/geo2a/selective-icfp19

## Running the image

Unzip the archive, obtaining file `geo2a-selective-icfp19.tar`

To load the image into Docker use the command: `docker load --input geo2a-selective-icfp19.tar`

To run it interactively use the command: `docker run -it geo2a/selective-icfp19`.

You will find yourself in the directory `/home/coq`.

The Haskell package contains a comprehensive suite of QuickCheck properties as
well as working examples from the paper, and is the most informative part of the
artefact. We recommend taking a look at it first.

## Haskell implementation

Change into the Haskell implementation directory:

```
cd ~/selective-haskell
```

And run tests with `stack`:

```
stack test
```

Then you might want to browse the code and documentation in the top-level module
`src/Control/Selective.hs`, which provides the `Selective` type class and
selective combinators. The free construction for rigid selective functors can be
found in `src/Control/Selective/Free/Rigid.hs`. Another free construction for
general selective functors is available in `src/Control/Selective/Free.hs`.

This package is also available on Hackage: http://hackage.haskell.org/package/selective-0.2.

## Coq proofs

We also provide a formalisation of selective functors in Coq, along with proofs
of correctness of several `Selective` instances.

To access Coq proofs, execute the following command:

```
cd ~/selective-coq
```

To typecheck all the Coq files in the development and verify the Coq proofs of
several Selective instances being lawful, execute:

```
make
```

Start by taking a look at the simple proofs in files `src/Data/Over.v`,
`src/Data/Under.v` and `src/Data/Validation.v`.

## OCaml implementation

We also provide an implementation of selective functors in OCaml. To access it,
change to the corresponding directory:

```
cd ~/selective-ocaml
```

You can build and test the project using the Dune build system:

```
dune build
dune runtest
```

Note that lack of output means all tests have passed.

The file `src/selective_intf.ml` contains the signature of the definition of the
main module `Selective.S`, which provides the interface comprising all the
selective combinators.

You can take a look at an example S-expression parser, a `List` instance, and
the `Task` abstraction from section 3.2 in the `example` directory.

This package is available on OPAM: https://opam.ocaml.org/packages/selective/selective.0.1.0/.
