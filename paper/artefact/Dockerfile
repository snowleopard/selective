# Docker image prepared for ICFP'19 Artifact Evaluation.
#
# To build the image, run the following command in the directory containing
# this Dockerfile: `docker build -t geo2a/selective-icfp19 .`
#
# To run a container interactively:
# `docker run -it geo2a/selective-icfp19`
#
# We chose to use the Coq base image as a base because it includes all
# software required for building the Coq and OCaml parts of the artefact.
# We have augmented the image with the software required for the Haskell part.
FROM coqorg/coq:8.9

MAINTAINER Georgy Lukyanov

RUN sudo apt-get update
RUN sudo apt-get install -y wget m4
RUN curl -sSL https://get.haskellstack.org/ | sh

# Pull the OCaml sources from GitHub
RUN wget -O selective-ocaml.zip https://github.com/snowleopard/selective-ocaml/archive/0.1.0.zip && \
    unzip selective-ocaml.zip && rm selective-ocaml.zip && \
    cd selective-ocaml-0.1.0 && \
    opam install -y dune base stdio expect_test_helpers_kernel
RUN cd selective-ocaml-0.1.0 && eval $(opam env) && make test
RUN mv selective-ocaml-0.1.0 selective-ocaml

# Pull the Coq sources from GitHub
RUN wget -O selective-coq.zip https://github.com/tuura/selective-theory-coq/archive/v0.1.zip
RUN unzip selective-coq.zip && rm selective-coq.zip && mv selective-theory-coq-0.1 selective-coq

# Pull the Haskell sources from GitHub
RUN wget -O selective.zip https://github.com/snowleopard/selective/archive/v0.2.zip
RUN unzip selective.zip && rm selective.zip
RUN cd selective-0.2 && stack build && stack test
RUN mv selective-0.2 selective-haskell

RUN exit
