FROM ocaml/opam2:debian-9

LABEL maintainer="Reuben N. S. Rowe (reuben.rowe@rhul.ac.uk)"

ARG DEBIAN_FRONTEND=noninteractive

ENV TERM linux

USER root

RUN apt-get update && apt-get install -y --no-install-recommends apt-utils
RUN apt-get update && apt-get install -y --no-install-recommends \
      autoconf \
      libpcre3-dev \
      m4 \
      default-jdk \
      pkg-config \
      software-properties-common \
      z3 \
  && sudo rm -rf /var/lib/apt/lists/*
RUN (echo "deb http://dl.bintray.com/sbt/debian /" | tee -a /etc/apt/sources.list.d/sbt.list) \
  && (curl -sL "http://keyserver.ubuntu.com/pks/lookup?op=get&search=0x2EE0EA64E40A89B84B2DF73499E82A75642AC823" | apt-key add) \
  && apt-get update \
  && apt-get install -y --no-install-recommends \
       sbt
RUN (curl -s https://www.lrde.epita.fr/repo/debian.gpg | apt-key add -) \
  && echo 'deb http://www.lrde.epita.fr/repo/debian/ stable/' >> /etc/apt/sources.list \
  && apt-get update \
  && apt-get install -y --no-install-recommends \
       spot \
       libspot-dev

USER opam

RUN  opam repo -a add ocaml.org https://opam.ocaml.org/ \
  && opam update \
  && opam install -y dune hashset hashcons pcre mparser ocamlgraph

WORKDIR /home/opam

RUN git clone https://github.com/ngorogiannis/cyclist.git \
  && cd cyclist \
  && eval `opam config env` \
  && dune build

ENV PATH /home/opam/cyclist/_build/install/default/bin:$PATH

RUN git clone https://github.com/TyGuS/suslik.git \
  && cd suslik \
  && sbt assembly

ENV PATH /home/opam/suslik:$PATH