You'll need a recent OCaml setup, with ocamlbuild and menhir both installed.

The easiest way to do this is to use OPAM. Install OPAM following the
instructions at:

    https://opam.ocaml.org/doc/Install.html

then install a recent version of OCaml:

    opam switch 4.03.0
    eval `opam config env`

then compile MLsub (in the directory in which you cloned/unpacked it):

    opam install ocamlbuild
    opam install menhir
    make

To test, try passing the `sample_list.ml` file:

    ./main.byte sample_list.ml

Compare the output to the types inferred by OCaml:

    ocamlc -i sample_list.ml
