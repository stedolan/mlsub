.PHONY: all
all:
	ocamlbuild -r -cflag -g -lflag -g -use-menhir -yaccflag --explain main.byte


build-js:
	ocamlbuild -r -build-dir _build.js -use-ocamlfind -use-menhir \
	  -package js_of_ocaml -package js_of_ocaml.syntax \
          -syntax camlp4o webpage.byte

_build.js/webpage.byte: build-js


mlsub.js: _build.js/webpage.byte
	js_of_ocaml $^ -o $@
