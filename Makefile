.PHONY: all
all:
	ocamlbuild -no-hygiene -use-ocamlfind -r -cflag -bin-annot -cflag -g -lflag -g -pkg menhirLib -pkg sedlex -pkg str -use-menhir -yaccflag --explain -yaccflag --table main.byte


build-js:
	ocamlbuild -r -build-dir _build.js -use-ocamlfind -use-menhir \
	  -package js_of_ocaml -package js_of_ocaml.syntax \
          -syntax camlp4o webpage.byte

_build.js/webpage.byte: build-js


mlsub.js: _build.js/webpage.byte
	js_of_ocaml $^ -o $@
