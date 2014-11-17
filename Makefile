.PHONY: all
all:
	ocamlbuild -cflag -g -lflag -g -use-menhir -yaccflag --explain main.byte

