.PHONY: default all clean clean-all coq-finproof-base tools proofs newproofs

all: default

coq-finproof-base: 
	make -C modules/coq-finproof-base

proofs: all
	make -C src/Proofs

newproofs: all proofs
	make -C src/NewProofs

default: CoqMakefile
	make -f CoqMakefile

tools: CoqMakefile-tools
	make -f CoqMakefile.Tools
	ocamlbuild ClassGeneratorTogetherSol.native -use-ocamlfind -package io-system	
	ocamlbuild specFileGenerator.native -use-ocamlfind -package io-system
	ocamlbuild CommonStateProofsGenerator.native -use-ocamlfind -package io-system
	ocamlbuild generator.native -use-ocamlfind -package io-system
	ocamlbuild functionsFileGenerator.native -use-ocamlfind -package io-system

deps: clone-deps build-deps

clean: CoqMakefile
	make -f CoqMakefile clean
clean-all: clean
	-rm -rf .deps
	-rm -rf CoqMakefile
	-rm -rf CoqMakefile.conf
	-rm -r .*.aux */.*.aux
	-rm -f */*.glob
	-rm -f */*.vo
	-rm -f */*/*.vo
	-rm -f */*.vio
	-rm -f */*/*.vio
	-rm -f */*/*.glob

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

CoqMakefile-tools: _CoqProject.Tools
	coq_makefile -f _CoqProject.Tools -o CoqMakefile.Tools

clone-deps:
	-mkdir -p .deps
	-git clone git@vcs.modus-ponens.com:ton/coq-ext-lib.git --depth 1 --branch v0.10.2 .deps/coq-ext-lib
build-deps:
	make -C .deps/coq-ext-lib
clean-deps:
	make -C .deps/coq-ext-lib
