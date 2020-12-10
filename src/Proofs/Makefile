.PHONY: default all clean clean-all

all:  default

default: CoqMakefile
	make -f CoqMakefile

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
