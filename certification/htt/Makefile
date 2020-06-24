all: default doc
default: Makefile.coq
	make -f Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq

install: Makefile.coq
	make -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: coq clean install doc
