.PHONY: all clean

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject: ;

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -rf doc/

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@
