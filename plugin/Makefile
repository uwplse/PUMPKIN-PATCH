all: plugin install

plugin: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

merlin:
	./merlin.sh

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

install:
	$(MAKE) -f Makefile.coq install

uninstall:
	$(MAKE) -f Makefile.coq uninstall

.PHONY: all plugin clean install uninstall
