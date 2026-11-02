all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

clean:
	git clean -fdX

.PHONY: all clean
