# Build: make            (needs rocq 9.x + rocq-stdlib; uses rocq makefile)
#        make -j1 is the default to respect the machine's memory limits.
.PHONY: all clean
all: Makefile.rocq
	$(MAKE) -f Makefile.rocq -j1 all
Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq
clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean
	rm -f Makefile.rocq Makefile.rocq.conf
