COQMAKEFILE?=Makefile.coq
EXE?=TestHttp.native
INSTALLDIR?=$(shell opam var bin)

all: $(COQMAKEFILE)
	@+$(MAKE) -f $^ $@
	$(MAKE) -C extract

test: all
	$(MAKE) -C $@

install: $(COQMAKEFILE)
	@+$(MAKE) -f $^ $@
	install extract/$(EXE) $(INSTALLDIR)

uninstall: $(COQMAKEFILE)
	@+$(MAKE) -f $^ $@
	@rm -f $(INSTALLDIR)/$(EXE)

clean: $(COQMAKEFILE)
	@+$(MAKE) -f $^ cleanall
	@rm -f $^ $^.conf */*~
	$(MAKE) -C extract $@

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

force _CoqProject Makefile: ;

%: $(COQMAKEFILE) force
	@+$(MAKE) -f $< $@

.PHONY: all clean force test
