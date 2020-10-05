COQMAKEFILE?=Makefile.coq
EXE?=TestHttp.native

all: $(COQMAKEFILE)
	@+$(MAKE) -f $^ $@
	$(MAKE) -C extract

install: $(COQMAKEFILE)
	@+$(MAKE) -f $^ $@
	install extract/$(EXE) `opam var bin`

uninstall: $(COQMAKEFILE)
	@+$(MAKE) -f $^ $@
	@rm -f `opam var bin`/$(EXE)

clean: $(COQMAKEFILE)
	@+$(MAKE) -f $^ cleanall
	@rm -f $^ $^.conf */*~

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

force _CoqProject Makefile: ;

%: $(COQMAKEFILE) force
	@+$(MAKE) -f $< $@

.PHONY: all clean force
