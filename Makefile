COQMAKEFILE?=Makefile.coq

all: $(COQMAKEFILE)
	@+$(MAKE) -f $^ $@

clean: $(COQMAKEFILE)
	@+$(MAKE) -f $^ cleanall
	@rm -f $^ $^.conf */*~

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

force _CoqProject Makefile: ;

%: $(COQMAKEFILE) force
	@+$(MAKE) -f $< $@

.PHONY: all clean force
