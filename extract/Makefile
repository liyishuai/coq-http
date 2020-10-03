COQMAKEFILE?=Makefile.coq

all:
	$(RM) TestHttp.native
	$(MAKE) TestHttp.native

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

clean: $(COQMAKEFILE)
	@+$(MAKE) -f $^ cleanall
	@rm -f $^ $^.conf *~ *.ml*
	@ocamlbuild -clean

%.native:
	$(MAKE) -C ..
	$(MAKE) $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) $*.vo
	ocamlbuild -lib unix $@

stop:
	-if [ $$(which docker) ]; \
		then docker rm -f apache; \
	fi

APACHE?=ysli/apache

apache: stop
	if [ $$(which docker) ]; \
		then docker pull $(APACHE); \
		     docker run -d --name $@ -p $(PORT):80 $(APACHE); \
		else echo Docker not found; \
		     exit 1; \
	fi
