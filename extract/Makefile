COQMAKEFILE?=Makefile.coq

all:
	$(RM) TestHttp.native
	$(MAKE) TestHttp.native

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

clean: $(COQMAKEFILE)
	@+$(MAKE) -f $^ cleanall
	@rm -f $^ $^.conf *~ *.ml* *.log
	@ocamlbuild -clean

%.native:
	$(MAKE) $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) $*.vo
	ocamlbuild -lib unix $@

stop:
	-if [ $$(which docker) ]; \
		then docker rm -f server; \
	fi

SERVER?=ysli/apache
PORT?=8000

server: stop
	if [ $$(which docker) ]; \
		then docker pull $(SERVER); \
		     docker run -d --name $@ -p $(PORT):80 $(SERVER); \
		else echo Docker not found; \
		     exit 1; \
	fi

test: server
	./TestHttp.native 2> client.log

etag-test:
	curl -X PUT -d Fine localhost:8000/wat
	curl -v localhost:8000/wat
	curl -v -X PUT -H 'If-Match: "WAT"' -d 'Wat' localhost:8000/wat
	curl localhost:8000/wat
	curl -v -X DELETE -H 'If-Match: "WAT"' localhost:8000/wat 
	curl localhost:8000/wat
	curl -v -X DELETE localhost:8000/wat 
	curl -v -X PUT -H 'If-Match: "WAT"' -d 'NewWat' localhost:8000/wat
	curl localhost:8000/wat
