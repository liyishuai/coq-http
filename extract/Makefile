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
	ocamlbuild -use-ocamlfind $@

stop:
	-if [ $$(which docker) ]; \
		then docker rm -f server; \
	fi

SERVER?=ysli/apache:proxy
PORT?=80
CPORT?=80

server: stop
	if [ $$(which docker) ]; \
		then docker pull $(SERVER) || true; \
		     docker run -d --name $@ -p $(PORT):$(CPORT) $(SERVER); \
		else echo Docker not found; \
		     exit 1; \
	fi

py:
	$(MAKE) server CPORT=8899 SERVER=abhinavsingh/proxy.py

hs:
	$(MAKE) server CPORT=31081 SERVER=ysli/http-proxy

bug%:
	$(MAKE) server SERVER=ysli/apache:$@

TIMEOUT?=0

test: TestHttp.native
	time timeout $(TIMEOUT) ./TestHttp.native 2> client.log

etag-test:
	curl -X PUT -d Fine localhost:$(PORT)/wat
	curl -v localhost:$(PORT)/wat
	curl -v -X PUT -H 'If-Match: "WAT"' -d 'Wat' localhost:$(PORT)/wat
	curl localhost:$(PORT)/wat
	curl -v -X DELETE -H 'If-Match: "WAT"' localhost:$(PORT)/wat
	curl localhost:$(PORT)/wat
	curl -v -X DELETE localhost:$(PORT)/wat
	curl -v -X PUT -H 'If-Match: "WAT"' -d 'NewWat' localhost:$(PORT)/wat
	curl localhost:$(PORT)/wat

proxy-test:
	curl -v wat -x localhost:$(PORT)
