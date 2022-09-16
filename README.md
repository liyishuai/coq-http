<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# coq-http

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/liyishuai/coq-http/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/liyishuai/coq-http/actions?query=workflow:"Docker%20CI"




HTTP specification in Coq, testable and verifiable

## Meta

- Author(s):
  - Yishuai Li
  - Li-yao Xia
  - Yao Li
  - Azzam Althagafi
  - Benjamin C. Pierce
- License: [Mozilla Public License 2.0](LICENSE)
- Compatible Coq versions: 8.14 or later
- Additional dependencies:
  - [OCamlbuild](https://github.com/ocaml/ocamlbuild)
  - [QuickChick](https://github.com/QuickChick/QuickChick/)
  - [AsyncTest](https://github.com/liyishuai/coq-async-test)
- Coq namespace: `HTTP`
- Related publication(s):
  - [From C to Interaction Trees: Specifying, Verifying, and Testing a Networked Server](https://doi.org/10.1145/3293880.3294106) doi:[10.1145/3293880.3294106](https://doi.org/10.1145/3293880.3294106)
  - [Model-Based Testing of Networked Applications](https://doi.org/10.1145/3460319.3464798) doi:[10.1145/3460319.3464798](https://doi.org/10.1145/3460319.3464798)
  - [Verifying an HTTP Key-Value Server with Interaction Trees and VST](https://drops.dagstuhl.de/opus/volltexte/2021/13927) doi:[10.4230/LIPIcs.ITP.2021.32](https://doi.org/10.4230/LIPIcs.ITP.2021.32)

## Building and installation instructions

The easiest way to install the latest released version of coq-http
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-http
```

To instead build and install manually, do:

``` shell
git clone https://github.com/liyishuai/coq-http.git
cd coq-http
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



