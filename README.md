<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# coq-http

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/liyishuai/coq-http/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/liyishuai/coq-http/actions/workflows/docker-action.yml




HTTP specification in Coq, testable and verifiable

## Meta

- Author(s):
  - Yishuai Li [<img src="https://zenodo.org/static/images/orcid.svg" height="14px" alt="ORCID logo" />](https://orcid.org/0000-0002-5728-5903)
  - Li-yao Xia [<img src="https://zenodo.org/static/images/orcid.svg" height="14px" alt="ORCID logo" />](https://orcid.org/0000-0003-2673-4400)
  - Yao Li [<img src="https://zenodo.org/static/images/orcid.svg" height="14px" alt="ORCID logo" />](https://orcid.org/0000-0001-8720-883X)
  - Azzam Althagafi
  - Benjamin C. Pierce [<img src="https://zenodo.org/static/images/orcid.svg" height="14px" alt="ORCID logo" />](https://orcid.org/0000-0001-7839-1636)
- License: [Mozilla Public License 2.0](LICENSE)
- Compatible Rocq/Coq versions: 8.14 or later
- Additional dependencies:
  - [OCamlbuild](https://github.com/ocaml/ocamlbuild)
  - [QuickChick](https://github.com/QuickChick/QuickChick/)
  - [AsyncTest](https://github.com/liyishuai/coq-async-test)
- Rocq/Coq namespace: `HTTP`
- Related publication(s):
  - [From C to Interaction Trees: Specifying, Verifying, and Testing a Networked Server](https://doi.org/10.1145/3293880.3294106) doi:[10.1145/3293880.3294106](https://doi.org/10.1145/3293880.3294106)
  - [Model-Based Testing of Networked Applications](https://doi.org/10.1145/3460319.3464798) doi:[10.1145/3460319.3464798](https://doi.org/10.1145/3460319.3464798)
  - [Verifying an HTTP Key-Value Server with Interaction Trees and VST](https://drops.dagstuhl.de/opus/volltexte/2021/13927) doi:[10.4230/LIPIcs.ITP.2021.32](https://doi.org/10.4230/LIPIcs.ITP.2021.32)
  - [Testing by Dualization](https://repository.upenn.edu/handle/20.500.14332/32046) doi:[20.500.14332/32046](https://doi.org/20.500.14332/32046)

## Building and installation instructions

The easiest way to install the latest released version of coq-http
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-http
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/liyishuai/coq-http.git
cd coq-http
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



