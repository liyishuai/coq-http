<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# coq-http

[![CircleCI][circleci-shield]][circleci-link]

[circleci-shield]: https://circleci.com/gh/liyishuai/coq-http.svg?style=svg
[circleci-link]:   https://circleci.com/gh/liyishuai/coq-http




HTTP specification in Coq, testable and verifiable

## Meta

- Author(s):
  - Yishuai Li
  - Li-yao Xia
  - Yao Li
  - Azzam Althagafi
  - Benjamin C. Pierce
- License: [Mozilla Public License 2.0](LICENSE)
- Compatible Coq versions: 8.13 or later
- Additional dependencies:
  - [OCamlbuild](https://github.com/ocaml/ocamlbuild)
  - [ITreeIO](https://github.com/Lysxia/coq-itree-io)
  - [Parsec](https://github.com/liyishuai/coq-parsec)
  - [QuickChick](https://github.com/QuickChick/QuickChick/)
- Coq namespace: `HTTP`
- Related publication(s):
  - [From C to Interaction Trees:
    Specifying, Verifying, and Testing a Networked Server
](https://doi.org/10.1145/3293880.3294106) doi:[10.1145/3293880.3294106](https://doi.org/10.1145/3293880.3294106)
  - [Interaction Trees: Representing Recursive and Impure Programs in Coq
](https://doi.org/10.1145/3371119) doi:[10.1145/3371119](https://doi.org/10.1145/3371119)

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



