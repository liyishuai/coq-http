# coq-http

[![CircleCI][circleci-shield]][circleci-link]

[circleci-shield]: https://circleci.com/gh/liyishuai/coq-http.svg?style=svg
[circleci-link]:   https://circleci.com/gh/liyishuai/coq-http




HTTP specification in Coq, testable and verifiable

## Meta

- Author(s):
  - Yishuai Li
  - Yao Li
  - Azzam Althagafi
  - Li-yao Xia
  - Benjamin C. Pierce
- License: [GNU Affero General Public License v3.0 or later](LICENSE)
- Compatible Coq versions: 8.12 or later
- Additional dependencies:
  - [ITreeIO](https://github.com/Lysxia/coq-itree-io)
  - [Parsec](https://github.com/liyishuai/coq-parsec)
- Coq namespace: `HTTP`
- Related publication(s): none

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


