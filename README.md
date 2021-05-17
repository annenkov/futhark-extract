# Extracting Futhark code

A prototype implementation of code extraction from the Coq proof assistant targeting [Futhark](https://futhark-lang.org/)

Extraction machinery is provided by [MetaCoq](https://github.com/MetaCoq/metacoq/) and [ConCert](https://github.com/AU-COBRA/ConCert)

## Requirements

Requires Coq 8.11.2 to compile.
The easiest way to install Coq and the dependencies is through `opam`.
Read [here](https://coq.inria.fr/opam-using.html) about how to install and manage several versions of Coq.

If it's a fresh installation (or to a newly created switch/root), the following lines should be sufficient.

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin -j 4 add https://github.com/AU-COBRA/ConCert.git
```

Coq will be installed as one of the dependencies.
The process of building all the dependencies is quite time-consuming.

After the process of building dependencies is finished, just run `make` in the project root.
