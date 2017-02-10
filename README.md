# Isabelle theory files for *Local Lexing*

**Author:** Steven Obua (steven.obua@gmail.com)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.290216.svg)](https://doi.org/10.5281/zenodo.290216)

These theory files are for use with Isabelle 2016. They accompany the paper [Local Lexing](http://www.proofpeer.net/papers/locallexing) and contain: 

* the definition of and semantics for local lexing  
* a high-level algorithm which implements local lexing
* a proof that the algorithm is correct with respect to the semantics of local lexing

Theories `CFG`, `LocalLexing` and `LLEarleyParsing` introduce the basic definitions, and theory `MainTheorems` states and proves the correctness result. All other theories contain supporting definitions and theorems needed to prove the correctness result.
