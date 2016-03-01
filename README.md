# PLT Redex implementation of ClojureTxTk

This repository contains a machine-executable implementation of the operational semantics of ClojureTxTk, using [PLT Redex][plt-redex].

[plt-redex]: https://redex.racket-lang.org/

It consists of the following files:
* `clj-base.rkt` defines Lb, the "base" language (based on Clojure)
* `clj-futures.rkt` defines Lf, the base language extended with support for futures (as in Clojure)
* `clj-tx.rkt` defines Lt, which is Lf extended with support for transactions (as in Clojure)
* `tx-futs.rkt` defines Ltf, which is Lt extended with support for transactional futures (not in Clojure)
* `map.rkt`: helper functions for maps
* `set.rkt`: helper functions for sets

TODO: more explanation here
