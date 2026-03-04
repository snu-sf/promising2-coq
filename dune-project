(lang dune 3.21)
(name rocq-promising2)
(using coq 0.8)

(source (github snu-sf/promising2-coq))
(license "MIT")
(authors
  "Sung-Hwan Lee" "Minki Cho" "Anton Podkopaev"
  "Soham Chakraborty" "Chung-Kil Hur" "Ori Lahav"
  "Viktor Vafeiadis")
(maintainers "yeji.han@sf.snu.ac.kr")

(package
 (name rocq-promising2)
 (synopsis "Rocq formalization of Promising 2.0: Global Optimizations in Relaxed Memory Concurrency")
 (depends
  (coq-core (>= 9.0))
  rocq-stdlib
  (coq-sflib (>= 2.1.0))
  (coq-paco (>= 4.2.3))
  (coq-promising-lib (>= 2.1.0))
  (dune (>= 3.21)))
 (maintainers "yeji.han@sf.snu.ac.kr"))
