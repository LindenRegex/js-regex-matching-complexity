(lang dune 3.14)

(name jsregexoptp)

(generate_opam_files false)

(using coq 0.8)

(authors "Victor Deng" "Aurèle Barrière" "Clément Pit-Claudel")

(package
 (name jsregexoptp)
 (synopsis "Proving that JavaScript regex matching is OptP-complete")
 (depends
  (coq (and (>= "8.18.0") (<= "8.19.2")))
  (linden (= "dev"))))
