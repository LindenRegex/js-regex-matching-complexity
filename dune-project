(lang dune 3.21)

(name jsregexoptp)

(generate_opam_files false)

(using rocq 0.11)

(authors "Victor Deng" "Aurèle Barrière" "Clément Pit-Claudel")

(package
 (name jsregexoptp)
 (synopsis "Complexity results about JavaScript regex matching")
 (depends
  (rocq-prover (= 9.1.0))
  (linden (= "dev"))))
