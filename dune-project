(lang dune 3.21)

(name js-regex-complexity)

(version 0.1)

(generate_opam_files false)

(using rocq 0.11)

(homepage "https://lin.den.re/")

(source
 (github LindenRegex/js-regex-matching-complexity))

(authors "Victor Deng" "Aurèle Barrière" "Clément Pit-Claudel")

(maintainers "Victor Deng")

(license MIT)

(package
 (name js-regex-complexity)
 (synopsis "Complexity results about JavaScript regex matching")
 (depends
  (rocq-prover (>= 9.1))
  linden
  warblre
  strict-order-solver))
