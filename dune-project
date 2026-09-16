(lang dune 3.21)

(name jsregexoptp)

(generate_opam_files false)

(using rocq 0.11)

(authors "Anonymous")

(package
 (name jsregexoptp)
 (synopsis "Proving that JavaScript regex matching is OptP-complete")
 (depends
  (rocq-prover (= 9.1.0))
  (linden (= "dev"))))
