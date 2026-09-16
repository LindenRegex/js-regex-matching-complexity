From Stdlib Require Import Classes.RelationClasses Lists.List.
Import ListNotations.

Require Import Solver.

Section Tests.
  Variable lt : list nat -> list nat -> Prop.
  Variable SO : StrictOrder lt.

  Goal forall a b c d,
    lt a b -> lt c d -> lt b c -> lt a d.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d e,
    lt a e -> lt a b -> lt c d -> lt b c -> lt a d.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d e,
    lt a b -> lt a e -> lt c d -> lt b c -> lt a d.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d,
    lt a b -> lt b c -> lt c d -> lt d b -> lt a a.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c,
    lt a b -> lt b a -> lt a c.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* Simple transitivity chains *)
  Goal forall a b c,
    lt a b -> lt b c -> lt a c.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d e,
    lt a b -> lt b c -> lt c d -> lt d e -> lt a e.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d e f,
    lt a b -> lt b c -> lt c d -> lt d e -> lt e f -> lt a f.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* Multiple paths to same conclusion *)
  Goal forall a b c d,
    lt a b -> lt a c -> lt b d -> lt c d -> lt a d.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d e,
    lt a b -> lt a c -> lt b e -> lt c e -> lt e d -> lt a d.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* Contradiction cases - cycles *)
  Goal forall a b,
    lt a b -> lt b a -> lt a a.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c,
    lt a b -> lt b c -> lt c a -> lt a b.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d,
    lt a b -> lt b c -> lt c d -> lt d a -> lt a c.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* Complex graphs with multiple variables *)
  Goal forall a b c d e f,
    lt a b -> lt b c -> lt d e -> lt e f -> lt c d -> lt a f.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d e f g,
    lt a b -> lt c d -> lt e f -> lt b c -> lt d e -> lt f g -> lt a g.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* Diamond patterns *)
  Goal forall a b c d,
    lt a b -> lt a c -> lt b d -> lt c d -> lt a d.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d e,
    lt a b -> lt a c -> lt b d -> lt c e -> lt d e -> lt a e.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* More contradiction cases *)
  Goal forall a b c,
    lt a b -> lt b a -> lt b c.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d,
    lt a b -> lt b c -> lt c a -> lt d d.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* Long chains with irrelevant hypotheses *)
  Goal forall a b c d e x y p q,
    lt a b -> lt x y -> lt b c -> lt c d -> lt p q -> lt d e -> lt a e.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* Overlapping chains *)
  Goal forall a b c d e f,
    lt a b -> lt b c -> lt c d -> lt b e -> lt e f -> lt a f.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d e f g,
    lt a b -> lt b c -> lt c d -> lt a e -> lt e f -> lt f g -> lt a d.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* Self-loops through transitivity *)
  Goal forall a b c d,
    lt a b -> lt b c -> lt c d -> lt d a -> 1 = 2.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* Complex mixed patterns *)
  Goal forall a b c d e f g h,
    lt a b -> lt b c -> lt d e -> lt e f -> lt c d -> lt f g -> lt g h -> lt a h.
  Proof.
    intros.
    strict_order lt.
  Qed.

  Goal forall a b c d e f,
    lt a b -> lt a c -> lt a d -> lt b e -> lt c e -> lt d e -> lt e f -> lt a f.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* Edge cases with minimal hypotheses *)
  Goal forall a b,
    lt a b -> lt a b.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* finding cycles while looking for paths *)
  Goal forall a b,
    (* here, we look for a cycle for `a` but while doing so we find the cycle `b`<->`b` *)
    lt a b -> lt b b -> False.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* make sure we can `try` failed solving *)
  Goal False.
  Proof.
    try (strict_order lt).
  Abort.

  (* ---- Long chains ---- *)

  (* 10-element chain *)
  Goal forall a b c d e f g h i j,
    lt a b -> lt b c -> lt c d -> lt d e -> lt e f ->
    lt f g -> lt g h -> lt h i -> lt i j -> lt a j.
  Proof. intros. strict_order lt. Qed.

  (* Long chain, goal is a sub-path in the middle *)
  Goal forall a b c d e f g h i j,
    lt a b -> lt b c -> lt c d -> lt d e -> lt e f ->
    lt f g -> lt g h -> lt h i -> lt i j -> lt c g.
  Proof. intros. strict_order lt. Qed.

  (* Long chain with many distractors *)
  Goal forall a b c d e f g p q r s t u v,
    lt p q -> lt a b -> lt r s -> lt b c -> lt s t ->
    lt c d -> lt t u -> lt d e -> lt u v -> lt e f ->
    lt q r -> lt f g -> lt a g.
  Proof. intros. strict_order lt. Qed.

  (* ---- Complex graph structures ---- *)

  (* Multiple merging paths: a diamond within a diamond *)
  Goal forall a b c d e f g,
    lt a b -> lt a c -> lt b d -> lt c d ->
    lt d e -> lt d f -> lt e g -> lt f g -> lt a g.
  Proof. intros. strict_order lt. Qed.

  (* Wide fan-in: many predecessors of a single node *)
  Goal forall a b c d e f g h,
    lt a e -> lt b e -> lt c e -> lt d e ->
    lt e f -> lt f g -> lt g h -> lt c h.
  Proof. intros. strict_order lt. Qed.

  (* Wide fan-out then converge *)
  Goal forall a b c d e f g,
    lt a b -> lt a c -> lt a d -> lt a e ->
    lt b f -> lt c f -> lt d f -> lt e f -> lt f g -> lt a g.
  Proof. intros. strict_order lt. Qed.

  (* Zigzag pattern: a->b, c->d, b->c, d->e, ... *)
  Goal forall a b c d e f g h i,
    lt a b -> lt c d -> lt e f -> lt g h ->
    lt b c -> lt d e -> lt f g -> lt h i -> lt a i.
  Proof. intros. strict_order lt. Qed.

  (* Two parallel chains that cross *)
  Goal forall a b c d e f g h,
    lt a b -> lt b c -> lt c d ->
    lt e f -> lt f g -> lt g h ->
    lt b f -> lt a h.
  Proof. intros. strict_order lt. Qed.

  (* ---- Cycle / contradiction tests ---- *)

  (* 2-cycle proves arbitrary goal *)
  Goal forall a b c d,
    lt a b -> lt b a -> lt c d.
  Proof. intros. strict_order lt. Qed.

  (* 3-cycle proves arbitrary goal *)
  Goal forall a b c x y,
    lt a b -> lt b c -> lt c a -> lt x y.
  Proof. intros. strict_order lt. Qed.

  (* 5-cycle, goal is unrelated *)
  Goal forall a b c d e x y,
    lt a b -> lt b c -> lt c d -> lt d e -> lt e a -> lt x y.
  Proof. intros. strict_order lt. Qed.

  (* Cycle in a subgraph, goal on a different component *)
  Goal forall a b c p q r,
    lt a b -> lt b c -> lt c a ->
    lt p q -> lt q r -> lt p r.
  Proof. intros. strict_order lt. Qed.

  (* Cycle with a tail: a->b->c->d->b, goal involves the tail *)
  Goal forall a b c d,
    lt a b -> lt b c -> lt c d -> lt d b -> lt a c.
  Proof. intros. strict_order lt. Qed.

  (* Cycle proves False, so we can prove anything (even non-lt) *)
  Goal forall a b c (P : Prop),
    lt a b -> lt b c -> lt c a -> P.
  Proof. intros. strict_order lt. Qed.

  (* Long cycle: 8-cycle *)
  Goal forall a b c d e f g h (P : Prop),
    lt a b -> lt b c -> lt c d -> lt d e ->
    lt e f -> lt f g -> lt g h -> lt h a -> P.
  Proof. intros. strict_order lt. Qed.

  (* Two separate cycles, goal is arbitrary *)
  Goal forall a b c d e f (P : Prop),
    lt a b -> lt b c -> lt c a ->
    lt d e -> lt e f -> lt f d -> P.
  Proof. intros. strict_order lt. Qed.

  (* Cycle reachable only from certain nodes *)
  Goal forall a b c d e,
    lt a b -> lt b c -> lt c d -> lt d b -> lt a e.
  Proof. intros. strict_order lt. Qed.

  (* ---- Mixed: path + irrelevant cycle ---- *)

  (* Direct path exists, but there's also a cycle elsewhere *)
  Goal forall a b c d e f,
    lt a b -> lt b c ->
    lt d e -> lt e f -> lt f d ->
    lt a c.
  Proof. intros. strict_order lt. Qed.

  (* ---- Stress: dense graphs ---- *)

  (* Complete ordering on 5 elements (10 edges), pick a transitive goal *)
  Goal forall a b c d e,
    lt a b -> lt a c -> lt a d -> lt a e ->
    lt b c -> lt b d -> lt b e ->
    lt c d -> lt c e ->
    lt d e ->
    lt a e.
  Proof. intros. strict_order lt. Qed.

  (* Same complete ordering, non-obvious sub-path *)
  Goal forall a b c d e,
    lt a b -> lt a c -> lt a d -> lt a e ->
    lt b c -> lt b d -> lt b e ->
    lt c d -> lt c e ->
    lt d e ->
    lt b d.
  Proof. intros. strict_order lt. Qed.

  (* Dense graph with cross-edges, long goal path *)
  Goal forall a b c d e f g h,
    lt a b -> lt a c -> lt b d -> lt c d ->
    lt d e -> lt d f -> lt e g -> lt f g ->
    lt g h -> lt b f -> lt c e -> lt a h.
  Proof. intros. strict_order lt. Qed.

  (* Element is not an identifier *)
  Goal forall a c d e,
    lt a e -> lt a (cons 1 (cons 2 nil)) -> lt c d -> lt (cons 1 (cons 2 nil)) c -> lt a d.
  Proof.
    intros.
    strict_order lt.
  Qed.

  (* Elements are same but only after reductions *)
  Goal forall a b,
    lt a b -> lt b (cons (1+1) (cons (2*3) nil)) -> lt a (cons 2 (cons 6 nil)).
  Proof.
    intros.
    strict_order lt.
  Qed.
End Tests.

(* ================================================================ *)
(*  Tests for generic / lambda-wrapped relations                     *)
(* ================================================================ *)

(* --- Reversed arguments: fun x y => R y x ----------------------- *)
Section LambdaTests_Reversed.
  Variable R : nat -> nat -> Prop.
  Variable R_rev : StrictOrder (fun a b : nat => R b a).

  (* Basic 2-step chain *)
  Goal forall a b c : nat,
    R b a -> R c b -> (fun x y => R y x) a c.
  Proof. intros. strict_order (fun x y => R y x). Qed.

  (* 3-step chain *)
  Goal forall a b c d : nat,
    R b a -> R c b -> R d c -> (fun x y => R y x) a d.
  Proof. intros. strict_order (fun x y => R y x). Qed.

  (* 5-step chain *)
  Goal forall a b c d e f : nat,
    R b a -> R c b -> R d c -> R e d -> R f e -> (fun x y => R y x) a f.
  Proof. intros. strict_order (fun x y => R y x). Qed.

  (* Diamond: two paths to same destination *)
  Goal forall a b c d : nat,
    R b a -> R c a -> R d b -> R d c -> (fun x y => R y x) a d.
  Proof. intros. strict_order (fun x y => R y x). Qed.

  (* 2-cycle → contradiction *)
  Goal forall a b (P : Prop),
    R a b -> R b a -> P.
  Proof. intros. strict_order (fun x y => R y x). Qed.

  (* 3-cycle → contradiction *)
  Goal forall a b c (P : Prop),
    R b a -> R c b -> R a c -> P.
  Proof. intros. strict_order (fun x y => R y x). Qed.

  (* 5-cycle → contradiction *)
  Goal forall a b c d e (P : Prop),
    R b a -> R c b -> R d c -> R e d -> R a e -> P.
  Proof. intros. strict_order (fun x y => R y x). Qed.

  (* Cycle makes an otherwise unprovable goal provable *)
  Goal forall a b c d : nat,
    R a b -> R b a -> (fun x y => R y x) c d.
  Proof. intros. strict_order (fun x y => R y x). Qed.

  (* Chain with irrelevant hypotheses *)
  Goal forall a b c x y z : nat,
    R x z -> R b a -> R y x -> R c b -> (fun p q => R q p) a c.
  Proof. intros. strict_order (fun p q => R q p). Qed.
End LambdaTests_Reversed.

(* --- Symmetric successor mapping: fun x y => R (S x) (S y) ------- *)
Section LambdaTests_SuccessorBoth.
  Variable R : nat -> nat -> Prop.
  Variable R_succ : StrictOrder (fun a b : nat => R (S a) (S b)).

  (* Basic chain *)
  Goal forall a b c : nat,
    R (S a) (S b) -> R (S b) (S c) -> (fun x y => R (S x) (S y)) a c.
  Proof. intros. strict_order (fun x y => R (S x) (S y)). Qed.

  (* 4-step chain *)
  Goal forall a b c d e : nat,
    R (S a) (S b) -> R (S b) (S c) -> R (S c) (S d) -> R (S d) (S e) ->
    (fun x y => R (S x) (S y)) a e.
  Proof. intros. strict_order (fun x y => R (S x) (S y)). Qed.

  (* Goal is a sub-path in the middle of a long chain *)
  Goal forall a b c d e : nat,
    R (S a) (S b) -> R (S b) (S c) -> R (S c) (S d) -> R (S d) (S e) ->
    (fun x y => R (S x) (S y)) b d.
  Proof. intros. strict_order (fun x y => R (S x) (S y)). Qed.

  (* Diamond *)
  Goal forall a b c d : nat,
    R (S a) (S b) -> R (S a) (S c) -> R (S b) (S d) -> R (S c) (S d) ->
    (fun x y => R (S x) (S y)) a d.
  Proof. intros. strict_order (fun x y => R (S x) (S y)). Qed.

  (* 2-cycle → contradiction *)
  Goal forall a b (P : Prop),
    R (S a) (S b) -> R (S b) (S a) -> P.
  Proof. intros. strict_order (fun x y => R (S x) (S y)). Qed.

  (* 3-cycle → contradiction *)
  Goal forall a b c (P : Prop),
    R (S a) (S b) -> R (S b) (S c) -> R (S c) (S a) -> P.
  Proof. intros. strict_order (fun x y => R (S x) (S y)). Qed.

  (* Cycle alongside an independent path (goal on the path) *)
  Goal forall a b c d e : nat,
    R (S a) (S b) -> R (S b) (S c) ->
    R (S d) (S e) -> R (S e) (S d) ->
    (fun x y => R (S x) (S y)) a c.
  Proof. intros. strict_order (fun x y => R (S x) (S y)). Qed.
End LambdaTests_SuccessorBoth.

(* --- Asymmetric mapping: only right argument gets S --------------- *)
Section LambdaTests_RightSuccessor.
  Variable R : nat -> nat -> Prop.
  Variable R_rsucc : StrictOrder (fun a b : nat => R a (S b)).

  (* Basic chain: a -> b -> c  *)
  (* hyp a->b means R a (S b); hyp b->c means R b (S c) *)
  Goal forall a b c : nat,
    R a (S b) -> R b (S c) -> (fun x y => R x (S y)) a c.
  Proof. intros. strict_order (fun x y => R x (S y)). Qed.

  (* 4-step chain *)
  Goal forall a b c d e : nat,
    R a (S b) -> R b (S c) -> R c (S d) -> R d (S e) ->
    (fun x y => R x (S y)) a e.
  Proof. intros. strict_order (fun x y => R x (S y)). Qed.

  (* 2-cycle → contradiction *)
  Goal forall a b (P : Prop),
    R a (S b) -> R b (S a) -> P.
  Proof. intros. strict_order (fun x y => R x (S y)). Qed.

  (* 3-cycle → contradiction *)
  Goal forall a b c (P : Prop),
    R a (S b) -> R b (S c) -> R c (S a) -> P.
  Proof. intros. strict_order (fun x y => R x (S y)). Qed.

  (* Irrelevant hypotheses scattered among real ones *)
  Goal forall a b c d x y z : nat,
    R x (S z) -> R a (S b) -> R y (S z) -> R b (S c) -> R z (S x) ->
    R c (S d) -> (fun p q => R p (S q)) a d.
  Proof. intros. strict_order (fun p q => R p (S q)). Qed.
End LambdaTests_RightSuccessor.

(* --- List cons mapping -------------- *)
(*     fun x y => lt y (5 :: x)                                *)
(*     A hypothesis  lt b (5::a) provides edge  a -> b in the graph   *)
Section LambdaTests_ListPrepend.
  Variable lt : list nat -> list nat -> Prop.
  Variable SO : StrictOrder (fun a b => lt b (5 :: a)).

  (* Basic 2-step chain *)
  Goal forall a b c : list nat,
    lt b (5 :: a) -> lt c (5 :: b) ->
    (fun x y => lt y (5 :: x)) a c.
  Proof. intros. strict_order (fun x y => lt y (5 :: x)). Qed.

  (* 3-step chain *)
  Goal forall a b c d : list nat,
    lt b (5 :: a) -> lt c (5 :: b) -> lt d (5 :: c) ->
    (fun x y => lt y (5 :: x)) a d.
  Proof. intros. strict_order (fun x y => lt y (5 :: x)). Qed.

  (* Long 5-step chain *)
  Goal forall a b c d e f : list nat,
    lt b (5 :: a) -> lt c (5 :: b) -> lt d (5 :: c) ->
    lt e (5 :: d) -> lt f (5 :: e) ->
    (fun x y => lt y (5 :: x)) a f.
  Proof. intros. strict_order (fun x y => lt y (5 :: x)). Qed.

  (* Goal is a sub-path in the middle of a chain *)
  Goal forall a b c d e f : list nat,
    lt b (5 :: a) -> lt c (5 :: b) -> lt d (5 :: c) ->
    lt e (5 :: d) -> lt f (5 :: e) ->
    (fun x y => lt y (5 :: x)) b e.
  Proof. intros. strict_order (fun x y => lt y (5 :: x)). Qed.

  (* Diamond: two routes to the same list *)
  Goal forall a b c d : list nat,
    lt b (5 :: a) -> lt c (5 :: a) ->
    lt d (5 :: b) -> lt d (5 :: c) ->
    (fun x y => lt y (5 :: x)) a d.
  Proof. intros. strict_order (fun x y => lt y (5 :: x)). Qed.

  (* 2-cycle → contradiction *)
  Goal forall a b (P : Prop),
    lt b (5 :: a) -> lt a (5 :: b) -> P.
  Proof. intros. strict_order (fun x y => lt y (5 :: x)). Qed.

  (* 3-cycle → contradiction *)
  Goal forall a b c (P : Prop),
    lt b (5 :: a) -> lt c (5 :: b) -> lt a (5 :: c) -> P.
  Proof. intros. strict_order (fun x y => lt y (5 :: x)). Qed.

  (* 5-cycle → contradiction *)
  Goal forall a b c d e (P : Prop),
    lt b (5 :: a) -> lt c (5 :: b) -> lt d (5 :: c) ->
    lt e (5 :: d) -> lt a (5 :: e) -> P.
  Proof. intros. strict_order (fun x y => lt y (5 :: x)). Qed.

  (* Cycle in a subgraph; goal follows from a separate connected path *)
  Goal forall a b c d e : list nat,
    lt b (5 :: a) -> lt c (5 :: b) ->
    lt d (5 :: c) -> lt c (5 :: d) ->   (* c <-> d cycle *)
    (fun x y => lt y (5 :: x)) a b.
  Proof. intros. strict_order (fun x y => lt y (5 :: x)). Qed.

  (* Irrelevant hypotheses scattered around *)
  Goal forall a b c x y : list nat,
    lt x (5 :: y) -> lt b (5 :: a) -> lt y (5 :: x) ->
    lt c (5 :: b) -> (fun p q => lt q (5 :: p)) a c.
  Proof. intros. strict_order (fun p q => lt q (5 :: p)). Qed.

  (* Non-trivial elements: cons-built lists as node labels *)
  Goal forall a b c : list nat,
    lt b (5 :: (0 :: a)) -> lt c (5 :: b) ->
    (fun x y => lt y (5 :: x)) (0 :: a) c.
  Proof. intros. strict_order (fun x y => lt y (5 :: x)). Qed.

  (* Extra fixed prefix differs from the edges: 7 :: instead of 5 :: *)
  Variable SO' : StrictOrder (fun a b => lt b (7 :: a)).

  Goal forall a b c : list nat,
    lt b (7 :: a) -> lt c (7 :: b) ->
    (fun x y => lt y (7 :: x)) a c.
  Proof. intros. strict_order (fun x y => lt y (7 :: x)). Qed.

  Goal forall a b c d : list nat,
    lt b (7 :: a) -> lt c (7 :: b) -> lt d (7 :: c) ->
    (fun x y => lt y (7 :: x)) a d.
  Proof. intros. strict_order (fun x y => lt y (7 :: x)). Qed.

  (* 2-cycle with 7 :: prefix *)
  Goal forall a b (P : Prop),
    lt b (7 :: a) -> lt a (7 :: b) -> P.
  Proof. intros. strict_order (fun x y => lt y (7 :: x)). Qed.
End LambdaTests_ListPrepend.
