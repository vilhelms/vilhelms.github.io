(* Section 3.1 from Thierry Coquand and Christine Paulin, 
   "Inductively defined types", COLOG-88. *)

(* Phi is a positive, but not strictly positive, operator. *)
Definition Phi (a : Type) := (a -> Prop) -> Prop.

(* If we were allowed to form the inductive type
     Inductive A: Type :=
       intro : Phi A -> A.
   then among other things, we would get the following. *)
Axiom A : Type.
Axiom intro : Phi A -> A.
Axiom matchA : A -> Phi A.
Axiom beta : forall x, matchA (intro x) = x.

(* In particular, intro is an injection. *)
Lemma intro_injective : forall p p', intro p = intro p' -> p = p'.
Proof.
  intros.
  assert (matchA (intro p) = (matchA (intro p'))) as H1 by congruence.
  now repeat rewrite beta in H1.
Qed.

(* However, ... *) 

(* Proposition: For any type A, there cannot be an injection
   from Phi(A) to A. *)

(* For any type X, there is an injection from X to (X->Prop),
   which is λx.(λy.x=y) . *)
Definition i {X:Type} : X -> (X -> Prop) := 
  fun x y => x=y.

Lemma i_injective : forall X (x x' :X), i x = i x' -> x = x'.
Proof.
  intros.
  assert (i x x = i x' x) as H1 by congruence.
  compute in H1.
  symmetry.
  rewrite <- H1.
  reflexivity.
Qed.  

(* Hence, by composition, we get an injection f from A->Prop to A. *)
Definition f : (A->Prop) -> A 
  := fun p => intro (i p).

Lemma f_injective : forall p p', f p = f p' -> p = p'.
Proof.
  unfold f. intros.
  apply intro_injective in H. apply i_injective in H. assumption.
Qed.

(* We are now back to the usual Cantor-Russel paradox. *)
(* We can define *)
Definition P0 : A -> Prop
  := fun x => 
       exists (P:A->Prop), f P = x /\ ~ P x.
  (* i.e., P0 x := x codes a set P such that x∉P. *)

Definition x0 := f P0.

(* We have (P0 x0) iff ~(P0 x0) *)
Lemma bad : (P0 x0) <-> ~(P0 x0).
Proof.
split.
  * intros [P [H1 H2]] H.
    change x0 with (f P0) in H1.
    apply f_injective in H1. rewrite H1 in H2.
    auto.
  * intros.
    exists P0. auto.
Qed.

(* Hence a contradiction. *)
Theorem worse : False.
  pose bad. tauto.
Qed.