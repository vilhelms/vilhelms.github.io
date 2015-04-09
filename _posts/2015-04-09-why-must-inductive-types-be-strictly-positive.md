---
layout: post
title: Why must inductive types be strictly positive?
---

In dependently typed languages like Coq and Agda, when you define a datatype D, all the constructors are required to be strictly positive. (That is, the types of the constructor arguments must not involve a D to the left of an arrow.) It is easy to see why *negative* types, where D appears to the left of an odd number of arrows, are bad. For example, if the datatype
{% highlight coq %}
Inductive D : Type :=
  | D_intro : (D -> D) -> D.
{% endhighlight %}
was accepted, one could write an infinitely looping term using [Curry's paradox](http://en.wikipedia.org/wiki/Curry%27s_paradox). 

On the other hand, it's not immediately clear what would be bad about allowing datatypes which are positive but not strictly positive (that is, where D occurs to the left of an even number of arrows). It is known that such types can be [encoded in System F](http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt) without introducing any nontermination, so what goes wrong in a dependent language?

The answer is in Thierry Coquand and Christine Paulin's paper [Inductively Defined Types](http://link.springer.com/chapter/10.1007/3-540-52335-9_47) (COLOG-88). They show that if the positive, but not strictly positive type 
{% highlight coq %}
Inductive A : Type :=
  | introA : ((A->Prop)->Prop) -> A.
{% endhighlight %}
was allowed, then one could derive a contradiction. The construction is short, but the syntax the programs are written in is a bit old and unfamiliar. I translated it into modern Coq as follows. (You can also [download the source file](/files/PositiveParadox.v).)

{% highlight coq %}
(* Section 3.1 from Thierry Coquand and Christine Paulin, 
   "Inductively defined types", COLOG-88. *)

(* Phi is a positive, but not strictly positive, operator. *)
Definition Phi (a : Type) := (a -> Prop) -> Prop.

(* If we were allowed to form the inductive type
     Inductive A: Type :=
       introA : Phi A -> A.
   then among other things, we would get the following. *)
Axiom A : Type.
Axiom introA : Phi A -> A.
Axiom matchA : A -> Phi A.
Axiom beta : forall x, matchA (introA x) = x.

(* In particular, introA is an injection. *)
Lemma introA_injective : forall p p', introA p = introA p' -> p = p'.
Proof.
  intros.
  assert (matchA (introA p) = (matchA (introA p'))) as H1 by congruence.
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
  := fun p => introA (i p).

Lemma f_injective : forall p p', f p = f p' -> p = p'.
Proof.
  unfold f. intros.
  apply introA_injective in H. apply i_injective in H. assumption.
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
{% endhighlight %}

As the paper points out there is a subtle point: the development relies that fact that Prop in Coq is impredicative. In particular, it defines a type P0, roughly the "set of sets that do not contain themselves":
{% highlight coq %}
Definition P0 : A -> Prop
  := fun x =>
   exists (P:A->Prop), f P = x /\ ~ P x.
{% endhighlight %}
In a predicative language like Agda, you could not make {%highlight agda nowrap %}P0 : A->Set{% endhighlight %}, because it quantifies over a Set. You would have to put it in Set1
{% highlight agda %}
P0 : A → Set1
P0 x = Σ (A → Set) (λ P → f P ≡ x ∧ ¬ P x)
{%endhighlight%}
 and then the Russel-style paradox fails, because later you want to instantiate the existential quantifier with P0 itself.

This leave the question open whether one could add non-strictly positive types to Agda. In fact, [Coquand  himself](https://lists.chalmers.se/pipermail/agda/2013/006189.html) posted a comment on the Agda mailing list, suggesting that one could.

There is also Nax Mendler's work on [inductive types in Nuprl](http://ecommons.library.cornell.edu/handle/1813/6710), which doesn't fit neatly into the above story. Nuprl is a predicative theory, and indeed it supports general positive recursive types. *However*, the elimination rule for recursive types is different from the Coq/Agda rule, and Mendler goes on to say that his consistency proof also justifies adding a "stratified impredicative" ∀-type. (That is, the ∀ quantifies over all types on its own level, unlike Coq's type which also quantifies over all higher levels. But the stratified version is already enough to encode the above existential type.)

I find this business confusing but intriguing! On the one hand, the original motivation for universe levels was exactly to rule out Russel's paradox, and yet in the presence of impredicativity it somehow comes back to haunt us? On the other, saying that there is an isomorphism between A and 𝒫(𝒫A) does not make sense set-theoretically, so what is the meaning of the predicative system?
