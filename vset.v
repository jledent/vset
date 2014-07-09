(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about the cumulative hierarchy [V]. *)

Require Import HoTT.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables A B R f g h.


(* ** Misc. definitions ** *)

Definition hor (P:Type) (Q:Type):Type:= minus1Trunc (P + Q).

Definition compose {A B C} (g : forall b, C b) (f : A -> B) :=
  fun x : A => g (f x).

Hint Unfold compose.

Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity).


(* ** Pushout with respect to a relation ** *)

Module Export RPushout.

Local Inductive RPushout {A B : Type} (R : A -> B -> hProp) : Type :=
| inL : A -> RPushout R
| inR : B -> RPushout R.

Axiom glue : forall {A B : Type} (R : A -> B -> hProp)
  (a : A) (b : B) (r : R a b), (inL R a) = (inR R b).

Definition RPushout_rect {A B : Type} {R : A -> B -> hProp}
  (P : RPushout R -> Type)
  (i : forall a : A, P (inL R a)) (j : forall b : B, P (inR R b)) 
  (gl : forall (a : A) (b : B) (r : R a b), (glue R a b r) # (i a) = (j b))
: forall (x : RPushout R), P x
:= fun x => (match x with inL a => (fun _ => i a)
                        | inR b => (fun _ => j b) end) gl.

Axiom RPushout_comp_glue : forall {A B : Type} {R : A -> B -> hProp}
  (P : RPushout R -> Type)
  (i : forall a : A, P (inL R a)) (j : forall b : B, P (inR R b)) 
  (gl : forall (a : A) (b : B) (r : R a b), (glue R a b r) # (i a) = (j b))
  (a : A) (b : B) (r : R a b),
apD (RPushout_rect P i j gl) (glue R a b r) = gl a b r.

End RPushout.

(* ** The non-depentent eliminator *)

Definition RPushout_rect_nd {A B : Type} (R : A -> B -> hProp)
  (P : Type) (i : A -> P) (j : B -> P)
  (gl : forall (a : A) (b : B) (r : R a b), (i a) = (j b))
: RPushout R -> P
:= RPushout_rect (fun _ => P) i j (fun a b r => transport_const _ _ @ gl a b r).

Definition RPushout_comp_nd_glue {A B : Type} (R : A -> B -> hProp) 
  (P : Type) (i : A -> P) (j : B -> P)
  (gl : forall (a : A) (b : B) (r : R a b), (i a) = (j b))
  (a : A) (b : B) (r : R a b)
: ap (RPushout_rect_nd R P i j gl) (glue R a b r) = gl a b r.
Proof.
  apply (cancelL (transport_const (glue R a b r) (i a))).
  path_via (apD (RPushout_rect_nd R P i j gl) (glue R a b r)).
  apply (apD_const (RPushout_rect_nd R P i j gl) (glue R a b r))^.
  refine (RPushout_comp_glue (fun _ => P) _ _ _ _ _ _).
Defined.


(* ** Bitotal relation ** *)

Definition Bitot {A B : Type} (R : A -> B -> hProp) :=
   (forall a : A, hexists (fun (b : B) => R a b))
 * (forall b : B, hexists (fun (a : A) => R a b)).


(* ** Cumulative hierarchy ** *)

Module Export VHierarchy.

Local Inductive Vset : Type :=
| set {A : Type} (f : A -> Vset) : Vset.

Axiom setext : forall {A B : Type} (R : A -> B -> hProp)
  (bitot_R : Bitot R) (h : RPushout R -> Vset),
set (h ∘ (inL R)) = set (h ∘ (inR R)).

Axiom is0trunc_vset : IsTrunc 0 Vset.

Definition Vset_rect (P : Vset -> Type)
  (H_set : forall (A : Type) (f : A -> Vset) (H_f : forall a : A, P (f a)), P (set f))
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R)
    (h : RPushout R -> Vset) (H_h : forall x : RPushout R, P (h x)),
    (setext R bitot_R h) # (H_set A (h ∘ inL R) (H_h ∘ inL R))
      = H_set B (h ∘ inR R) (H_h ∘ inR R) )
  (H_0trunc : forall v : Vset, IsTrunc 0 (P v))
: forall v : Vset, P v
:= fix F (v : Vset) :=
     (match v with
      | set A f => fun _ _ => H_set A f (fun a => F (f a))
     end) H_setext H_0trunc.

Axiom Vset_comp_setext : forall (P : Vset -> Type)
  (H_set : forall (A : Type) (f : A -> Vset) (H_f : forall a : A, P (f a)), P (set f))
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R)
    (h : RPushout R -> Vset) (H_h : forall x : RPushout R, P (h x)),
    (setext R bitot_R h) # (H_set A (h ∘ inL R) (H_h ∘ inL R))
      = H_set B (h ∘ inR R) (H_h ∘ inR R) )
  (H_0trunc : forall v : Vset, IsTrunc 0 (P v))
  (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R) (h : RPushout R -> Vset),
apD (Vset_rect P H_set H_setext H_0trunc) (setext R bitot_R h)
= H_setext A B R bitot_R h ((Vset_rect P H_set H_setext H_0trunc) ∘ h).

End VHierarchy.


(* ** The non-dependent eliminator ** *)

Definition Vset_rect_nd (P : Type)
  (H_set : forall (A : Type), (A -> Vset) -> (A -> P) -> P)
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R)
    (h : RPushout R -> Vset) (H_h : RPushout R -> P),
    H_set A (h ∘ inL R) (H_h ∘ inL R) = H_set B (h ∘ inR R) (H_h ∘ inR R) )
  (H_0trunc : IsTrunc 0 P)
: Vset -> P.
Proof.
  apply (Vset_rect (fun _ => P) H_set).
  intros. exact (transport_const _ _ @ H_setext A B R bitot_R h H_h).
  intro; assumption.
Defined.

Definition Vset_comp_nd_setext (P : Type)
  (H_set : forall (A : Type), (A -> Vset) -> (A -> P) -> P)
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R)
    (h : RPushout R -> Vset) (H_h : RPushout R -> P),
    H_set A (h ∘ inL R) (H_h ∘ inL R) = H_set B (h ∘ inR R) (H_h ∘ inR R) )
  (H_0trunc : IsTrunc 0 P)
  (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R) (h : RPushout R -> Vset)
: ap (Vset_rect_nd P H_set H_setext H_0trunc) (setext R bitot_R h)
  = H_setext A B R bitot_R h ((Vset_rect_nd P H_set H_setext H_0trunc) ∘ h).
Proof.
(* We might want to fill-in the blank in transport_const next line *)
  apply (cancelL (transport_const (setext R bitot_R h) _)).
  path_via (apD (Vset_rect_nd P H_set H_setext H_0trunc) (setext R bitot_R h)).
  symmetry; refine (apD_const (Vset_rect_nd P H_set H_setext H_0trunc) _).
  refine (Vset_comp_setext (fun _ => P) _ _ _ _ _ _ _ _).
Defined.


(* ** Alternative induction principle (This is the one from the book) ** *)

Definition Equal_img {A B C : Type} (f : A -> C) (g : B -> C) :=
   (forall a : A, hexists (fun (b : B) => f a = g b))
 * (forall b : B, hexists (fun (a : A) => f a = g b)).

Let setext' {A B : Type} (f : A -> Vset) (g : B -> Vset) (eq_img : Equal_img f g)
: set f = set g.
Proof.
  pose (R := fun a b => hp (f a = g b) _).
  pose (h := RPushout_rect_nd R Vset f g (fun _ _ r => r)).
  exact (setext R eq_img h).
Defined.

Definition Vset_rect'_nd (P : Type)
  (H_set : forall (A : Type), (A -> Vset) -> (A -> P) -> P)
  (H_setext' : forall (A B : Type) (f : A -> Vset) (g : B -> Vset), (Equal_img f g) ->
    forall (H_f : A -> P) (H_g : B -> P), (Equal_img H_f H_g) ->
    (H_set A f H_f) = (H_set B g H_g) )
  (H_0trunc : IsTrunc 0 P)
: Vset -> P.
Proof.
  apply Vset_rect_nd with H_set.
  intros.
  apply H_setext'.
  split.
    intro. generalize (fst bitot_R a). apply minus1Trunc_map.
      intros [b r]. exists b. exact (ap h (glue R _ _ r)).
    intro. generalize (snd bitot_R b). apply minus1Trunc_map.
      intros [a r]. exists a. exact (ap h (glue R _ _ r)).
  split.
    intro. generalize (fst bitot_R a). apply minus1Trunc_map.
      intros [b r]. exists b. exact (ap H_h (glue R _ _ r)).
    intro. generalize (snd bitot_R b). apply minus1Trunc_map.
      intros [a r]. exists a. exact (ap H_h (glue R _ _ r)).
  assumption.
Defined.

Definition Vset_rect' (P : Vset -> Type)
  (H_0trunc : forall v : Vset, IsTrunc 0 (P v))
  (H_set : forall (A : Type) (f : A -> Vset) (H_f : forall a : A, P (f a)), P (set f))
  (H_setext' : forall (A B : Type) (f : A -> Vset) (g : B -> Vset)
    (eq_img: Equal_img f g)
    (H_f : forall a : A, P (f a)) (H_g : forall b : B, P (g b)),
    ((forall a : A, hexists (fun (b : B) =>
         hexists (fun (p:f a = g b) => p # (H_f a)=H_g b)))
 * (forall b : B, hexists (fun (a : A) =>
         hexists (fun (p:f a = g b) => p# (H_f a)=H_g b))) ->
    (setext' f g eq_img) # (H_set A f H_f) = (H_set B g H_g) ))
: forall v : Vset, P v.
Proof.
  apply Vset_rect with H_set; try assumption.
  intros.
    pose (f := h ∘ inL R : A -> Vset ).
    pose (g := h ∘ inR R : B -> Vset ).
    pose (H_f := H_h ∘ inL R : forall a : A, P (f a)).
    pose (H_g := H_h ∘ inR R : forall b : B, P (g b)).
    assert (eq_img : Equal_img f g). split.
      intro. generalize (fst bitot_R a). apply minus1Trunc_map.
        intros [b r]. exists b. exact (ap h (glue R _ _ r)).
      intro. generalize (snd bitot_R b). apply minus1Trunc_map.
       intros [a r]. exists a. exact (ap h (glue R _ _ r)).
    path_via (transport P (setext' (h ∘ inL R) (h ∘ inR R) eq_img)
                (H_set A (h ∘ inL R) (H_h ∘ inL R))).
      apply (ap (fun p => transport P p (H_set A (h ∘ inL R) (H_h ∘ inL R)))).
      apply allpath_hprop.
    apply (H_setext' A B f g eq_img H_f H_g).  split.
      intros a.
      set (truncb := fst bitot_R a). generalize truncb.
      apply minus1Trunc_map.
      intros [b Rab]. exists b.
      apply min1.
      exists (ap h (glue R _ _ Rab)).
      apply (concatR (apD H_h (glue R _ _ Rab))).
      apply inverse. unfold f, g, compose.  apply transport_compose.
    intros b.
    set (trunca := snd bitot_R b). generalize trunca.
    apply minus1Trunc_map.
    intros [a Rab]. exists a.
    apply min1.
    exists (ap h (glue R _ _ Rab)).
    apply (concatR (apD H_h (glue R _ _ Rab))).
    apply inverse. unfold f, g, compose. apply transport_compose.
Defined.


(* ** Simpler induction principle when the goal is an hprop ** *)

Definition Vset_rect_hprop (P : Vset -> Type)
  (H_set : forall (A : Type) (f : A -> Vset) (H_f : forall a : A, P (f a)), P (set f))
  (isHProp_P : forall v : Vset, IsHProp (P v))
  : forall v : Vset, P v.
Proof.
  apply Vset_rect with H_set.
  intros. apply allpath_hprop.
  intro. apply trunc_succ.
Defined.



Section AssumeAxioms.
Context `{Funext} `{Univalence}.

(* ** Membership relation ** *)

Definition mem (x : Vset) : Vset -> hProp.
Proof.
  apply Vset_rect'_nd with (fun A f _ => hp (hexists (fun a : A => x = f a)) _).
  2: exact isset_hProp.
  intros. apply path_iff_hProp_uncurried.
  split.
    intro H1. apply (minus1Trunc_rect_nondep (A := {a : A & x = f a})).
      intros [a p]. generalize (fst X a). apply minus1Trunc_map.
        intros [b p']. exists b. path_via (f a).
      apply allpath_hprop.
      exact H1.
    intro H1. apply (minus1Trunc_rect_nondep (A := {b : B & x = g b})).
      intros [b p]. generalize (snd X b). apply minus1Trunc_map.
        intros [a p']. exists a. path_via (g b).
      apply allpath_hprop.
      exact H1.
Defined.

Notation " x ∈ v " := (mem x v)
  (at level 30).


(* ** Subset relation ** *)

Definition subset (x : Vset) (y : Vset) : hProp
:= hp (forall z : Vset, z ∈ x -> z ∈ y) _.

Notation " x ⊆ y " := (subset x y)
  (at level 30).


(* ** Bisimulation relation ** *)

Definition bisim : Vset -> Vset -> hProp.
refine (Vset_rect'_nd (Vset -> hProp) (fun A f H_f => 
          Vset_rect'_nd hProp (fun B g _ => 
            hp ((forall a, hexists (fun b => H_f a (g b)))
              * forall b, hexists (fun a => H_f a (g b))) _
          ) _ _
       ) _ _
).
intros.
apply (Funext_implies_NaiveFunext H).
apply Vset_rect_hprop.
2: intro; apply istrunc_paths, isset_hProp.
intros C h _; simpl.
apply path_iff_hProp_uncurried. split.
intros [H1 H2]. split.
  intro b. apply (minus1Trunc_rect_nondep (A := {a : A & H_f a = H_g b})).
    intros [a p]. generalize (H1 a). apply minus1Trunc_map.
      intros [c H3]. exists c. exact ((ap10 p (h c)) # H3).
    apply allpath_hprop.
    exact (snd X0 b).
  intro c. apply (minus1Trunc_rect_nondep (A := {a : A & H_f a (h c)})).
    intros [a H3]. generalize (fst X0 a). apply minus1Trunc_map.
      intros [b p]. exists b. exact ((ap10 p (h c)) # H3).
    apply allpath_hprop.
    exact (H2 c).
intros [H1 H2]. split.
  intro a. apply (minus1Trunc_rect_nondep (A := {b : B & H_f a = H_g b})).
    intros [b p]. generalize (H1 b). apply minus1Trunc_map.
      intros [c H3]. exists c. exact ((ap10 p^ (h c)) # H3).
    apply allpath_hprop.
    exact (fst X0 a).
  intro c. apply (minus1Trunc_rect_nondep (A := {b : B & H_g b (h c)})).
    intros [b H3]. generalize (snd X0 b). apply minus1Trunc_map.
      intros [a p]. exists a. exact ((ap10 p^ (h c)) # H3).
    apply allpath_hprop.
    exact (H2 c).
Admitted.


(* ** Axioms of set theory (theorem 10.5.8) ** *)

Definition Emptyset : Vset := set (Empty_rect (fun _ => Vset)).

Lemma not_in_emptyset : forall x, ~ (x ∈ Emptyset).
Proof.
  intro; intro. apply (minus1Trunc_rect_nondep (A := {a : Empty & x = (Empty_rect (fun _ => Vset)) a})).
  intros [ff _]. exact ff.
  apply allpath_hprop.
  exact X.
Qed.

Lemma extensionality : forall x y : Vset, (x ⊆ y * y ⊆ x) <-> x = y.
Proof.
  refine (Vset_rect_hprop _ _ _). intros A f _.
  refine (Vset_rect_hprop _ _ _). intros B g _.
  split. intro. destruct X. apply setext'. split.
    intro. apply (h (f a)). apply min1. exists a; reflexivity.
    intro. apply (minus1Trunc_rect_nondep (A := {a : A & g b = f a})).
      intros [a p]. apply min1. exists a. exact p^.
      apply allpath_hprop.
      apply (h0 (g b)). apply min1. exists b; reflexivity.
  intro p; split. intros z h. apply (transport (fun x => z ∈ x) p h).
  intros z h. apply (transport (fun x => z ∈ x) p^ h).
Qed.

Lemma pairing : forall u v, hexists (fun w => forall x, x ∈ w <-> hor (x = u) (x = v)).
Proof.
  intros. apply min1. exists (set (fun b : Bool => if b then u else v)).
  intro; split.
    intro. generalize X. apply minus1Trunc_map.
      intros [b p]. destruct b. left; assumption. right; assumption.
    intro. generalize X. apply minus1Trunc_map.
      intros [h | h]. exists true; assumption. exists false; assumption.
Qed.

Lemma mem_induction (C : Vset -> hProp)
: (forall v, (forall x, x ∈ v -> C x) -> C v) -> forall v, C v.
Proof.
  intro.
  apply Vset_rect_hprop.
    intros. apply X. intros. apply (minus1Trunc_rect_nondep (A := {a : A & x = f a})).
      intro. destruct X1. rewrite p. apply H_f.
      apply isp.
      assumption.
    intro. apply isp.
Defined.

Lemma replacement : forall (r : Vset -> Vset) (x : Vset),
  hexists (fun w => forall y, y ∈ w <-> hexists (fun z => z ∈ x * (y = r z))).
Proof.
  intro r. apply Vset_rect_hprop.
  intros A f _. apply min1. exists (set (r ∘ f)). split.
    apply minus1Trunc_map.
      intros [a p]. exists (f a). split. apply min1; exists a; auto. assumption.
    intro. apply (minus1Trunc_rect_nondep (A := {z : Vset & z ∈ set f * (y = r z)})).
      intros [z [h p]]. generalize h. apply minus1Trunc_map.
        intros [a p']. exists a. path_via (r z). rewrite p'; auto.
      apply allpath_hprop.
      exact X.
  intro. apply minus1Trunc_is_prop.
Qed.

Lemma separation (C : Vset -> hProp) : forall a : Vset,
  hexists (fun w => forall x, x ∈ w <-> x ∈ a * (C x)).
Proof.
  apply Vset_rect_hprop.
  intros A f _. apply min1. exists (set (fun z : {a : A & C (f a)} => f (pr1 z))). split.
    intro. apply (minus1Trunc_rect_nondep (A := {z : {a : A & C (f a)} & x = f (pr1 z)})).
      intros [[a h] p]. split. apply min1; exists a; assumption. rewrite p; exact h.
      apply allpath_hprop.
      exact X.
    intros [h0 h]. generalize h0. apply minus1Trunc_map.
      intros [a p]. exists (a; transport C p h). exact p.
  intro; apply minus1Trunc_is_prop.
Qed.

(* Vsucc x := x ∪ {x} *)
Definition Vsucc : Vset -> Vset.
Proof.
  apply Vset_rect'_nd with (fun A f _ =>
    set (fun (x : A + Unit) => match x with inl a => f a
                                          | inr tt => set f end)).
  intros. apply setext'. split.
    intro. destruct a.
      generalize (fst X a). apply minus1Trunc_map.
        intros [b p]. exists (inl b); exact p.
      apply min1; exists (inr tt). destruct u. apply setext'; auto.
    intro. destruct b.
      generalize (snd X b). apply minus1Trunc_map. 
        intros [a p]. exists (inl a); exact p.
      apply min1; exists (inr tt). destruct u. apply setext'; auto.
  exact is0trunc_vset.
Defined.

Fixpoint I n := match n with 0   => Emptyset
                           | S n => Vsucc (I n) end.
Definition omega : Vset := set I.

Lemma infinity : (Emptyset ∈ omega) * (forall x, x ∈ omega -> Vsucc x ∈ omega).
Proof.
  split. apply min1; exists 0; auto.
  intro. apply minus1Trunc_map.
    intros [n p]. exists (S n). rewrite p; auto.
Qed.


End AssumeAxioms.