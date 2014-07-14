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
set (h o (inL R)) = set (h o (inR R)).

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

(* We might also want to prove the associated computation rules *)
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
Context `{fs : Funext} `{ua : Univalence}.

(* ** Membership relation ** *)

Definition mem (x : Vset) : Vset -> hProp.
Proof.
  apply Vset_rect'_nd with (fun A f _ => hp (hexists (fun a : A => x = f a)) _).
  2: exact isset_hProp.
  intros. apply path_iff_hProp_uncurried.
  split.
    intro H. apply (minus1Trunc_rect_nondep (A := {a : A & x = f a})).
      intros [a p]. generalize (fst X a). apply minus1Trunc_map.
        intros [b p']. exists b. path_via (f a).
      apply allpath_hprop.
      exact H.
    intro H. apply (minus1Trunc_rect_nondep (A := {b : B & x = g b})).
      intros [b p]. generalize (snd X b). apply minus1Trunc_map.
        intros [a p']. exists a. path_via (g b).
      apply allpath_hprop.
      exact H.
Defined.

Notation " x ∈ v " := (mem x v)
  (at level 30).


(* ** Subset relation ** *)

Definition subset (x : Vset) (y : Vset) : hProp
:= hp (forall z : Vset, z ∈ x -> z ∈ y) _.

Notation " x ⊆ y " := (subset x y)
  (at level 30).


(* ** Bisimulation relation ** *)

(* We need to assume a different instance of Funext to avoid universe inconsistency *)
Definition bisim `{fs' : Funext} : Vset -> Vset -> hProp.

  (* We first fix the first argument as set(A,f) and define bisim_aux : Vset -> hProp, by induction. This is the inner of the two inductions. *)
  Definition bisim_aux (A : Type) (f : A -> Vset) (H_f : A -> Vset -> hProp) : (Vset -> hProp).
  apply Vset_rect'_nd with
    (fun B g _ => hp ( (forall a, hexists (fun b => H_f a (g b)))
                      * forall b, hexists (fun a => H_f a (g b)) ) _
    ).
  2: apply isset_hProp.
  intros B B' g g' eq_img H_g H_g' H_img; simpl.
  apply path_iff_hProp_uncurried. split.
  intros [H1 H2]; split.
   intro a. apply (minus1Trunc_rect_nondep (A := {b : B & H_f a (g b)})).
     intros [b H3]. generalize (fst eq_img b). apply minus1Trunc_map.
       intros [b' p]. exists b'. exact (transport (fun x => H_f a x) p H3).
     apply allpath_hprop.
     exact (H1 a).
   intro b'. apply (minus1Trunc_rect_nondep (A := {b : B & g b = g' b'})).
     intros [b p]. generalize (H2 b). apply minus1Trunc_map.
       intros [a H3]. exists a. exact (transport (fun x => H_f a x) p H3).
     apply allpath_hprop.
     exact (snd eq_img b').
  intros [H1 H2]; split.
   intro a. apply (minus1Trunc_rect_nondep (A := {b' : B' & H_f a (g' b')})).
     intros [b' H3]. generalize (snd eq_img b'). apply minus1Trunc_map.
        intros [b p]. exists b. exact (transport (fun x => H_f a x) p^ H3).
      apply allpath_hprop.
      exact (H1 a).
   intro b. apply (minus1Trunc_rect_nondep (A := {b' : B' & g b = g' b'})).
     intros [b' p]. generalize (H2 b'). apply minus1Trunc_map.
       intros [a H3]. exists a. exact (transport (fun x => H_f a x) p^ H3).
     apply allpath_hprop.
     exact (fst eq_img b).
  Defined.

(* Then define bisim : Vset -> (Vset -> hProp) by induction again *)
refine (Vset_rect'_nd (Vset -> hProp) bisim_aux _ _).
intros A B f g eq_img H_f H_g H_img.
apply (Funext_implies_NaiveFunext fs').
clear fs'. (* Necessary to avoid universe inconsistency *)
apply Vset_rect_hprop.
2: intro; apply istrunc_paths, isset_hProp.
intros C h _; simpl.
apply path_iff_hProp_uncurried. split.
intros [H1 H2]. split.
  intro b. apply (minus1Trunc_rect_nondep (A := {a : A & H_f a = H_g b})).
    intros [a p]. generalize (H1 a). apply minus1Trunc_map.
      intros [c H3]. exists c. exact ((ap10 p (h c)) # H3).
    apply allpath_hprop.
    exact (snd H_img b).
  intro c. apply (minus1Trunc_rect_nondep (A := {a : A & H_f a (h c)})).
    intros [a H3]. generalize (fst H_img a). apply minus1Trunc_map.
      intros [b p]. exists b. exact ((ap10 p (h c)) # H3).
    apply allpath_hprop.
    exact (H2 c).
intros [H1 H2]. split.
  intro a. apply (minus1Trunc_rect_nondep (A := {b : B & H_f a = H_g b})).
    intros [b p]. generalize (H1 b). apply minus1Trunc_map.
      intros [c H3]. exists c. exact ((ap10 p^ (h c)) # H3).
    apply allpath_hprop.
    exact (fst H_img a).
  intro c. apply (minus1Trunc_rect_nondep (A := {b : B & H_g b (h c)})).
    intros [b H3]. generalize (snd H_img b). apply minus1Trunc_map.
      intros [a p]. exists a. exact ((ap10 p^ (h c)) # H3).
    apply allpath_hprop.
    exact (H2 c).
Defined.

Notation " u ~~ v " := (bisim u v)
  (at level 30).

Lemma reflexive_bisim `{fs' : Funext} : forall u, u ~~ u.
Proof.
  refine (Vset_rect_hprop _ _ _).
  intros A f H_f; simpl. split.
    intro a; apply min1; exists a; auto.
    intro a; apply min1; exists a; auto.
Defined.

Lemma is_eq_bisim `{fs' : Funext} : forall u v : Vset, (u = v) = (u ~~ v).
Proof.
  intros u v.
  apply path_iff_hprop_uncurried; split.
  intro p; exact (transport (fun x => u ~~ x) p (reflexive_bisim u)).
  generalize u v.
  refine (Vset_rect_hprop _ _ _); intros A f H_f.
  refine (Vset_rect_hprop _ _ _); intros B g _.
  intro H; simpl in H; destruct H as [H1 H2].
  apply setext'. split.
  intro a. generalize (H1 a). apply minus1Trunc_map.
    intros [b h]. exists b; exact (H_f a (g b) h).
  intro b. generalize (H2 b). apply minus1Trunc_map.
    intros [a h]. exists a; exact (H_f a (g b) h).
Defined.


(* ** Definitions of particular sets in Vset ** *)

Definition Vempty : Vset := set (Empty_rect (fun _ => Vset)).

Definition Vsingleton (u : Vset) := set (Unit_rect u).

Definition Vpair (u : Vset) (v : Vset) := set (fun b : Bool => if b then u else v).

Definition Vpair_ord (u : Vset) (v : Vset) := Vpair u (Vpair u v).

(* Vsucc x := x ∪ {x} *)
Definition Vsucc : Vset -> Vset.
Proof.
  apply Vset_rect'_nd with (fun A f _ =>
    set (fun (x : A + Unit) => match x with inl a => f a
                                          | inr tt => set f end)).
  intros A B f g eq_img _ _ _. apply setext'. split.
    intro. destruct a.
      generalize (fst eq_img a). apply minus1Trunc_map.
        intros [b p]. exists (inl b); exact p.
      apply min1; exists (inr tt). destruct u. apply setext'; auto.
    intro. destruct b.
      generalize (snd eq_img b). apply minus1Trunc_map. 
        intros [a p]. exists (inl a); exact p.
      apply min1; exists (inr tt). destruct u. apply setext'; auto.
  exact is0trunc_vset.
Defined.

Definition omega : Vset
:= set (fix I n := match n with 0   => Vempty
                              | S n => Vsucc (I n) end).


(* ** Axioms of set theory (theorem 10.5.8) ** *)

Lemma not_mem_Vempty : forall x, ~ (x ∈ Vempty).
Proof.
  intros x Hx. apply (minus1Trunc_rect_nondep (A := {a : Empty & x = (Empty_rect (fun _ => Vset)) a})).
  intros [ff _]. exact ff.
  apply allpath_hprop.
  exact Hx.
Qed.

Lemma extensionality : forall x y : Vset, (x ⊆ y * y ⊆ x) <-> x = y.
Proof.
  refine (Vset_rect_hprop _ _ _). intros A f _.
  refine (Vset_rect_hprop _ _ _). intros B g _.
  split.
  intros [H1 H2]. apply setext'. split.
    intro. apply (H1 (f a)). apply min1. exists a; reflexivity.
    intro. apply (minus1Trunc_rect_nondep (A := {a : A & g b = f a})).
      intros [a p]. apply min1. exists a. exact p^.
      apply allpath_hprop.
      apply (H2 (g b)). apply min1. exists b; reflexivity.
  intro p; split.
    intros z Hz. apply (transport (fun x => z ∈ x) p Hz).
    intros z Hz. apply (transport (fun x => z ∈ x) p^ Hz).
Qed.

Lemma pairing : forall u v, hexists (fun w => forall x, x ∈ w <-> hor (x = u) (x = v)).
Proof.
  intros u v. apply min1. exists (Vpair u v).
  intro; split.
    apply minus1Trunc_map. intros [b p]. destruct b.
      left; assumption. right; assumption.
    apply minus1Trunc_map. intros [H | H].
      exists true; assumption. exists false; assumption.
Qed.

Lemma mem_induction (C : Vset -> hProp)
: (forall v, (forall x, x ∈ v -> C x) -> C v) -> forall v, C v.
Proof.
  intro H.
  apply Vset_rect_hprop.
  2: intro; apply isp.
  intros A f H_f. apply H. intros x Hx.
  apply (minus1Trunc_rect_nondep (A := {a : A & x = f a})).
    intros [a p]. rewrite p. apply H_f.
    apply isp.
    assumption.
Defined.

Lemma replacement : forall (r : Vset -> Vset) (x : Vset),
  hexists (fun w => forall y, y ∈ w <-> hexists (fun z => z ∈ x * (y = r z))).
Proof.
  intro r. apply Vset_rect_hprop.
  2: intro; apply minus1Trunc_is_prop.
  intros A f _. apply min1. exists (set (r ∘ f)). split.
  apply minus1Trunc_map.
    intros [a p]. exists (f a). split. apply min1; exists a; auto. assumption.
  intro H. apply (minus1Trunc_rect_nondep (A := {z : Vset & z ∈ set f * (y = r z)})).
    intros [z [h p]]. generalize h. apply minus1Trunc_map.
      intros [a p']. exists a. path_via (r z). rewrite p'; auto.
    apply allpath_hprop.
    exact H.
Qed.

Lemma separation (C : Vset -> hProp) : forall a : Vset,
  hexists (fun w => forall x, x ∈ w <-> x ∈ a * (C x)).
Proof.
  apply Vset_rect_hprop.
  2: intro; apply minus1Trunc_is_prop.
  intros A f _. apply min1. exists (set (fun z : {a : A & C (f a)} => f (pr1 z))). split.
  intro H. apply (minus1Trunc_rect_nondep (A := {z : {a : A & C (f a)} & x = f (pr1 z)})).
    intros [[a h] p]. split. apply min1; exists a; assumption. rewrite p; exact h.
    apply allpath_hprop.
    exact H.
  intros [H1 H2]. generalize H1. apply minus1Trunc_map.
    intros [a p]. exists (a; transport C p H2). exact p.
Qed.

Lemma infinity : (Vempty ∈ omega) * (forall x, x ∈ omega -> Vsucc x ∈ omega).
Proof.
  split. apply min1; exists 0; auto.
  intro. apply minus1Trunc_map.
    intros [n p]. exists (S n). rewrite p; auto.
Qed.


End AssumeAxioms.