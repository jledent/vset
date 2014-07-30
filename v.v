(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about the cumulative hierarchy [V]. *)

Require Import HoTT.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables A B R f g h.


(* ** Misc. definitions & lemmas ** *)

Definition compose {A B C} (g : forall b, C b) (f : A -> B) :=
  fun x : A => g (f x).

Hint Unfold compose.

Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity).

Definition hor (P:Type) (Q:Type):Type:= minus1Trunc (P + Q).

Lemma untrunc {P : Type} : (IsHProp P) -> (minus1Trunc P) -> P.
Proof.
  intro. apply minus1Trunc_ind. exact idmap.
Defined. 

Lemma mono_cancel {A B : Type} (m : A -> B) : is_mono m -> (forall a a', m a = m a' -> a = a').
Proof.
  intros H a a' p.
  specialize (H (m a')). unfold hfiber in *.
  assert ((a; p) = (a'; 1) :> {x : A & m x = m a'}) by apply allpath_hprop.
  apply (path_sigma_uncurried (fun x => m x = m a') (a; p) (a'; 1))^-1.
  assumption.
Defined.

(* ** Pushout with respect to a relation ** *)

Module Export RPushout.

Private Inductive RPushout {A B : Type} (R : A -> B -> hProp) : Type :=
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

Module Export CumulativeHierarchy.

Private Inductive V : Type :=
| set {A : Type} (f : A -> V) : V.

Axiom setext : forall {A B : Type} (R : A -> B -> hProp)
  (bitot_R : Bitot R) (h : RPushout R -> V),
set (h o (inL R)) = set (h o (inR R)).

Axiom is0trunc_V : IsTrunc 0 V.

Definition V_rect (P : V -> Type)
  (H_set : forall (A : Type) (f : A -> V) (H_f : forall a : A, P (f a)), P (set f))
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R)
    (h : RPushout R -> V) (H_h : forall x : RPushout R, P (h x)),
    (setext R bitot_R h) # (H_set A (h ∘ inL R) (H_h ∘ inL R))
      = H_set B (h ∘ inR R) (H_h ∘ inR R) )
  (H_0trunc : forall v : V, IsTrunc 0 (P v))
: forall v : V, P v
:= fix F (v : V) :=
     (match v with
      | set A f => fun _ _ => H_set A f (fun a => F (f a))
     end) H_setext H_0trunc.

Axiom V_comp_setext : forall (P : V -> Type)
  (H_set : forall (A : Type) (f : A -> V) (H_f : forall a : A, P (f a)), P (set f))
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R)
    (h : RPushout R -> V) (H_h : forall x : RPushout R, P (h x)),
    (setext R bitot_R h) # (H_set A (h ∘ inL R) (H_h ∘ inL R))
      = H_set B (h ∘ inR R) (H_h ∘ inR R) )
  (H_0trunc : forall v : V, IsTrunc 0 (P v))
  (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R) (h : RPushout R -> V),
apD (V_rect P H_set H_setext H_0trunc) (setext R bitot_R h)
= H_setext A B R bitot_R h ((V_rect P H_set H_setext H_0trunc) ∘ h).

End CumulativeHierarchy.


(* ** The non-dependent eliminator ** *)

Definition V_rect_nd (P : Type)
  (H_set : forall (A : Type), (A -> V) -> (A -> P) -> P)
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R)
    (h : RPushout R -> V) (H_h : RPushout R -> P),
    H_set A (h ∘ inL R) (H_h ∘ inL R) = H_set B (h ∘ inR R) (H_h ∘ inR R) )
  (H_0trunc : IsTrunc 0 P)
: V -> P.
Proof.
  apply (V_rect (fun _ => P) H_set).
  intros. exact (transport_const _ _ @ H_setext A B R bitot_R h H_h).
  intro; assumption.
Defined.

Definition V_comp_nd_setext (P : Type)
  (H_set : forall (A : Type), (A -> V) -> (A -> P) -> P)
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R)
    (h : RPushout R -> V) (H_h : RPushout R -> P),
    H_set A (h ∘ inL R) (H_h ∘ inL R) = H_set B (h ∘ inR R) (H_h ∘ inR R) )
  (H_0trunc : IsTrunc 0 P)
  (A B : Type) (R : A -> B -> hProp) (bitot_R : Bitot R) (h : RPushout R -> V)
: ap (V_rect_nd P H_set H_setext H_0trunc) (setext R bitot_R h)
  = H_setext A B R bitot_R h ((V_rect_nd P H_set H_setext H_0trunc) ∘ h).
Proof.
(* We might want to fill-in the blank in transport_const next line *)
  apply (cancelL (transport_const (setext R bitot_R h) _)).
  path_via (apD (V_rect_nd P H_set H_setext H_0trunc) (setext R bitot_R h)).
  symmetry; refine (apD_const (V_rect_nd P H_set H_setext H_0trunc) _).
  refine (V_comp_setext (fun _ => P) _ _ _ _ _ _ _ _).
Defined.


(* ** Alternative induction principle (This is close to the one from the book) ** *)

Definition Equal_img {A B C : Type} (f : A -> C) (g : B -> C) :=
   (forall a : A, hexists (fun (b : B) => f a = g b))
 * (forall b : B, hexists (fun (a : A) => f a = g b)).

Let setext' {A B : Type} (f : A -> V) (g : B -> V) (eq_img : Equal_img f g)
: set f = set g.
Proof.
  pose (R := fun a b => hp (f a = g b) _).
  pose (h := RPushout_rect_nd R V f g (fun _ _ r => r)).
  exact (setext R eq_img h).
Defined.

Definition V_rect'_nd (P : Type)
  (H_set : forall (A : Type), (A -> V) -> (A -> P) -> P)
  (H_setext' : forall (A B : Type) (f : A -> V) (g : B -> V), (Equal_img f g) ->
    forall (H_f : A -> P) (H_g : B -> P), (Equal_img H_f H_g) ->
    (H_set A f H_f) = (H_set B g H_g) )
  (H_0trunc : IsTrunc 0 P)
: V -> P.
Proof.
  refine (V_rect_nd P H_set _ H_0trunc).
  intros A B R bitot_R h H_h.
  apply H_setext'.
  - split.
    + intro a. generalize (fst bitot_R a). apply minus1Trunc_map.
      intros [b r]. exists b. exact (ap h (glue R _ _ r)).
    + intro b. generalize (snd bitot_R b). apply minus1Trunc_map.
      intros [a r]. exists a. exact (ap h (glue R _ _ r)).
  - split.
    + intro a. generalize (fst bitot_R a). apply minus1Trunc_map.
      intros [b r]. exists b. exact (ap H_h (glue R _ _ r)).
    + intro b. generalize (snd bitot_R b). apply minus1Trunc_map.
      intros [a r]. exists a. exact (ap H_h (glue R _ _ r)).
Defined.

(* We might also want to prove the associated computation rules *)
(* Note that the hypothesis H_setext' differs from the one given in section 10.5 of the HoTT book. *)
Definition V_rect' (P : V -> Type)
  (H_0trunc : forall v : V, IsTrunc 0 (P v))
  (H_set : forall (A : Type) (f : A -> V) (H_f : forall a : A, P (f a)), P (set f))
  (H_setext' : forall (A B : Type) (f : A -> V) (g : B -> V)
    (eq_img: Equal_img f g)
    (H_f : forall a : A, P (f a)) (H_g : forall b : B, P (g b)),
    ((forall a : A, hexists (fun (b : B) =>
         hexists (fun (p:f a = g b) => p # (H_f a)=H_g b)))
   * (forall b : B, hexists (fun (a : A) =>
         hexists (fun (p:f a = g b) => p# (H_f a)=H_g b))) ->
    (setext' f g eq_img) # (H_set A f H_f) = (H_set B g H_g) ))
: forall v : V, P v.
Proof.
  apply V_rect with H_set; try assumption.
  intros A B R bitot_R h H_h.
  pose (f := h ∘ inL R : A -> V ).
  pose (g := h ∘ inR R : B -> V ).
  pose (H_f := H_h ∘ inL R : forall a : A, P (f a)).
  pose (H_g := H_h ∘ inR R : forall b : B, P (g b)).
  assert (eq_img : Equal_img f g). split.
    intro a. generalize (fst bitot_R a). apply minus1Trunc_map.
      intros [b r]. exists b. exact (ap h (glue R _ _ r)).
    intro b. generalize (snd bitot_R b). apply minus1Trunc_map.
      intros [a r]. exists a. exact (ap h (glue R _ _ r)).
  path_via (transport P (setext' (h ∘ inL R) (h ∘ inR R) eq_img)
                (H_set A (h ∘ inL R) (H_h ∘ inL R))).
    apply (ap (fun p => transport P p (H_set A (h ∘ inL R) (H_h ∘ inL R)))).
    apply allpath_hprop.
  apply (H_setext' A B f g eq_img H_f H_g).  split.
  - intro a.
    set (truncb := fst bitot_R a). generalize truncb.
    apply minus1Trunc_map.
    intros [b Rab]. exists b.
    apply min1.
    exists (ap h (glue R _ _ Rab)).
    apply (concatR (apD H_h (glue R _ _ Rab))).
    apply inverse. unfold f, g, compose. apply transport_compose.
  - intros b.
    set (trunca := snd bitot_R b). generalize trunca.
    apply minus1Trunc_map.
    intros [a Rab]. exists a.
    apply min1.
    exists (ap h (glue R _ _ Rab)).
    apply (concatR (apD H_h (glue R _ _ Rab))).
    apply inverse. unfold f, g, compose. apply transport_compose.
Defined.


(* ** Simpler induction principle when the goal is an hprop ** *)

Definition V_rect_hprop (P : V -> Type)
  (H_set : forall (A : Type) (f : A -> V) (H_f : forall a : A, P (f a)), P (set f))
  (isHProp_P : forall v : V, IsHProp (P v))
  : forall v : V, P v.
Proof.
  apply V_rect with H_set.
  intros. apply allpath_hprop.
  intro. apply trunc_succ.
Defined.


Section AssumingUA.
Context `{ua : Univalence}.

(* ** Membership relation ** *)

Definition mem (x : V) : V -> hProp.
Proof.
  apply V_rect'_nd with (fun A f _ => hp (hexists (fun a : A => f a = x)) _).
  2: exact isset_hProp.
  intros. apply path_iff_hProp_uncurried. split.
  - intro H. apply (minus1Trunc_rect_nondep (A := {a : A & f a = x})).
      intros [a p]. generalize (fst X a). apply minus1Trunc_map.
        intros [b p']. exists b. path_via (f a).
      apply allpath_hprop.
      exact H.
  - intro H. apply (minus1Trunc_rect_nondep (A := {b : B & g b = x})).
      intros [b p]. generalize (snd X b). apply minus1Trunc_map.
        intros [a p']. exists a. path_via (g b).
      apply allpath_hprop.
      exact H.
Defined.

Notation " x ∈ v " := (mem x v)
  (at level 30).


(* ** Subset relation ** *)

Definition subset (x : V) (y : V) : hProp
:= hp (forall z : V, z ∈ x -> z ∈ y) _.

Notation " x ⊆ y " := (subset x y)
  (at level 30).


(* This lemma might be useful *)
Lemma path_V_eqimg {A B} {f : A -> V} {g : B -> V} : set f = set g -> Equal_img f g.
Proof.
  intro p. split.
  - intro a.
    assert (H : f a ∈ set f). apply min1; exists a; reflexivity.
    generalize (transport (fun x => f a ∈ x) p H). apply minus1Trunc_map.
    intros [b p']. exists b; exact p'^.
  - intro b.
    assert (H : g b ∈ set g). apply min1; exists b; reflexivity.
    generalize (transport (fun x => g b ∈ x) p^ H). apply minus1Trunc_map.
    intros [a p']. exists a; exact p'.
Defined.


(* ** Bisimulation relation ** *)

Definition bisimulation : V -> V -> hProp.
Proof.
  (* We first fix the first argument as set(A,f) and define bisim_aux : V -> hProp, by induction. This is the inner of the two inductions. *)
  Definition bisim_aux (A : Type) (f : A -> V) (H_f : A -> V -> hProp) : (V -> hProp).
  apply V_rect'_nd with
    (fun B g _ => hp ( (forall a, hexists (fun b => H_f a (g b)))
                      * forall b, hexists (fun a => H_f a (g b)) ) _
    ).
  2: apply isset_hProp.
  intros B B' g g' eq_img H_g H_g' H_img; simpl.
  apply path_iff_hProp_uncurried. split.
  - intros [H1 H2]; split.
    + intro a. apply (minus1Trunc_rect_nondep (A := {b : B & H_f a (g b)})).
        intros [b H3]. generalize (fst eq_img b). apply minus1Trunc_map.
          intros [b' p]. exists b'. exact (transport (fun x => H_f a x) p H3).
        apply allpath_hprop.
        exact (H1 a).
    + intro b'. apply (minus1Trunc_rect_nondep (A := {b : B & g b = g' b'})).
        intros [b p]. generalize (H2 b). apply minus1Trunc_map.
          intros [a H3]. exists a. exact (transport (fun x => H_f a x) p H3).
        apply allpath_hprop.
        exact (snd eq_img b').
  - intros [H1 H2]; split.
    + intro a. apply (minus1Trunc_rect_nondep (A := {b' : B' & H_f a (g' b')})).
        intros [b' H3]. generalize (snd eq_img b'). apply minus1Trunc_map.
          intros [b p]. exists b. exact (transport (fun x => H_f a x) p^ H3).
        apply allpath_hprop.
        exact (H1 a).
    + intro b. apply (minus1Trunc_rect_nondep (A := {b' : B' & g b = g' b'})).
        intros [b' p]. generalize (H2 b'). apply minus1Trunc_map.
          intros [a H3]. exists a. exact (transport (fun x => H_f a x) p^ H3).
        apply allpath_hprop.
        exact (fst eq_img b).
  Defined.

(* Then define bisim : V -> (V -> hProp) by induction again *)
refine (V_rect'_nd (V -> hProp) bisim_aux _ _).
intros A B f g eq_img H_f H_g H_img.
apply path_forall.
refine (V_rect_hprop _ _ _).
intros C h _; simpl.
apply path_iff_hProp_uncurried. split.
- intros [H1 H2]; split.
  + intro b. apply (minus1Trunc_rect_nondep (A := {a : A & H_f a = H_g b})).
      intros [a p]. generalize (H1 a). apply minus1Trunc_map.
        intros [c H3]. exists c. exact ((ap10 p (h c)) # H3).
      apply allpath_hprop.
      exact (snd H_img b).
  + intro c. apply (minus1Trunc_rect_nondep (A := {a : A & H_f a (h c)})).
      intros [a H3]. generalize (fst H_img a). apply minus1Trunc_map.
        intros [b p]. exists b. exact ((ap10 p (h c)) # H3).
      apply allpath_hprop.
      exact (H2 c).
- intros [H1 H2]; split.
  + intro a. apply (minus1Trunc_rect_nondep (A := {b : B & H_f a = H_g b})).
      intros [b p]. generalize (H1 b). apply minus1Trunc_map.
        intros [c H3]. exists c. exact ((ap10 p^ (h c)) # H3).
      apply allpath_hprop.
      exact (fst H_img a).
  + intro c. apply (minus1Trunc_rect_nondep (A := {b : B & H_g b (h c)})).
      intros [b H3]. generalize (snd H_img b). apply minus1Trunc_map.
        intros [a p]. exists a. exact ((ap10 p^ (h c)) # H3).
      apply allpath_hprop.
      exact (H2 c).
Defined.

Notation " u ~~ v " := (bisimulation u v)
  (at level 30).

Lemma reflexive_bisim : forall u, u ~~ u.
Proof.
  refine (V_rect_hprop _ _ _).
  intros A f H_f; simpl. split.
    intro a; apply min1; exists a; auto.
    intro a; apply min1; exists a; auto.
Defined.

Lemma BisimEqualsId : forall u v : V, (u = v) = (u ~~ v).
Proof.
  intros u v.
(*  apply path_iff_hprop_uncurried; split.
  intro p; exact (transport (fun x => u ~~ x) p (reflexive_bisim u)).
  generalize u v.
  refine (V_rect_hprop _ _ _); intros A f H_f.
  refine (V_rect_hprop _ _ _); intros B g _.
  intro H; simpl in H; destruct H as [H1 H2].
  apply setext'. split.
  - intro a. generalize (H1 a). apply minus1Trunc_map.
    intros [b h]. exists b; exact (H_f a (g b) h).
  - intro b. generalize (H2 b). apply minus1Trunc_map.
    intros [a h]. exists a; exact (H_f a (g b) h).*)
Admitted.


(* ** Canonical presentation of V-sets (Lemma 10.5.6) ** *)

Definition hfiber_bisim {A : Type} (f : A -> V) (y : V) := { x : A & f x ~~ y }.

Lemma inj_surj_factor_V {A : Type} (f : A -> V)
: exists (C : Type) (e : A -> C) (m : C -> V), IsHSet C * is_epi e * is_mono m * (f = m ∘ e).
Proof.
  pose (imf := {u : V & minus1Trunc (hfiber_bisim f u)}).
  exists imf.
  pose (e := fun a => (f a; min1 (a; (reflexive_bisim (f a)))) : imf).
  exists e.
  exists pr1.
  split. split. split.
  - intros [u Hu] [v Hv]. apply (trunc_equiv' (A := u = v)).
    equiv_via {p : u = v & transport (fun x => minus1Trunc (hfiber_bisim f x)) p Hu = Hv}.
      apply equiv_inverse. refine (BuildEquiv _ _ pr1 _).
      refine (BuildEquiv _ _ (path_sigma_uncurried _ (u; Hu) (v; Hv)) _).
    apply istrunc_paths. apply is0trunc_V.
  - unfold is_epi. intros [u H].
    generalize H; apply minus1Trunc_map_dep; intros [a p].
    exists a. unfold e; simpl.
    apply path_sigma_uncurried; simpl.
    exists (transport (fun X : Type => X) (BisimEqualsId (f a) u)^ p). apply allpath_hprop.
  - unfold is_mono. intro u.
    apply hprop_allpath. intros [[v Hv] p] [[v' Hv'] p']. simpl in *.
    apply path_sigma_uncurried; simpl.
    assert ((v; Hv) = (v'; Hv') :> imf).
      apply path_sigma_uncurried; simpl. exists (p @ p'^). apply allpath_hprop.
    exists X. apply allpath_hprop.
  - apply path_forall. intro a. reflexivity.
Defined.


Section MonicSetPresent_Unique.
(* Given u : V, we want to show that the representation u = @set Au mu, where Au is an hSet and mu is monic, is unique. *)

Context {u : V} {Au Au': Type} {h : IsHSet Au} {h' : IsHSet Au'} {mu : Au -> V} {mono : is_mono mu}
  {mu' : Au' -> V} {mono' : is_mono mu'} {p : u = set mu} {p' : u = set mu'}.

Lemma eq_img_untrunc : (forall a : Au, {a' : Au' & mu' a' = mu a})
                     * (forall a' : Au', {a : Au & mu a = mu' a'}).
Proof.
  split.
  intro a. exact (untrunc (mono' (mu a)) (transport (fun x => mu a ∈ x) (p^ @ p') (min1 (a; 1)))).
  intro a'. exact (untrunc (mono (mu' a')) (transport (fun x => mu' a' ∈ x) (p'^ @ p) (min1 (a'; 1)))).
Defined.

Let e : Au -> Au' := fun a => pr1 (fst eq_img_untrunc a).
Let inv_e : Au' -> Au := fun a' => pr1 (snd eq_img_untrunc a').

Definition hom1 : Sect inv_e e.
Proof.
  intro a'.
  apply (mono_cancel mu' mono').
  path_via (mu (inv_e a')).
  exact (pr2 (fst eq_img_untrunc (inv_e a'))).
  exact (pr2 (snd eq_img_untrunc a')).
Defined.

Definition hom2 : Sect e inv_e.
Proof.
  intro a.
  apply (mono_cancel mu mono).
  path_via (mu' (e a)).
  exact (pr2 (snd eq_img_untrunc (e a))).
  exact (pr2 (fst eq_img_untrunc a)).
Defined.

Lemma path : Au' = Au.
Proof.
  apply path_universe_uncurried.
  apply (equiv_adjointify inv_e e hom2 hom1).
Defined.

Lemma mu_eq_mu' : transport (fun A : Type => A -> V) path^ mu = mu'.
Proof.
  apply path_forall. intro a'.
  path_via (transport (fun X => V) path^ (mu (transport (fun X : Type => X) path^^ a'))).
  apply (@transport_arrow Type (fun X : Type => X) (fun X => V) Au Au' path^ mu a').
  path_via (mu (transport idmap path^^ a')).
  apply transport_const.
  path_via (mu (inv_e a')).
  2: apply (pr2 (snd eq_img_untrunc a')).
  refine (ap mu _).
  path_via (transport idmap path a').
  exact (ap (fun x => transport idmap x a') (inv_V path)).
  apply transport_path_universe.
Defined.

Lemma set_mono_uniqueness : (Au; (mu; (h, mono, p))) = (Au'; (mu'; (h', mono', p'))) :> {A : Type & {m : A -> V & IsHSet A * is_mono m * (u = set m)}}.
Proof.
  apply path_sigma_uncurried; simpl.
  exists path^.
  path_via (path^ # mu; transportD (fun A => A -> V) (fun A m => IsHSet A * is_mono m * (u = set m)) path^ mu (h, mono, p)).
  apply (@transport_sigma Type (fun A => A -> V) (fun A m => IsHSet A * is_mono m * (u = set m)) Au Au' path^ (mu; (h, mono, p))).
  apply path_sigma_uncurried; simpl.
  exists mu_eq_mu'.
  apply allpath_hprop.
Defined.

End MonicSetPresent_Unique.

(* This lemma actually says a little more than 10.5.6, i.e., that Au is a hSet *)
Lemma MonicSetPresent : forall u, exists (Au : Type) (m : Au -> V),
  (IsHSet Au) * (is_mono m) * (u = set m).
Proof.
  apply V_rect_hprop.
  - intros A f _.
    destruct (inj_surj_factor_V f) as [Au [eu [mu (((hset_Au, epi_eu), mono_mu), factor)]]].
(*    exists Au, mu. split. exact (hset_Au, mono_mu).
    apply setext'; split.
    + intro a. apply min1; exists (eu a). exact (ap10 factor a).
    + intro a'. generalize (epi_eu a'). apply minus1Trunc_map.
      intros [a p]. exists a. path_via (mu (eu a)).
      exact (ap10 factor a). exact (ap mu p). 
  - intro v. apply hprop_allpath.
    intros [Au [mu ((hset, mono), p)]].
    intros [Au' [mu' ((hset', mono'), p')]].
    apply set_mono_uniqueness.*)
Admitted.

Definition TypeOfMembers (u : V) : Type := pr1 (MonicSetPresent u).

Notation " [ u ] " := (TypeOfMembers u)
  (at level 20).

Definition FuncOfMembers {u : V} : [u] -> V := pr1 (pr2 (MonicSetPresent u)) : [u] -> V.

Definition is_hset_TypeOfMembers {u : V} : IsHSet ([u]) := fst (fst (pr2 (pr2 (MonicSetPresent u)))).

Definition is_mono_FuncOfMembers {u : V} : is_mono FuncOfMembers := snd (fst (pr2 (pr2 (MonicSetPresent u)))).

Definition is_valid_presentation (u : V) : u = set FuncOfMembers := snd (pr2 (pr2 (MonicSetPresent u))).


(* ** Definitions of particular sets in V ** *)

(* The empty set *)
Definition V_empty : V := set (Empty_rect (fun _ => V)).

(* The singleton {u} *)
Definition V_singleton (u : V) := set (Unit_rect u).

(* The pair {u,v} *)
Definition V_pair (u : V) (v : V) := set (fun b : Bool => if b then u else v).

Lemma path_pair {u v u' v' : V} : (u = u') * (v = v') -> V_pair u v = V_pair u' v'.
Proof.
  intros (H1, H2). apply setext'. split.
  + apply Bool_rect. apply min1; exists true. assumption.
    apply min1; exists false; assumption.
  + apply Bool_rect. apply min1; exists true; assumption.
    apply min1; exists false; assumption.
Defined.

(* The ordered pair (u,v) *)
Definition V_pair_ord (u : V) (v : V) := V_pair u (V_pair u v).

Notation " [ u , v ] " := (V_pair_ord u v)
  (at level 20).

Lemma path_pair_ord {a b a' b' : V} : [a, b] = [a', b'] <-> (a = a') * (b = b').
Proof.
split.
- intro H. admit. (* TODO *)
- intros (H1, H2). apply path_pair. split. assumption.
  apply path_pair. split; assumption; assumption.
Defined.

(* The cartesian product a × b *)
Definition V_cart_prod (a : V) (b : V) : V
:= set (fun x : [a] * [b] => [FuncOfMembers (fst x), FuncOfMembers (snd x)]).

(* Previous version without using the member type [-] :
Definition V_cart_prod : V -> V -> V.
  Definition V_cart_prod_aux (A : Type) (f : A -> V) (H_f : A -> V -> V) : V -> V.
  apply V_rect'_nd with (fun B g _ => 
    set (fun (x : A * B) => [f (fst x), g (snd x)] ) ).
  2: exact is0trunc_V.
  intros B B' g g' eq_img _ _ _.
  apply setext'; split.
  - intros (a, b). generalize (fst eq_img b). apply minus1Trunc_map.
    intros [b' p]. exists (a, b'). simpl.
    exact (ap (fun x => [f a, x]) p).
  - intros (a, b'). generalize (snd eq_img b'). apply minus1Trunc_map.
    intros [b p]. exists (a, b). simpl.
    exact (ap (fun x => [f a, x]) p).
  Defined.
refine (V_rect'_nd (V -> V) V_cart_prod_aux _ _).
intros A B f g eq_img H_f H_g _.
apply (Funext_implies_NaiveFunext fs).
apply V_rect_hprop.
2: intro; apply istrunc_paths; apply is0trunc_V.
intros C h _; simpl.
apply setext'; split.
- intros (a,c). generalize (fst eq_img a). apply minus1Trunc_map.
  intros [b p]. exists (b, c). simpl.
  exact (ap (fun x => [x, h c]) p).
- intros (b,c). generalize (snd eq_img b). apply minus1Trunc_map.
  intros [a p]. exists (a, c). simpl.
  exact (ap (fun x => [x, h c]) p).
Defined.
*)

Notation " a × b " := (V_cart_prod a b)
  (at level 25).

(* f is a function with domain a and codomain b *)
Definition V_is_func (a : V) (b : V) (f : V) := f ⊆ a × b
 * (forall x, x ∈ a -> hexists (fun y => y ∈ b * [x,y] ∈ f))
 * (forall x y y', [x,y] ∈ f * [x,y'] ∈ f -> y = y').

(* The set of functions from a to b *)
Definition V_func (a : V) (b : V) : V
:= @set ([a] -> [b]) (fun f => set (fun x => [FuncOfMembers x, FuncOfMembers (f x)] )).

(* The ordinal successor x ∪ {x} *)
Definition V_succ : V -> V.
Proof.
  apply V_rect'_nd with (fun A f _ =>
    set (fun (x : A + Unit) => match x with inl a => f a
                                          | inr tt => set f end)).
  2: exact is0trunc_V.
  intros A B f g eq_img _ _ _. apply setext'. split.
    - intro. destruct a.
      + generalize (fst eq_img a). apply minus1Trunc_map.
        intros [b p]. exists (inl b); exact p.
      + apply min1; exists (inr tt). destruct u. apply setext'; auto.
    - intro. destruct b.
      + generalize (snd eq_img b). apply minus1Trunc_map. 
        intros [a p]. exists (inl a); exact p.
      + apply min1; exists (inr tt). destruct u. apply setext'; auto.
Defined.

(* The set of finite ordinals *) 
Definition V_omega : V
:= set (fix I n := match n with 0   => V_empty
                              | S n => V_succ (I n) end).


(* ** Axioms of set theory (theorem 10.5.8) ** *)

Lemma not_mem_Vempty : forall x, ~ (x ∈ V_empty).
Proof.
  intros x Hx. generalize Hx; apply minus1Trunc_ind.
  intros [ff _]. exact ff.
Qed.

Lemma extensionality : forall x y : V, (x ⊆ y * y ⊆ x) <-> x = y.
Proof.
  refine (V_rect_hprop _ _ _). intros A f _.
  refine (V_rect_hprop _ _ _). intros B g _.
  split.
  - intros [H1 H2]. apply setext'. split.
    intro. apply (minus1Trunc_rect_nondep (A := {b : B & g b = f a})).
      intros [b p]. apply min1. exists b. exact p^.
      apply allpath_hprop.
      apply (H1 (f a)). apply min1. exists a; reflexivity.
    intro. apply (H2 (g b)). apply min1. exists b; reflexivity.
  - intro p; split.
    intros z Hz. apply (transport (fun x => z ∈ x) p Hz).
    intros z Hz. apply (transport (fun x => z ∈ x) p^ Hz).
Qed.

Lemma pairing : forall u v, hexists (fun w => forall x, x ∈ w <-> hor (x = u) (x = v)).
Proof.
  intros u v. apply min1. exists (V_pair u v).
  intro; split.
  - apply minus1Trunc_map. intros [b p]. destruct b.
    left; exact p^. right; exact p^.
  - apply minus1Trunc_map. intros [p | p].
    exists true; exact p^. exists false; exact p^.
Qed.

Lemma infinity : (V_empty ∈ V_omega) * (forall x, x ∈ V_omega -> V_succ x ∈ V_omega).
Proof.
  split. apply min1; exists 0; auto.
  intro. apply minus1Trunc_map.
  intros [n p]. exists (S n). rewrite p; auto.
Qed.

(* TODO : Union *)

Lemma function : forall u v, hexists (fun w => forall x, x ∈ w <-> V_is_func u v x).
Proof.
  intros u v. apply min1; exists (V_func u v).
  assert (memb_u : u = set (@FuncOfMembers u)) by exact (is_valid_presentation u).
  assert (memb_v : v = set (@FuncOfMembers v)) by exact (is_valid_presentation v).
  intro phi; split.
  - intro H. split. split.
    + intros z Hz. simpl in *. generalize H. apply minus1Trunc_ind.
      intros [h p_phi]. generalize (transport (fun x => z ∈ x) p_phi^ Hz). apply minus1Trunc_map.
      intros [a p]. exists (a, h a). assumption.
    + intros x Hx. generalize (transport (fun y => x ∈ y) memb_u Hx).
      apply minus1Trunc_ind. intros [a p]. generalize H; apply minus1Trunc_map.
      intros [h p_phi]. exists (FuncOfMembers (h a)). split.
      exact (transport (fun z => FuncOfMembers (h a) ∈ z) memb_v^ (min1 (h a; 1))).
      apply (transport (fun y => [x, FuncOfMembers (h a)] ∈ y) p_phi).
      apply min1; exists a. rewrite p; reflexivity.
    + intros x y y' (Hy, Hy'). generalize H; apply minus1Trunc_ind. intros [h p_phi].
      generalize (transport (fun z => [x, y] ∈ z) p_phi^ Hy). apply minus1Trunc_ind. intros [a p].
      generalize (transport (fun z => [x, y'] ∈ z) p_phi^ Hy'). apply minus1Trunc_ind. intros [a' p'].
      destruct (fst path_pair_ord p) as (px, py). destruct (fst path_pair_ord p') as (px', py').
      path_via (FuncOfMembers (h a)). path_via (FuncOfMembers (h a')).
      refine (ap FuncOfMembers _). refine (ap h _).
      apply (mono_cancel FuncOfMembers is_mono_FuncOfMembers a a' (px @ px'^)).
  - intros ((H1, H2), H3). simpl.
    assert (h : forall a : [u], {b : [v] & [FuncOfMembers a, FuncOfMembers b] ∈ phi}).
    + intro a. pose (x := FuncOfMembers a).
      refine (let H := untrunc _ (H2 x (transport (fun z => x ∈ z) memb_u^ (min1 (a; 1)))) in _).
        apply hprop_allpath. intros [y (H1_y, H2_y)] [y' (H1_y', H2_y')].
        apply path_sigma_uncurried; simpl.
        exists (H3 x y y' (H2_y, H2_y')).
        apply allpath_hprop.
      destruct H as [y (H1_y, H2_y)].
      destruct (untrunc (is_mono_FuncOfMembers y) (transport (fun z => y ∈ z) memb_v H1_y)) as [b Hb].
      exists b. exact (transport (fun z => [x, z] ∈ phi) Hb^ H2_y).
    + apply min1; exists (fun a => pr1 (h a)). apply extensionality. split.
      intros z Hz. generalize Hz; apply minus1Trunc_ind. intros [a Ha].
        exact (transport (fun w => w ∈ phi) Ha (pr2 (h a))).
      intros z Hz. simpl.
      generalize (H1 z Hz). apply minus1Trunc_map. intros [(a,b) p]. simpl in p.
      exists a. path_via ([FuncOfMembers a, FuncOfMembers b]).
      apply path_pair_ord. split. reflexivity.
      apply H3 with (FuncOfMembers a). split.
      exact (pr2 (h a)).
      exact (transport (fun w => w ∈ phi) p^ Hz).
Qed.

Lemma mem_induction (C : V -> hProp)
: (forall v, (forall x, x ∈ v -> C x) -> C v) -> forall v, C v.
Proof.
  intro H.
  apply V_rect_hprop.
  2: intro; apply isp.
  intros A f H_f. apply H. intros x Hx.
  generalize Hx; apply minus1Trunc_ind.
  intros [a p]. exact (transport C p (H_f a)).
Defined.

Lemma replacement : forall (r : V -> V) (x : V),
  hexists (fun w => forall y, y ∈ w <-> hexists (fun z => z ∈ x * (r z = y))).
Proof.
  intro r. apply V_rect_hprop.
  2: intro; apply minus1Trunc_is_prop.
  intros A f _. apply min1. exists (set (r ∘ f)). split.
  - apply minus1Trunc_map.
    intros [a p]. exists (f a). split. apply min1; exists a; auto. assumption.
  - apply minus1Trunc_ind.
    intros [z [h p]]. generalize h. apply minus1Trunc_map.
    intros [a p']. exists a. path_via (r z). exact (ap r p').
Qed.

Lemma separation (C : V -> hProp) : forall a : V,
  hexists (fun w => forall x, x ∈ w <-> x ∈ a * (C x)).
Proof.
  apply V_rect_hprop.
  2: intro; apply minus1Trunc_is_prop.
  intros A f _. apply min1. exists (set (fun z : {a : A & C (f a)} => f (pr1 z))). split.
  - apply minus1Trunc_ind.
    intros [[a h] p]. split. apply min1; exists a; assumption. exact (transport C p h).
  - intros [H1 H2]. generalize H1. apply minus1Trunc_map.
      intros [a p]. exists (a; transport C p^ H2). exact p.
Qed.

End AssumingUA.
