(** Abstract Reduction Systems, from Semantics Lecture at Programming Systems Lab, https://www.ps.uni-saarland.de/courses/sem-ws13/ *)

Require Export Base.

Notation "p '<=1' q" := (forall x, p x -> q x) (at level 70).
Notation "p '=1' q" := (p <=1 q /\ q <=1 p) (at level 70).
Notation "R '<=2' S" := (forall x y, R x y -> S x y) (at level 70).
Notation "R '=2' S"  := (R <=2 S /\ S <=2 R) (at level 70).

(** Relational composition *)

Definition rcomp X Y Z (R : X -> Y -> Prop) (S : Y -> Z -> Prop) 
: X -> Z -> Prop :=
  fun x z => exists y, R x y /\ S y z.

(** Power predicates *)

Require Import Arith.
Definition pow X R n : X -> X -> Prop := it (rcomp R) n eq.

Section FixX.
  Variable X : Type.
  Implicit Types R S : X -> X -> Prop.
  Implicit Types x y z : X.

  Definition reflexive R := forall x, R x x.
  Definition symmetric R := forall x y, R x y -> R y x.
  Definition transitive R := forall x y z, R x y -> R y z -> R x z.
  Definition functional R := forall x y z, R x y -> R x z -> y = z.


  (** Reflexive transitive closure *)

  Inductive star R : X -> X -> Prop :=
  | starR x : star R x x
  | starC x y z : R x y -> star R y z -> star R x z.

  Lemma star_trans R:
    transitive (star R).
  Proof.
    induction 1; eauto using star.
  Qed.

  Lemma R_star R: R <=2 star R.
  Proof.
    eauto using star.
  Qed.

  Instance star_PO R: PreOrder (star R).
  Proof.
    constructor;repeat intro;try eapply star_trans;  now eauto using star.
  Qed.
  
  (** Power characterization *)

  Lemma star_pow R x y :
    star R x y <-> exists n, pow R n x y.
  Proof.
    split; intros A.
    - induction A as [|x x' y B _ [n IH]].
      + exists 0. reflexivity.
               + exists (S n), x'. auto.
               - destruct A as [n A].
                 revert x A. induction n; intros x A.
                 + destruct A. constructor.
                 + destruct A as [x' [A B]]. econstructor; eauto.
  Qed.

  Lemma pow_star R x y n:
    pow R n x y -> star R x y.
  Proof.
    intros A. erewrite star_pow. eauto.
  Qed.

  Lemma pow_add R n m (s t : X) : pow R (n + m) s t <-> rcomp (pow R n) (pow R m) s t.
  Proof.
    revert m s t; induction n; intros m s t.
    - simpl. split; intros. econstructor. split. unfold pow. simpl. reflexivity. eassumption.
      destruct H as [u [H1 H2]]. unfold pow in H1. simpl in *. subst s. eassumption.
    - simpl in *; split; intros.
      + destruct H as [u [H1 H2]].
        change (it (rcomp R) (n + m) eq) with (pow R (n+m)) in H2.
        rewrite IHn in H2.
        destruct H2 as [u' [A B]]. unfold pow in A.
        econstructor. 
        split. econstructor. repeat split; repeat eassumption. eassumption.
      + destruct H as [u [H1 H2]].
        destruct H1 as [u' [A B]].
        econstructor.  split. eassumption. change (it (rcomp R) (n + m) eq) with (pow R (n + m)).
        rewrite IHn. econstructor. split; eassumption.
  Qed.
  
  Lemma rcomp_1 (R : X -> X -> Prop): R =2 pow R 1.  Proof.
    split; intros s t; unfold pow in *; simpl in *; intros H.
    - econstructor. split; eauto.
    - destruct H as [u [H1 H2]]; subst u; eassumption.
  Qed.

  
End FixX.

Existing Instance star_PO.

(** A notion of a reduction sequence which keeps track of the largest occuring state *)

Inductive redWithMaxSize {X} (size:X -> nat) (step : X -> X -> Prop): nat -> X -> X -> Prop:=
  redWithMaxSizeR m s: m = size s -> redWithMaxSize size step m s s 
| redWithMaxSizeC s s' t m m': step s s' -> redWithMaxSize size step m' s' t -> m = max (size s) m' -> redWithMaxSize size step m s t.

Lemma redWithMaxSize_ge X size step (s t:X) m:
  redWithMaxSize size step m s t -> size s<= m /\ size t <= m.
Proof.
  induction 1;subst;firstorder (repeat eapply Nat.max_case_strong; try omega).
Qed.

Lemma redWithMaxSize_trans X size step (s t u:X) m1 m2 m3:
 redWithMaxSize size step m1 s t -> redWithMaxSize size step m2 t u -> max m1 m2 = m3 -> redWithMaxSize size step m3 s u.
Proof.
  induction 1 in m2,u,m3|-*;intros.
  -specialize (redWithMaxSize_ge H0) as [].
   revert H1;
     repeat eapply Nat.max_case_strong; subst m;intros. all:replace m3 with m2 by omega. all:eauto.
  - specialize (redWithMaxSize_ge H0) as [].
    specialize (redWithMaxSize_ge H2) as [].
    eassert (H1':=Max.le_max_l _ _);rewrite H3 in H1'.
    eassert (H2':=Max.le_max_r _ _);rewrite H3 in H2'.
    econstructor. eassumption.
     
    eapply IHredWithMaxSize. eassumption. reflexivity.
    subst m;revert H3;repeat eapply Nat.max_case_strong;intros;try omega. 
Qed.

