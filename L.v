Require Export ARS.
Require Export Prelims Base. (* Shared.Extra.Bijection. *)

Hint Constructors ARS.star : cbv.

(** * L: Weak Call-by-value Lambda Calculus*)

Inductive term : Type :=
| var (n : nat) : term
| app (s : term) (t : term) : term
| lam (s : term).

Coercion app : term >-> Funclass. 
Coercion var : nat >-> term.

Notation "(λ  s )" := (lam s) (right associativity, at level 0). 

Instance term_eq_dec : eq_dec term.
Proof.
  intros s t; unfold dec; repeat decide equality.
Defined.

Fixpoint size s :nat :=
  match s with
    var x => 1 + x
  | lam s => 1 +(size s)
  | app s t => 1 + size s + size t
  end.

(** ** Substitution and Closedness *)

Fixpoint subst (s : term) (k : nat) (u : term) :=
  match s with
      | var n => if Dec (n = k) then u else (var n)
      | app s t => app (subst s k u) (subst t k u)
      | lam s => lam (subst s (S k) u)
  end.

Inductive bound : nat -> term -> Prop :=
  | bndvar k n : k > n -> bound k (var n)
  | bndApp k s t : bound k s -> bound k t -> bound k (s t)
  | bndlam k s : bound (S k) s -> bound k (lam s).
Hint Constructors bound.

Definition closed s:= bound 0 s.

Hint Unfold closed. 

Definition lambda s := exists t, s = lam t.

Lemma lambda_lam s : lambda (lam s).
Proof.
  exists s; reflexivity.
Qed.

Hint Resolve lambda_lam.

Lemma bound_closed_k s k u : bound k s -> subst s k u = s.
Proof with eauto.
  intros H; revert u; induction H; intros u; simpl.
  - decide (n = k)... omega.
  - rewrite IHbound1, IHbound2...
  - f_equal...
Qed.

Lemma bound_ge k s : bound k s -> forall m, m >= k -> bound m s.
Proof.
  induction 1; intros m Hmk; econstructor; eauto. 
  - omega.
  - eapply IHbound. omega.
Qed.

Lemma bound_closed s k u : bound 0 s -> subst s k u = s.
Proof.
  intros H. destruct k.
  - eapply bound_closed_k. eassumption.
  - eapply bound_ge in H. eapply bound_closed_k. eassumption. omega.
Qed.

Lemma closed_k_bound k s : (forall n u, n >= k -> subst s n u = s) -> bound k s.
Proof.
  revert k. induction s; intros k H.
  - econstructor. specialize (H n (S n)). simpl in H.
    decide (n >= k) as [Heq | Heq].
    + decide (n = n) ; [injection (H Heq)|]; omega. 
    + omega.
  - econstructor; [eapply IHs1 | eapply IHs2]; intros n u Hnk;
    injection (H n u Hnk); congruence.
  - econstructor. eapply IHs. intros n u Hnk.
    destruct n. omega.
    injection (H n u). tauto. omega.
Qed.

Lemma closed_subst_iff s : closed s <-> (forall k t, subst s k t = s).
Proof.
  split.
  -intros. rewrite bound_closed_k. tauto. eapply bound_ge;eauto. omega. 
  -intros. apply closed_k_bound. eauto.
Qed.

Lemma closed_subst s : closed s -> (forall k t, subst s k t = s).
Proof.
  apply closed_subst_iff.
Qed.


Lemma closed_app (s t : term) : closed (s t) -> closed s /\ closed t.
Proof.
  intros H. now inv H.
Qed.

Lemma app_closed (s t : term) : closed s -> closed t -> closed (s t).
Proof.
  unfold closed. eauto using bound. 
Qed.

Lemma bound_subst s t k : bound (S k) s -> bound k t -> bound k (subst s k t).
Proof.
  revert k t; induction s; intros k t cls_s cls_t; simpl; inv cls_s; eauto 6 using bound, bound_ge.
  decide (n = k); eauto. econstructor.  omega.
Qed.

Lemma closed_subst2 s t: closed (lam s) -> closed t -> closed (subst s 0 t).
Proof.
  intros cs ct. inv cs.  now apply bound_subst.
Qed.

(** ** Deterministic Reduction *)

Reserved Notation "s '>>' t" (at level 50).

Inductive step : term -> term -> Prop :=
| stepApp  s t     : app (lam s) (lam t) >> subst s 0 (lam t)
| stepAppR s t  t' : t >> t' -> app (lam s) t >> app (lam s) t'
| stepAppL s s' t  : s >> s' -> app s t >> app s' t
where "s '>>' t" := (step s t).
Hint Constructors step.

Ltac inv_step :=
  match goal with
    | H : step (lam _) _ |- _ => inv H
    | H : step (var _) _ |- _ => inv H
    | H : star step (lam _) _ |- _ => inv H
    | H : star step (var _) _ |- _ => inv H
  end.



(** ** Resource Measures *)

(** *** Small-Step Time Measure *)

Instance pow_step_congL k:
  Proper ((pow step k) ==> eq ==> (pow step k)) app.
Proof.
  intros s t R u ? <-. revert s t R u.
  induction k;cbn in *;intros ? ? R ?. congruence. destruct R as [s' [R1 R2]].
  exists (s' u). firstorder.
Defined.

Instance pow_step_congR k:
  Proper (eq ==>(pow step k) ==> (pow step k)) (fun s t => app (lam s) t).
Proof.
  intros s ? <- t u R. revert s t u R.
  induction k;cbn in *;intros ? ? ? R. congruence. destruct R as [t' [R1 R2]].
  exists (lam s t'). firstorder.
Defined.


(** *** Small-Step Space Measure *)

Definition redWithMaxSizeL := redWithMaxSize size step.

Lemma redWithMaxSizeL_congL m m' s s' t:
  redWithMaxSizeL m s s' -> m' = (1 + m + size t) -> redWithMaxSizeL m' (s t) (s' t).
Proof.
  intros R Heq.
  induction R as [s | s s'] in m',t,Heq |-* .
  -apply redWithMaxSizeR. cbn. omega. 
  -eapply redWithMaxSizeC. now eauto using step. apply IHR. reflexivity.
   subst m m'. cbn. repeat eapply Nat.max_case_strong;omega.
Qed.

Lemma redWithMaxSizeL_congR m m' s t t':
  redWithMaxSizeL m t t' -> m' = (1 + m + size (lam s)) -> redWithMaxSizeL m' (lam s t) (lam s t').
Proof.
  intros R Heq.
  induction R as [t | t t'] in m',s,Heq |-* .
  -apply redWithMaxSizeR. cbn in *. omega. 
  -eapply redWithMaxSizeC. now eauto using step. apply IHR. reflexivity.
   subst m m'. cbn -[plus]. repeat eapply Nat.max_case_strong;omega.
Defined.

(** *** Big-Step Time Measure*)

Inductive timeBS : nat -> term -> term -> Prop :=
  timeBSVal s : timeBS 0 (λ s) (λ s)
| timeBSBeta (s s' t t' u : term) i j k l: timeBS i s (λ s') -> timeBS j t (λ t') -> timeBS k (subst s' 0 (λ t')) u -> l = (i+j+1+k) -> timeBS l (s t) u.

Lemma step_evaluatesIn s s' t k: s >> s' -> timeBS k s' t -> timeBS (S k) s t.
Proof.
  intros H; induction H in t,k|-*; intros;  try inv H0; eauto 20 using timeBS.
  eapply IHstep in H4. econstructor; eauto. omega. 
Qed.

Lemma timeBS_correct s t k:
  (timeBS k s t <-> pow step k s t /\ lambda t).
Proof.
  split.
  -intros R.
   induction R.
   +unfold pow;cbn. eauto.
   +destruct IHR1 as [R1']. 
    destruct IHR2 as [R2'].
    destruct IHR3 as [R3'].
    split;[|assumption].
    subst l.
    replace (i+j+1+k) with (i+(j+(1+k))) by omega. 
    eapply pow_add.
    eexists;split.
    eapply pow_step_congL;now eauto.
    eapply pow_add.
    eexists;split.
    eapply pow_step_congR;now eauto.
    eapply pow_add.
    eexists;split.
    eapply (rcomp_1 step). eauto.
    eauto. 
  -intros [R lt].
   induction k in s,t,R,lt,R|-*.
   +inv R. inv lt. constructor.
   +change (S k) with (1+k) in R. eapply pow_add in R as (?&R'&?).
    eapply (rcomp_1 step) in R'. eapply step_evaluatesIn;eauto 10.
Qed.

(** *** Big-Step Space Measure*)

Inductive spaceBS : nat -> term -> term -> Prop :=
  spaceBSVal s : spaceBS (size (λ s)) (λ s) (λ s)
| spaceBSBeta (s s' t t' u : term) m1 m2 m3 m:
    spaceBS m1 s (λ s') ->
    spaceBS m2 t (λ t') ->
    spaceBS m3 (subst s' 0 (λ t')) u ->
    m = max (m1 + 1 + size t)
            (max (size (lam s') + 1 + m2) m3) ->
    spaceBS m (s t) u.

Lemma spaceBS_ge s t m: spaceBS m s t -> size s<= m /\ size t <= m.
Proof.
  induction 1. omega.
  subst m. cbn -[plus]. all:(repeat apply Nat.max_case_strong;try omega).
Qed.

Lemma step_evaluatesSpace s s' t m: s >> s' -> spaceBS m s' t -> spaceBS (max (size s) m) s t.
Proof.
  intros H; induction H in t,m|-*; intros H'.
  -inv H'.
   +destruct s;inv H1. decide _;inv H0.
    all:repeat econstructor.
    all:cbn -[plus].
    all:(repeat apply Nat.max_case_strong;try omega).
   +destruct s;inv H. now decide _.
    econstructor. 1,2:econstructor. cbn.
    econstructor.
    1-4:now eauto.
    cbn -[plus]. 
    (repeat apply Nat.max_case_strong;intros;try omega).
  -inv H'. inv H2.
   specialize (spaceBS_ge H3) as [? ?].
   apply IHstep in H3.
   specialize (spaceBS_ge H5) as [? ?].
   specialize (spaceBS_ge H3) as [_ H7].
   econstructor;[now eauto using spaceBS..|]. 
   revert H7. cbn -[plus] in *. 
   (repeat apply Nat.max_case_strong;intros;try omega).
  -inv H'.
   specialize (spaceBS_ge H2) as [? ?].
   eapply IHstep in H2.
   specialize (spaceBS_ge H2) as [_ H7].
   specialize (spaceBS_ge H3) as [? ?].

   econstructor.
   1-3:eassumption.
   revert H7.
   cbn -[plus] in *. 
   (repeat apply Nat.max_case_strong;intros;try omega).
Qed.

Lemma spaceBS_correct s t m:
  spaceBS m s t <-> 
   redWithMaxSizeL m s t /\ lambda t.
Proof.
  split.
  -intros R. induction R.
   +repeat econstructor.
   +destruct IHR1 as (R1'&?). 
    destruct IHR2 as (R2'&?).
    destruct IHR3 as (R3'&?).
    split;[|firstorder].
    subst m.
    eapply redWithMaxSize_trans with (t:=(lam s') t).
    { eapply redWithMaxSizeL_congL. eassumption. reflexivity. }
    
    eapply redWithMaxSize_trans with (t:=(lam s') (lam t')).
    { eapply redWithMaxSizeL_congR. eassumption. reflexivity. }
    econstructor. constructor. eassumption. reflexivity. reflexivity.
    specialize (spaceBS_ge R2) as [_ H3];cbn in H3.   
    cbn - [plus]. repeat eapply Nat.max_case_strong;omega.
  -intros (R&H).
   induction R as [t | s s' t m].
   +inv H;rename x into t. eauto using spaceBS.
   +inv H;rename m' into m. eapply step_evaluatesSpace. eassumption. eauto.
Qed.
