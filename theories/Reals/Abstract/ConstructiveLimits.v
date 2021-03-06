(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import QArith Qabs.
Require Import ConstructiveReals.
Require Import ConstructiveAbs.
Require Import ConstructiveSum.

Local Open Scope ConstructiveReals.


(** Definitions and basic properties of limits of real sequences
    and series. *)


Lemma CR_cv_extens
  : forall {R : ConstructiveReals} (xn yn : nat -> CRcarrier R) (l : CRcarrier R),
    (forall n:nat, xn n == yn n)
    -> CR_cv R xn l
    -> CR_cv R yn l.
Proof.
  intros. intro p. specialize (H0 p) as [n nmaj]. exists n.
  intros. specialize (nmaj i H0).
  apply (CRle_trans _ (CRabs R (CRminus R (xn i) l))).
  2: exact nmaj. rewrite <- CRabs_def. split.
  - apply (CRle_trans _ (CRminus R (xn i) l)).
    apply CRplus_le_compat_r. specialize (H i) as [H _]. exact H.
    pose proof (CRabs_def R (CRminus R (xn i) l) (CRabs R (CRminus R (xn i) l)))
      as [_ H1].
    apply H1. apply CRle_refl.
  - apply (CRle_trans _ (CRopp R (CRminus R (xn i) l))).
    intro abs. apply CRopp_lt_cancel, CRplus_lt_reg_r in abs.
    specialize (H i) as [_ H]. contradiction.
    pose proof (CRabs_def R (CRminus R (xn i) l) (CRabs R (CRminus R (xn i) l)))
      as [_ H1].
    apply H1. apply CRle_refl.
Qed.

Lemma CR_cv_opp : forall {R : ConstructiveReals} (xn : nat -> CRcarrier R) (l : CRcarrier R),
    CR_cv R xn l
    -> CR_cv R (fun n => - xn n) (- l).
Proof.
  intros. intro p. specialize (H p) as [n nmaj].
  exists n. intros. specialize (nmaj i H).
  apply (CRle_trans _ (CRabs R (CRminus R (xn i) l))).
  2: exact nmaj. clear nmaj H.
  unfold CRminus. rewrite <- CRopp_plus_distr, CRabs_opp.
  apply CRle_refl.
Qed.

Lemma CR_cv_plus : forall {R : ConstructiveReals} (xn yn : nat -> CRcarrier R) (a b : CRcarrier R),
    CR_cv R xn a
    -> CR_cv R yn b
    -> CR_cv R (fun n => xn n + yn n) (a + b).
Proof.
  intros. intro p.
  specialize (H (2*p)%positive) as [i imaj].
  specialize (H0 (2*p)%positive) as [j jmaj].
  exists (max i j). intros.
  apply (CRle_trans
           _ (CRabs R (CRplus R (CRminus R (xn i0) a) (CRminus R (yn i0) b)))).
  apply CRabs_morph.
  - unfold CRminus.
    do 2 rewrite <- (Radd_assoc (CRisRing R)).
    apply CRplus_morph. reflexivity. rewrite CRopp_plus_distr.
    destruct (CRisRing R). rewrite Radd_comm, <- Radd_assoc.
    apply CRplus_morph. reflexivity.
    rewrite Radd_comm. reflexivity.
  - apply (CRle_trans _ _ _ (CRabs_triang _ _)).
    apply (CRle_trans _ (CRplus R (CR_of_Q R (1 # 2*p)) (CR_of_Q R (1 # 2*p)))).
    apply CRplus_le_compat. apply imaj, (le_trans _ _ _ (Nat.le_max_l _ _) H).
    apply jmaj, (le_trans _ _ _ (Nat.le_max_r _ _) H).
    apply (CRle_trans _ (CR_of_Q R ((1 # 2 * p) + (1 # 2 * p)))).
    apply CR_of_Q_plus. apply CR_of_Q_le.
    rewrite Qinv_plus_distr. setoid_replace (1 + 1 # 2 * p) with (1 # p).
    apply Qle_refl. reflexivity.
Qed.

Lemma CR_cv_unique : forall {R : ConstructiveReals} (xn : nat -> CRcarrier R)
                       (a b : CRcarrier R),
    CR_cv R xn a
    -> CR_cv R xn b
    -> a == b.
Proof.
  intros. assert (CR_cv R (fun _ => CRzero R) (CRminus R b a)).
  { apply (CR_cv_extens (fun n => CRminus R (xn n) (xn n))).
    intro n. unfold CRminus. apply CRplus_opp_r.
    apply CR_cv_plus. exact H0. apply CR_cv_opp, H. }
  assert (forall q r : Q, 0 < q -> / q < r -> 1 < q * r)%Q.
  { intros. apply (Qmult_lt_l _ _ q) in H3.
    rewrite Qmult_inv_r in H3. exact H3. intro abs.
    rewrite abs in H2. exact (Qlt_irrefl 0 H2). exact H2. }
  clear H H0 xn. remember (CRminus R b a) as z.
  assert (z == 0). split.
  - intro abs. destruct (CR_Q_dense R _ _ abs) as [q [H0 H]].
    destruct (Qarchimedean (/(-q))) as [p pmaj].
    specialize (H1 p) as [n nmaj].
    specialize (nmaj n (le_refl n)). apply nmaj.
    apply (CRlt_trans _ (CR_of_Q R (-q))). apply CR_of_Q_lt.
    apply H2 in pmaj.
    apply (Qmult_lt_r _ _ (1#p)) in pmaj. 2: reflexivity.
    rewrite Qmult_1_l, <- Qmult_assoc in pmaj.
    setoid_replace ((Z.pos p # 1) * (1 # p))%Q with 1%Q in pmaj.
    rewrite Qmult_1_r in pmaj. exact pmaj. unfold Qeq, Qnum, Qden; simpl.
    do 2 rewrite Pos.mul_1_r. reflexivity.
    apply (Qplus_lt_l _ _ q). ring_simplify.
    apply (lt_CR_of_Q R q 0). apply (CRlt_le_trans _ (CRzero R) _ H).
    apply CR_of_Q_zero.
    apply (CRlt_le_trans _ (CRopp R z)).
    apply (CRle_lt_trans _ (CRopp R (CR_of_Q R q))). apply CR_of_Q_opp.
    apply CRopp_gt_lt_contravar, H0.
    apply (CRle_trans _ (CRabs R (CRopp R z))).
    pose proof (CRabs_def R (CRopp R z) (CRabs R (CRopp R z))) as [_ H1].
    apply H1, CRle_refl.
    apply CRabs_morph. unfold CRminus. symmetry. apply CRplus_0_l.
  - intro abs. destruct (CR_Q_dense R _ _ abs) as [q [H0 H]].
    destruct (Qarchimedean (/q)) as [p pmaj].
    specialize (H1 p) as [n nmaj].
    specialize (nmaj n (le_refl n)). apply nmaj.
    apply (CRlt_trans _ (CR_of_Q R q)). apply CR_of_Q_lt.
    apply H2 in pmaj.
    apply (Qmult_lt_r _ _ (1#p)) in pmaj. 2: reflexivity.
    rewrite Qmult_1_l, <- Qmult_assoc in pmaj.
    setoid_replace ((Z.pos p # 1) * (1 # p))%Q with 1%Q in pmaj.
    rewrite Qmult_1_r in pmaj. exact pmaj. unfold Qeq, Qnum, Qden; simpl.
    do 2 rewrite Pos.mul_1_r. reflexivity.
    apply (lt_CR_of_Q R 0 q). apply (CRle_lt_trans _ (CRzero R)).
    2: exact H0. apply CR_of_Q_zero.
    apply (CRlt_le_trans _ _ _ H).
    apply (CRle_trans _ (CRabs R (CRopp R z))).
    apply (CRle_trans _ (CRabs R z)).
    pose proof (CRabs_def R z (CRabs R z)) as [_ H1].
    apply H1. apply CRle_refl. apply CRabs_opp.
    apply CRabs_morph. unfold CRminus. symmetry. apply CRplus_0_l.
  - subst z. apply (CRplus_eq_reg_l (CRopp R a)).
    apply (CReq_trans _ (CRzero R)). apply CRplus_opp_l.
    destruct (CRisRing R).
    apply (CReq_trans _ (CRplus R b (CRopp R a))). apply CReq_sym, H.
    apply Radd_comm.
Qed.

Lemma CR_cv_eq : forall {R : ConstructiveReals}
                   (v u : nat -> CRcarrier R) (s : CRcarrier R),
    (forall n:nat, u n == v n)
    -> CR_cv R u s
    -> CR_cv R v s.
Proof.
  intros R v u s seq H1 p. specialize (H1 p) as [N H0].
  exists N. intros. unfold CRminus. rewrite <- seq. apply H0, H.
Qed.

Lemma CR_cauchy_eq : forall {R : ConstructiveReals}
                       (un vn : nat -> CRcarrier R),
    (forall n:nat, un n == vn n)
    -> CR_cauchy R un
    -> CR_cauchy R vn.
Proof.
  intros. intro p. specialize (H0 p) as [n H0].
  exists n. intros. specialize (H0 i j H1 H2).
  unfold CRminus in H0. rewrite <- CRabs_def.
  rewrite <- CRabs_def in H0.
  do 2 rewrite H in H0. exact H0.
Qed.

Lemma CR_cv_proper : forall {R : ConstructiveReals}
                       (un : nat -> CRcarrier R) (a b : CRcarrier R),
    CR_cv R un a
    -> a == b
    -> CR_cv R un b.
Proof.
  intros. intro p. specialize (H p) as [n H].
  exists n. intros. unfold CRminus. rewrite <- H0. apply H, H1.
Qed.

Instance CR_cv_morph
  : forall {R : ConstructiveReals} (un : nat -> CRcarrier R), CMorphisms.Proper
      (CMorphisms.respectful (CReq R) CRelationClasses.iffT) (CR_cv R un).
Proof.
  split. intros. apply (CR_cv_proper un x). exact H0. exact H.
  intros. apply (CR_cv_proper un y). exact H0. symmetry. exact H.
Qed.

Lemma Un_cv_nat_real : forall {R : ConstructiveReals}
                         (un : nat -> CRcarrier R) (l : CRcarrier R),
    CR_cv R un l
    -> forall eps : CRcarrier R,
      0 < eps
      -> { p : nat & forall i:nat, le p i -> CRabs R (un i - l) < eps }.
Proof.
  intros. destruct (CR_archimedean R (CRinv R eps (inr H0))) as [k kmaj].
  assert (0 < CR_of_Q R (Z.pos k # 1)).
  { rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity. }
  specialize (H k) as [p pmaj].
  exists p. intros.
  apply (CRle_lt_trans _ (CR_of_Q R (1 # k))).
  apply pmaj, H.
  apply (CRmult_lt_reg_l (CR_of_Q R (Z.pos k # 1))). exact H1.
  rewrite <- CR_of_Q_mult.
  apply (CRle_lt_trans _ 1).
  rewrite <- CR_of_Q_one. apply CR_of_Q_le.
  unfold Qle; simpl. do 2 rewrite Pos.mul_1_r. apply Z.le_refl.
  apply (CRmult_lt_reg_r (CRinv R eps (inr H0))).
  apply CRinv_0_lt_compat, H0. rewrite CRmult_1_l, CRmult_assoc.
  rewrite CRinv_r, CRmult_1_r. exact kmaj.
Qed.

Lemma Un_cv_real_nat : forall {R : ConstructiveReals}
                         (un : nat -> CRcarrier R) (l : CRcarrier R),
    (forall eps : CRcarrier R,
      0 < eps
      -> { p : nat & forall i:nat, le p i -> CRabs R (un i - l) < eps })
    -> CR_cv R un l.
Proof.
  intros. intros n.
  specialize (H (CR_of_Q R (1#n))) as [p pmaj].
  rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
  exists p. intros. apply CRlt_asym. apply pmaj. apply H.
Qed.

Definition series_cv {R : ConstructiveReals}
           (un : nat -> CRcarrier R) (s : CRcarrier R) : Set
  := CR_cv R (CRsum un) s.

Definition series_cv_lim_lt {R : ConstructiveReals}
           (un : nat -> CRcarrier R) (x : CRcarrier R) : Set
  := { l : CRcarrier R & prod (series_cv un l) (l < x) }.

Definition series_cv_le_lim {R : ConstructiveReals}
           (x : CRcarrier R) (un : nat -> CRcarrier R) : Set
  := { l : CRcarrier R & prod (series_cv un l) (x <= l) }.

Lemma CR_cv_minus :
  forall {R : ConstructiveReals}
    (An Bn:nat -> CRcarrier R) (l1 l2:CRcarrier R),
    CR_cv R An l1 -> CR_cv R Bn l2
    -> CR_cv R (fun i:nat => An i - Bn i) (l1 - l2).
Proof.
  intros. apply CR_cv_plus. apply H.
  intros p. specialize (H0 p) as [n H0]. exists n.
  intros. setoid_replace (- Bn i - - l2) with (- (Bn i - l2)).
  rewrite CRabs_opp. apply H0, H1. unfold CRminus.
  rewrite CRopp_plus_distr, CRopp_involutive. reflexivity.
Qed.

Lemma CR_cv_nonneg :
  forall {R : ConstructiveReals} (An:nat -> CRcarrier R) (l:CRcarrier R),
    CR_cv R An l
    -> (forall n:nat, 0 <= An n)
    -> 0 <= l.
Proof.
  intros. intro abs.
  destruct (Un_cv_nat_real _ l H (-l)) as [N H1].
  rewrite <- CRopp_0. apply CRopp_gt_lt_contravar. apply abs.
  specialize (H1 N (le_refl N)).
  pose proof (CRabs_def R (An N - l) (CRabs R (An N - l))) as [_ H2].
  apply (CRle_lt_trans _ _ _ (CRle_abs _)) in H1.
  apply (H0 N). apply (CRplus_lt_reg_r (-l)).
  rewrite CRplus_0_l. exact H1.
Qed.

Lemma series_cv_unique :
  forall {R : ConstructiveReals} (Un:nat -> CRcarrier R) (l1 l2:CRcarrier R),
    series_cv Un l1 -> series_cv Un l2 -> l1 == l2.
Proof.
  intros. apply (CR_cv_unique (CRsum Un)); assumption.
Qed.

Lemma CR_cv_scale : forall {R : ConstructiveReals} (u : nat -> CRcarrier R)
                      (a : CRcarrier R) (s : CRcarrier R),
    CR_cv R u s -> CR_cv R (fun n => u n * a) (s * a).
Proof.
  intros. intros n.
  destruct (CR_archimedean R (1 + CRabs R a)).
  destruct (H (n * x)%positive).
  exists x0. intros.
  unfold CRminus. rewrite CRopp_mult_distr_l.
  rewrite <- CRmult_plus_distr_r.
  apply (CRle_trans _ ((CR_of_Q R (1 # n * x)) * CRabs R a)).
  rewrite CRabs_mult. apply CRmult_le_compat_r. apply CRabs_pos.
  apply c0, H0.
  setoid_replace (1 # n * x)%Q with ((1 # n) *(1# x))%Q. 2: reflexivity.
  rewrite <- (CRmult_1_r (CR_of_Q R (1#n))).
  rewrite CR_of_Q_mult, CRmult_assoc.
  apply CRmult_le_compat_l. rewrite <- CR_of_Q_zero.
  apply CR_of_Q_le. discriminate. intro abs.
  apply (CRmult_lt_compat_l (CR_of_Q R (Z.pos x #1))) in abs.
  rewrite CRmult_1_r, <- CRmult_assoc, <- CR_of_Q_mult in abs.
  rewrite (CR_of_Q_morph R ((Z.pos x # 1) * (1 # x))%Q 1%Q) in abs.
  rewrite CR_of_Q_one, CRmult_1_l in abs.
  apply (CRlt_asym _ _ abs), (CRlt_trans _ (1 + CRabs R a)).
  2: exact c. rewrite <- CRplus_0_l, <- CRplus_assoc.
  apply CRplus_lt_compat_r. rewrite CRplus_0_r. apply CRzero_lt_one.
  unfold Qmult, Qeq, Qnum, Qden. ring_simplify. rewrite Pos.mul_1_l.
  reflexivity.
  apply (CRlt_trans _ (1+CRabs R a)). 2: exact c.
  rewrite CRplus_comm.
  rewrite <- (CRplus_0_r 0). apply CRplus_le_lt_compat.
  apply CRabs_pos. apply CRzero_lt_one.
Qed.

Lemma CR_cv_const : forall {R : ConstructiveReals} (a : CRcarrier R),
    CR_cv R (fun n => a) a.
Proof.
  intros a p. exists O. intros.
  unfold CRminus. rewrite CRplus_opp_r.
  rewrite CRabs_right. rewrite <- CR_of_Q_zero.
  apply CR_of_Q_le. discriminate. apply CRle_refl.
Qed.

Lemma Rcv_cauchy_mod : forall {R : ConstructiveReals}
                         (un : nat -> CRcarrier R) (l : CRcarrier R),
    CR_cv R un l -> CR_cauchy R un.
Proof.
  intros. intros p. specialize (H (2*p)%positive) as [k H].
  exists k. intros n q H0 H1.
  setoid_replace (1#p)%Q with ((1#2*p) + (1#2*p))%Q.
  rewrite CR_of_Q_plus.
  setoid_replace (un n - un q) with ((un n - l) - (un q - l)).
  apply (CRle_trans _ _ _ (CRabs_triang _ _)).
  apply CRplus_le_compat.
  - apply H, H0.
  - rewrite CRabs_opp. apply H. apply H1.
  - unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph.
    reflexivity. rewrite CRplus_comm, CRopp_plus_distr, CRopp_involutive.
    rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r. reflexivity.
  - rewrite Qinv_plus_distr. reflexivity.
Qed.

Lemma series_cv_eq : forall {R : ConstructiveReals}
                       (u v : nat -> CRcarrier R) (s : CRcarrier R),
    (forall n:nat, u n == v n)
    -> series_cv u s
    -> series_cv v s.
Proof.
  intros. intros p. specialize (H0 p). destruct H0 as [N H0].
  exists N. intros. unfold CRminus.
  rewrite <- (CRsum_eq u). apply H0, H1. intros. apply H.
Qed.

Lemma CR_growing_transit : forall {R : ConstructiveReals} (un : nat -> CRcarrier R),
    (forall n:nat, un n <= un (S n))
    -> forall n p : nat, le n p -> un n <= un p.
Proof.
  induction p.
  - intros. inversion H0. apply CRle_refl.
  - intros. apply Nat.le_succ_r in H0. destruct H0.
    apply (CRle_trans _ (un p)). apply IHp, H0. apply H.
    subst n. apply CRle_refl.
Qed.

Lemma growing_ineq :
  forall {R : ConstructiveReals} (Un:nat -> CRcarrier R) (l:CRcarrier R),
    (forall n:nat, Un n <= Un (S n))
    -> CR_cv R Un l -> forall n:nat, Un n <= l.
Proof.
  intros. intro abs.
  destruct (Un_cv_nat_real _ l H0 (Un n - l)) as [N H1].
  rewrite <- (CRplus_opp_r l). apply CRplus_lt_compat_r. exact abs.
  specialize (H1 (max n N) (Nat.le_max_r _ _)).
  apply (CRle_lt_trans _ _ _ (CRle_abs _)) in H1.
  apply CRplus_lt_reg_r in H1.
  apply (CR_growing_transit Un H n (max n N)). apply Nat.le_max_l.
  exact H1.
Qed.

Lemma CR_cv_open_below
  : forall {R : ConstructiveReals}
      (un : nat -> CRcarrier R) (m l : CRcarrier R),
    CR_cv R un l
    -> m < l
    -> { n : nat & forall i:nat, le n i -> m < un i }.
Proof.
  intros. apply CRlt_minus in H0.
  pose proof (Un_cv_nat_real _ l H (l-m) H0) as [n nmaj].
  exists n. intros. specialize (nmaj i H1).
  apply CRabs_lt in nmaj.
  destruct nmaj as [_ nmaj]. unfold CRminus in nmaj.
  rewrite CRopp_plus_distr, CRopp_involutive, CRplus_comm in nmaj.
  apply CRplus_lt_reg_l in nmaj.
  apply (CRplus_lt_reg_l R (-m)). rewrite CRplus_opp_l.
  apply (CRplus_lt_reg_r (-un i)). rewrite CRplus_0_l.
  rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r. exact nmaj.
Qed.

Lemma CR_cv_open_above
  : forall {R : ConstructiveReals}
      (un : nat -> CRcarrier R) (m l : CRcarrier R),
    CR_cv R un l
    -> l < m
    -> { n : nat & forall i:nat, le n i -> un i < m }.
Proof.
  intros. apply CRlt_minus in H0.
  pose proof (Un_cv_nat_real _ l H (m-l) H0) as [n nmaj].
  exists n. intros. specialize (nmaj i H1).
  apply CRabs_lt in nmaj.
  destruct nmaj as [nmaj _]. apply CRplus_lt_reg_r in nmaj.
  exact nmaj.
Qed.

Lemma CR_cv_bound_down : forall {R : ConstructiveReals}
                           (u : nat -> CRcarrier R) (A l : CRcarrier R) (N : nat),
    (forall n:nat, le N n -> A <= u n)
    -> CR_cv R u l
    -> A <= l.
Proof.
  intros. intro r.
  apply (CRplus_lt_compat_r (-l)) in r. rewrite CRplus_opp_r in r.
  destruct (Un_cv_nat_real _ l H0 (A - l) r) as [n H1].
  apply (H (n+N)%nat).
  rewrite <- (plus_0_l N). rewrite Nat.add_assoc.
  apply Nat.add_le_mono_r. apply le_0_n.
  specialize (H1 (n+N)%nat). apply (CRplus_lt_reg_r (-l)).
  assert (n + N >= n)%nat. rewrite <- (plus_0_r n). rewrite <- plus_assoc.
  apply Nat.add_le_mono_l. apply le_0_n. specialize (H1 H2).
  apply (CRle_lt_trans _ (CRabs R (u (n + N)%nat - l))).
  apply CRle_abs. assumption.
Qed.

Lemma CR_cv_bound_up : forall {R : ConstructiveReals}
                         (u : nat -> CRcarrier R) (A l : CRcarrier R) (N : nat),
    (forall n:nat, le N n -> u n <= A)
    -> CR_cv R u l
    -> l <= A.
Proof.
  intros. intro r.
  apply (CRplus_lt_compat_r (-A)) in r. rewrite CRplus_opp_r in r.
  destruct (Un_cv_nat_real _ l H0 (l-A) r) as [n H1].
  apply (H (n+N)%nat).
  - rewrite <- (plus_0_l N). apply Nat.add_le_mono_r. apply le_0_n.
  - specialize (H1 (n+N)%nat). apply (CRplus_lt_reg_l R (l - A - u (n+N)%nat)).
    unfold CRminus. repeat rewrite CRplus_assoc.
    rewrite CRplus_opp_l, CRplus_0_r, (CRplus_comm (-A)).
    rewrite CRplus_assoc, CRplus_opp_r, CRplus_0_r.
    apply (CRle_lt_trans _ _ _ (CRle_abs _)).
    fold (l - u (n+N)%nat). rewrite CRabs_minus_sym. apply H1.
    rewrite <- (plus_0_r n). rewrite <- plus_assoc.
    apply Nat.add_le_mono_l. apply le_0_n.
Qed.

Lemma series_cv_maj : forall {R : ConstructiveReals}
                        (un vn : nat -> CRcarrier R) (s : CRcarrier R),
    (forall n:nat, CRabs R (un n) <= vn n)
    -> series_cv vn s
    -> { l : CRcarrier R & prod (series_cv un l) (l <= s) }.
Proof.
  intros. destruct (CR_complete R (CRsum un)).
  - intros n.
    specialize (H0 (2*n)%positive) as [N maj].
    exists N. intros i j H0 H1.
    apply (CRle_trans _ (CRsum vn (max i j) - CRsum vn (min i j))).
    apply Abs_sum_maj. apply H.
    setoid_replace (CRsum vn (max i j) - CRsum vn (min i j))
      with (CRabs R (CRsum vn (max i j) - (CRsum vn (min i j)))).
    setoid_replace (CRsum vn (Init.Nat.max i j) - CRsum vn (Init.Nat.min i j))
      with (CRsum vn (Init.Nat.max i j) - s - (CRsum vn (Init.Nat.min i j) - s)).
    apply (CRle_trans _ _ _ (CRabs_triang _ _)).
    setoid_replace (1#n)%Q with ((1#2*n) + (1#2*n))%Q.
    rewrite CR_of_Q_plus.
    apply CRplus_le_compat.
    apply maj. apply (le_trans _ i). assumption. apply Nat.le_max_l.
    rewrite CRabs_opp. apply maj.
    apply Nat.min_case. apply (le_trans _ i). assumption. apply le_refl.
    assumption. rewrite Qinv_plus_distr. reflexivity.
    unfold CRminus. rewrite CRplus_assoc. apply CRplus_morph.
    reflexivity. rewrite CRopp_plus_distr, CRopp_involutive.
    rewrite CRplus_comm, CRplus_assoc, CRplus_opp_r, CRplus_0_r.
    reflexivity.
    rewrite CRabs_right. reflexivity.
    rewrite <- (CRplus_opp_r (CRsum vn (Init.Nat.min i j))).
    apply CRplus_le_compat. apply pos_sum_more.
    intros. apply (CRle_trans _ (CRabs R (un k))). apply CRabs_pos.
    apply H. apply (le_trans _ i). apply Nat.le_min_l. apply Nat.le_max_l.
    apply CRle_refl.
  - exists x. split. assumption.
    (* x <= s *)
    apply (CRplus_le_reg_r (-x)). rewrite CRplus_opp_r.
    apply (CR_cv_bound_down (fun n => CRsum vn n - CRsum un n) _ _ 0).
    intros. rewrite <- (CRplus_opp_r (CRsum un n)).
    apply CRplus_le_compat. apply sum_Rle.
    intros. apply (CRle_trans _ (CRabs R (un k))).
    apply CRle_abs. apply H. apply CRle_refl.
    apply CR_cv_plus. assumption.
    apply CR_cv_opp. assumption.
Qed.

Lemma series_cv_abs_lt
  : forall {R : ConstructiveReals} (un vn : nat -> CRcarrier R) (l : CRcarrier R),
    (forall n:nat, CRabs R (un n) <= vn n)
    -> series_cv_lim_lt vn l
    -> series_cv_lim_lt un l.
Proof.
  intros. destruct H0 as [x [H0 H1]].
  destruct (series_cv_maj un vn x H H0) as [x0 H2].
  exists x0. split. apply H2. apply (CRle_lt_trans _ x).
  apply H2. apply H1.
Qed.

Definition series_cv_abs {R : ConstructiveReals} (u : nat -> CRcarrier R)
  : CR_cauchy R (CRsum (fun n => CRabs R (u n)))
    -> { l : CRcarrier R & series_cv u l }.
Proof.
  intros. apply CR_complete in H. destruct H.
  destruct (series_cv_maj u (fun k => CRabs R (u k)) x).
  intro n. apply CRle_refl. assumption. exists x0. apply p.
Qed.

Lemma series_cv_abs_eq
  : forall {R : ConstructiveReals} (u : nat -> CRcarrier R) (a : CRcarrier R)
           (cau : CR_cauchy R (CRsum (fun n => CRabs R (u n)))),
    series_cv u a
    -> (a == (let (l,_):= series_cv_abs u cau in l))%ConstructiveReals.
Proof.
  intros. destruct (series_cv_abs u cau).
  apply (series_cv_unique u). exact H. exact s.
Qed.

Lemma series_cv_abs_cv
  : forall {R : ConstructiveReals} (u : nat -> CRcarrier R)
           (cau : CR_cauchy R (CRsum (fun n => CRabs R (u n)))),
    series_cv u (let (l,_):= series_cv_abs u cau in l).
Proof.
  intros. destruct (series_cv_abs u cau). exact s.
Qed.

Lemma series_cv_opp : forall {R : ConstructiveReals}
                        (s : CRcarrier R) (u : nat -> CRcarrier R),
    series_cv u s
    -> series_cv (fun n => - u n) (- s).
Proof.
  intros. intros p. specialize (H p) as [N H].
  exists N. intros n H0.
  setoid_replace (CRsum (fun n0 : nat => - u n0) n - - s)
    with (-(CRsum (fun n0 : nat => u n0) n - s)).
  rewrite CRabs_opp.
  apply H, H0. unfold CRminus.
  rewrite sum_opp. rewrite CRopp_plus_distr. reflexivity.
Qed.

Lemma series_cv_scale : forall {R : ConstructiveReals}
                          (a : CRcarrier R) (s : CRcarrier R) (u : nat -> CRcarrier R),
    series_cv u s
    -> series_cv (fun n => (u n) * a) (s * a).
Proof.
  intros.
  apply (CR_cv_eq _ (fun n => CRsum u n * a)).
  intro n. rewrite sum_scale. reflexivity. apply CR_cv_scale, H.
Qed.

Lemma series_cv_plus : forall {R : ConstructiveReals}
                         (u v : nat -> CRcarrier R) (s t : CRcarrier R),
    series_cv u s
    -> series_cv v t
    -> series_cv (fun n => u n + v n) (s + t).
Proof.
  intros. apply (CR_cv_eq _ (fun n => CRsum u n + CRsum v n)).
  intro n. symmetry. apply sum_plus. apply CR_cv_plus. exact H. exact H0.
Qed.

Lemma series_cv_nonneg : forall {R : ConstructiveReals}
                           (u : nat -> CRcarrier R) (s : CRcarrier R),
    (forall n:nat, 0 <= u n) -> series_cv u s -> 0 <= s.
Proof.
  intros. apply (CRle_trans 0 (CRsum u 0)). apply H.
  apply (growing_ineq (CRsum u)). intro n. simpl.
  rewrite <- CRplus_0_r. apply CRplus_le_compat.
  rewrite CRplus_0_r. apply CRle_refl. apply H. apply H0.
Qed.

Lemma CR_cv_le : forall {R : ConstructiveReals}
                   (u v : nat -> CRcarrier R) (a b : CRcarrier R),
    (forall n:nat, u n <= v n)
    -> CR_cv R u a
    -> CR_cv R v b
    -> a <= b.
Proof.
  intros. apply (CRplus_le_reg_r (-a)). rewrite CRplus_opp_r.
  apply (CR_cv_bound_down (fun i:nat => v i - u i) _ _ 0).
  intros. rewrite <- (CRplus_opp_l (u n)).
  unfold CRminus.
  rewrite (CRplus_comm (v n)). apply CRplus_le_compat_l.
  apply H. apply CR_cv_plus. exact H1. apply CR_cv_opp, H0.
Qed.

Lemma CR_cv_abs_cont : forall {R : ConstructiveReals}
                         (u : nat -> CRcarrier R) (s : CRcarrier R),
    CR_cv R u s
    -> CR_cv R (fun n => CRabs R (u n)) (CRabs R s).
Proof.
  intros. intros eps. specialize (H eps) as [N lim].
  exists N. intros n H.
  apply (CRle_trans _ (CRabs R (u n - s))). apply CRabs_triang_inv2.
  apply lim. assumption.
Qed.

Lemma CR_cv_dist_cont : forall {R : ConstructiveReals}
                          (u : nat -> CRcarrier R) (a s : CRcarrier R),
    CR_cv R u s
    -> CR_cv R (fun n => CRabs R (a - u n)) (CRabs R (a - s)).
Proof.
  intros. apply CR_cv_abs_cont.
  intros eps. specialize (H eps) as [N lim].
  exists N. intros n H.
  setoid_replace (a - u n - (a - s)) with (s - (u n)).
  specialize (lim n).
  rewrite CRabs_minus_sym.
  apply lim. assumption.
  unfold CRminus. rewrite CRopp_plus_distr, CRopp_involutive.
  rewrite (CRplus_comm a), (CRplus_comm s).
  rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l. reflexivity.
Qed.

Lemma series_cv_triangle : forall {R : ConstructiveReals}
                             (u : nat -> CRcarrier R) (s sAbs : CRcarrier R),
    series_cv u s
    -> series_cv (fun n => CRabs R (u n)) sAbs
    -> CRabs R s <= sAbs.
Proof.
  intros.
  apply (CR_cv_le (fun n => CRabs R (CRsum u n))
                   (CRsum (fun n => CRabs R (u n)))).
  intros. apply multiTriangleIneg. apply CR_cv_abs_cont. assumption. assumption.
Qed.

Lemma CR_double : forall {R : ConstructiveReals} (x:CRcarrier R),
    CR_of_Q R 2 * x == x + x.
Proof.
  intros R x. rewrite (CR_of_Q_morph R 2 (1+1)).
  2: reflexivity. rewrite CR_of_Q_plus, CR_of_Q_one.
  rewrite CRmult_plus_distr_r, CRmult_1_l. reflexivity.
Qed.

Lemma GeoCvZero : forall {R : ConstructiveReals},
    CR_cv R (fun n:nat => CRpow (CR_of_Q R (1#2)) n) 0.
Proof.
  intro R. assert (forall n:nat, INR n < CRpow (CR_of_Q R 2) n).
  { induction n. unfold INR; simpl. rewrite CR_of_Q_zero.
    apply CRzero_lt_one. unfold INR. fold (1+n)%nat.
    rewrite Nat2Z.inj_add.
    rewrite (CR_of_Q_morph R _ ((Z.of_nat 1 # 1) + (Z.of_nat n #1))).
    2: symmetry; apply Qinv_plus_distr.
    rewrite CR_of_Q_plus.
    replace (CRpow (CR_of_Q R 2) (1 + n))
      with (CR_of_Q R 2 * CRpow (CR_of_Q R 2) n).
    2: reflexivity. rewrite CR_double.
    apply CRplus_le_lt_compat.
    2: exact IHn. simpl. rewrite CR_of_Q_one.
    apply pow_R1_Rle. rewrite <- CR_of_Q_one. apply CR_of_Q_le. discriminate. }
  intros p. exists (Pos.to_nat p). intros.
  unfold CRminus. rewrite CRopp_0. rewrite CRplus_0_r.
  rewrite CRabs_right.
  2: apply pow_le; rewrite <- CR_of_Q_zero; apply CR_of_Q_le; discriminate.
  apply CRlt_asym.
  apply (CRmult_lt_reg_l (CR_of_Q R (Z.pos p # 1))).
  rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity. rewrite <- CR_of_Q_mult.
  rewrite (CR_of_Q_morph R ((Z.pos p # 1) * (1 # p)) 1).
  2: unfold Qmult, Qeq, Qnum, Qden; ring_simplify; reflexivity.
  apply (CRmult_lt_reg_r (CRpow (CR_of_Q R 2) i)).
  apply pow_lt. simpl. rewrite <- CR_of_Q_zero.
  apply CR_of_Q_lt. reflexivity.
  rewrite CRmult_assoc. rewrite pow_mult.
  rewrite (pow_proper (CR_of_Q R (1 # 2) * CR_of_Q R 2) 1), pow_one.
  rewrite CRmult_1_r, CR_of_Q_one, CRmult_1_l.
  apply (CRle_lt_trans _ (INR i)). 2: exact (H i). clear H.
  apply CR_of_Q_le. unfold Qle,Qnum,Qden.
  do 2 rewrite Z.mul_1_r.
  rewrite <- positive_nat_Z. apply Nat2Z.inj_le, H0.
  rewrite <- CR_of_Q_mult. setoid_replace ((1#2)*2)%Q with 1%Q.
  apply CR_of_Q_one. reflexivity.
Qed.

Lemma GeoFiniteSum : forall {R : ConstructiveReals} (n:nat),
    CRsum (CRpow (CR_of_Q R (1#2))) n == CR_of_Q R 2 - CRpow (CR_of_Q R (1#2)) n.
Proof.
  induction n.
  - unfold CRsum, CRpow. simpl (1%ConstructiveReals).
    unfold CRminus. rewrite (CR_of_Q_morph R _ (1+1)).
    rewrite CR_of_Q_plus, CR_of_Q_one, CRplus_assoc.
    rewrite CRplus_opp_r, CRplus_0_r. reflexivity. reflexivity.
  - setoid_replace (CRsum (CRpow (CR_of_Q R (1 # 2))) (S n))
      with (CRsum (CRpow (CR_of_Q R (1 # 2))) n + CRpow (CR_of_Q R (1 # 2)) (S n)).
    2: reflexivity.
    rewrite IHn. clear IHn. unfold CRminus.
    rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
    apply (CRplus_eq_reg_l
             (CRpow (CR_of_Q R (1 # 2)) n + CRpow (CR_of_Q R (1 # 2)) (S n))).
    rewrite (CRplus_assoc _ _ (-CRpow (CR_of_Q R (1 # 2)) (S n))),
    CRplus_opp_r, CRplus_0_r.
    rewrite (CRplus_comm (CRpow (CR_of_Q R (1 # 2)) n)), CRplus_assoc.
    rewrite <- (CRplus_assoc (CRpow (CR_of_Q R (1 # 2)) n)), CRplus_opp_r,
    CRplus_0_l, <- CR_double.
    setoid_replace (CRpow (CR_of_Q R (1 # 2)) (S n))
      with (CR_of_Q R (1 # 2) * CRpow (CR_of_Q R (1 # 2)) n).
    2: reflexivity.
    rewrite <- CRmult_assoc, <- CR_of_Q_mult.
    setoid_replace (2 * (1 # 2))%Q with 1%Q.
    rewrite CR_of_Q_one. apply CRmult_1_l. reflexivity.
Qed.

Lemma GeoHalfBelowTwo : forall {R : ConstructiveReals} (n:nat),
    CRsum (CRpow (CR_of_Q R (1#2))) n < CR_of_Q R 2.
Proof.
  intros. rewrite <- (CRplus_0_r (CR_of_Q R 2)), GeoFiniteSum.
  apply CRplus_lt_compat_l. rewrite <- CRopp_0.
  apply CRopp_gt_lt_contravar.
  apply pow_lt. rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
Qed.

Lemma GeoHalfTwo : forall {R : ConstructiveReals},
    series_cv (fun n => CRpow (CR_of_Q R (1#2)) n) (CR_of_Q R 2).
Proof.
  intro R.
  apply (CR_cv_eq _ (fun n => CR_of_Q R 2 - CRpow (CR_of_Q R (1 # 2)) n)).
  - intro n. rewrite GeoFiniteSum. reflexivity.
  - assert (forall n:nat, INR n < CRpow (CR_of_Q R 2) n).
    { induction n. unfold INR; simpl. rewrite CR_of_Q_zero.
      apply CRzero_lt_one. apply (CRlt_le_trans _ (CRpow (CR_of_Q R 2) n + 1)).
      unfold INR.
      rewrite Nat2Z.inj_succ, <- Z.add_1_l.
      rewrite (CR_of_Q_morph R _ (1 + (Z.of_nat n #1))).
      2: symmetry; apply Qinv_plus_distr. rewrite CR_of_Q_plus.
      rewrite CRplus_comm. rewrite CR_of_Q_one.
      apply CRplus_lt_compat_r, IHn.
      setoid_replace (CRpow (CR_of_Q R 2) (S n))
        with (CRpow (CR_of_Q R 2) n + CRpow (CR_of_Q R 2) n).
      apply CRplus_le_compat. apply CRle_refl.
      apply pow_R1_Rle. rewrite <- CR_of_Q_one. apply CR_of_Q_le. discriminate.
      rewrite <- CR_double. reflexivity. }
    intros n. exists (Pos.to_nat n). intros.
    setoid_replace (CR_of_Q R 2 - CRpow (CR_of_Q R (1 # 2)) i - CR_of_Q R 2)
      with (- CRpow (CR_of_Q R (1 # 2)) i).
    rewrite CRabs_opp. rewrite CRabs_right.
    assert (0 < CR_of_Q R 2).
    { rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity. }
    rewrite (pow_proper _ (CRinv R (CR_of_Q R 2) (inr H1))).
    rewrite pow_inv. apply CRlt_asym.
    apply (CRmult_lt_reg_l (CRpow (CR_of_Q R 2) i)). apply pow_lt, H1.
    rewrite CRinv_r.
    apply (CRmult_lt_reg_r (CR_of_Q R (Z.pos n#1))).
    rewrite <- CR_of_Q_zero. apply CR_of_Q_lt. reflexivity.
    rewrite CRmult_1_l, CRmult_assoc.
    rewrite <- CR_of_Q_mult.
    rewrite (CR_of_Q_morph R ((1 # n) * (Z.pos n # 1)) 1). 2: reflexivity.
    rewrite CR_of_Q_one, CRmult_1_r. apply (CRle_lt_trans _ (INR i)).
    2: apply H. apply CR_of_Q_le.
    unfold Qle, Qnum, Qden. do 2 rewrite Z.mul_1_r. destruct i.
    exfalso. inversion H0. pose proof (Pos2Nat.is_pos n).
    rewrite H3 in H2. inversion H2.
    apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    apply (le_trans _ _ _ H0). rewrite SuccNat2Pos.id_succ. apply le_refl.
    apply (CRmult_eq_reg_l (CR_of_Q R 2)). right. exact H1.
    rewrite CRinv_r. rewrite <- CR_of_Q_mult.
    setoid_replace (2 * (1 # 2))%Q with 1%Q.
    apply CR_of_Q_one. reflexivity.
    apply CRlt_asym, pow_lt. rewrite <- CR_of_Q_zero.
    apply CR_of_Q_lt. reflexivity.
    unfold CRminus. rewrite CRplus_comm, <- CRplus_assoc.
    rewrite CRplus_opp_l, CRplus_0_l. reflexivity.
Qed.

Lemma series_cv_remainder_maj : forall {R : ConstructiveReals} (u : nat -> CRcarrier R)
                                  (s eps : CRcarrier R)
                                  (N : nat),
    series_cv u s
    -> 0 < eps
    -> (forall n:nat, 0 <= u n)
    -> CRabs R (CRsum u N - s) <= eps
    -> forall n:nat, CRsum (fun k=> u (N + S k)%nat) n <= eps.
Proof.
  intros. pose proof (sum_assoc u N n).
  rewrite <- (CRsum_eq (fun k : nat => u (S N + k)%nat)).
  apply (CRplus_le_reg_l (CRsum u N)). rewrite <- H3.
  apply (CRle_trans _ s). apply growing_ineq.
  2: apply H.
  intro k. simpl. rewrite <- CRplus_0_r, CRplus_assoc.
  apply CRplus_le_compat_l. rewrite CRplus_0_l. apply H1.
  rewrite CRabs_minus_sym in H2.
  rewrite CRplus_comm. apply (CRplus_le_reg_r (-CRsum u N)).
  rewrite CRplus_assoc. rewrite CRplus_opp_r. rewrite CRplus_0_r.
  apply (CRle_trans _ (CRabs R (s - CRsum u N))). apply CRle_abs.
  assumption. intros. rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma series_cv_abs_remainder : forall {R : ConstructiveReals} (u : nat -> CRcarrier R)
                                  (s sAbs : CRcarrier R)
                                  (n : nat),
    series_cv u s
    -> series_cv (fun n => CRabs R (u n)) sAbs
    -> CRabs R (CRsum u n - s)
      <= sAbs - CRsum (fun n => CRabs R (u n)) n.
Proof.
  intros.
  apply (CR_cv_le (fun N => CRabs R (CRsum u n - (CRsum u (n + N))))
                   (fun N => CRsum (fun n : nat => CRabs R (u n)) (n + N)
                          - CRsum (fun n : nat => CRabs R (u n)) n)).
  - intro N. destruct N. rewrite plus_0_r. unfold CRminus.
    rewrite CRplus_opp_r. rewrite CRplus_opp_r.
    rewrite CRabs_right. apply CRle_refl. apply CRle_refl.
    rewrite Nat.add_succ_r.
    replace (S (n + N)) with (S n + N)%nat. 2: reflexivity.
    unfold CRminus. rewrite sum_assoc. rewrite sum_assoc.
    rewrite CRopp_plus_distr.
    rewrite <- CRplus_assoc, CRplus_opp_r, CRplus_0_l, CRabs_opp.
    rewrite CRplus_comm, <- CRplus_assoc, CRplus_opp_l.
    rewrite CRplus_0_l. apply multiTriangleIneg.
  - apply CR_cv_dist_cont. intros eps.
    specialize (H eps) as [N lim].
    exists N. intros. rewrite plus_comm. apply lim. apply (le_trans N i).
    assumption. rewrite <- (plus_0_r i). rewrite <- plus_assoc.
    apply Nat.add_le_mono_l. apply le_0_n.
  - apply CR_cv_plus. 2: apply CR_cv_const. intros eps.
    specialize (H0 eps) as [N lim].
    exists N. intros. rewrite plus_comm. apply lim. apply (le_trans N i).
    assumption. rewrite <- (plus_0_r i). rewrite <- plus_assoc.
    apply Nat.add_le_mono_l. apply le_0_n.
Qed.

Lemma series_cv_minus : forall {R : ConstructiveReals}
                          (u v : nat -> CRcarrier R) (s t : CRcarrier R),
    series_cv u s
    -> series_cv v t
    -> series_cv (fun n => u n - v n) (s - t).
Proof.
  intros. apply (CR_cv_eq _ (fun n => CRsum u n - CRsum v n)).
  intro n. symmetry. unfold CRminus. rewrite sum_plus.
  rewrite sum_opp. reflexivity.
  apply CR_cv_plus. exact H. apply CR_cv_opp. exact H0.
Qed.

Lemma series_cv_le : forall {R : ConstructiveReals}
                       (un vn : nat -> CRcarrier R) (a b : CRcarrier R),
    (forall n:nat, un n <= vn n)
    -> series_cv un a
    -> series_cv vn b
    -> a <= b.
Proof.
  intros. apply (CRplus_le_reg_r (-a)). rewrite CRplus_opp_r.
  apply (series_cv_nonneg (fun n => vn n - un n)).
  intro n. apply (CRplus_le_reg_r (un n)).
  rewrite CRplus_0_l. unfold CRminus.
  rewrite CRplus_assoc, CRplus_opp_l, CRplus_0_r.
  apply H. apply series_cv_minus; assumption.
Qed.

Lemma series_cv_series : forall {R : ConstructiveReals}
                           (u : nat -> nat -> CRcarrier R) (s : nat -> CRcarrier R) (n : nat),
    (forall i:nat, le i n -> series_cv (u i) (s i))
    -> series_cv (fun i => CRsum (fun j => u j i) n) (CRsum s n).
Proof.
  induction n.
  - intros. simpl. specialize (H O).
    apply (series_cv_eq (u O)). reflexivity. apply H. apply le_refl.
  - intros. simpl. apply (series_cv_plus). 2: apply (H (S n)).
    apply IHn. 2: apply le_refl. intros. apply H.
    apply (le_trans _ n _ H0). apply le_S. apply le_refl.
Qed.

Lemma CR_cv_shift :
  forall {R : ConstructiveReals} f k l,
    CR_cv R (fun n => f (n + k)%nat) l -> CR_cv R f l.
Proof.
  intros. intros eps.
  specialize (H eps) as [N Nmaj].
  exists (N+k)%nat. intros n H.
  destruct (Nat.le_exists_sub k n).
  apply (le_trans _ (N + k)). 2: exact H.
  apply (le_trans _ (0 + k)). apply le_refl.
  rewrite <- Nat.add_le_mono_r. apply le_0_n.
  destruct H0.
  subst n. apply Nmaj. unfold ge in H.
  rewrite <- Nat.add_le_mono_r in H. exact H.
Qed.

Lemma CR_cv_shift' :
  forall {R : ConstructiveReals} f k l,
    CR_cv R f l -> CR_cv R (fun n => f (n + k)%nat) l.
Proof.
  intros R f' k l cvf eps; destruct (cvf eps) as [N Pn].
  exists N; intros n nN; apply Pn; auto with arith.
Qed.

Lemma series_cv_shift :
  forall {R : ConstructiveReals} (f : nat -> CRcarrier R) k l,
    series_cv (fun n => f (S k + n)%nat) l
    -> series_cv f (l + CRsum f k).
Proof.
  intros. intro p. specialize (H p) as [n nmaj].
  exists (S k+n)%nat. intros. destruct (Nat.le_exists_sub (S k) i).
  apply (le_trans _ (S k + 0)). rewrite Nat.add_0_r. apply le_refl.
  apply (le_trans _ (S k + n)). apply Nat.add_le_mono_l, le_0_n.
  exact H. destruct H0. subst i.
  rewrite Nat.add_comm in H. rewrite <- Nat.add_le_mono_r in H.
  specialize (nmaj x H). unfold CRminus.
  rewrite Nat.add_comm, (sum_assoc f k x).
  setoid_replace (CRsum f k + CRsum (fun k0 : nat => f (S k + k0)%nat) x - (l + CRsum f k))
    with (CRsum (fun k0 : nat => f (S k + k0)%nat) x - l).
  exact nmaj. unfold CRminus. rewrite (CRplus_comm (CRsum f k)).
  rewrite CRplus_assoc. apply CRplus_morph. reflexivity.
  rewrite CRplus_comm, CRopp_plus_distr, CRplus_assoc.
  rewrite CRplus_opp_l, CRplus_0_r. reflexivity.
Qed.

Lemma series_cv_shift' : forall {R : ConstructiveReals}
                           (un : nat -> CRcarrier R) (s : CRcarrier R) (shift : nat),
    series_cv un s
    -> series_cv (fun n => un (n+shift)%nat)
                       (s - match shift with
                            | O => 0
                            | S p => CRsum un p
                            end).
Proof.
  intros. destruct shift as [|p].
  - unfold CRminus. rewrite CRopp_0. rewrite CRplus_0_r.
    apply (series_cv_eq un). intros.
    rewrite plus_0_r. reflexivity. apply H.
  - apply (CR_cv_eq _ (fun n => CRsum un (n + S p) - CRsum un p)).
    intros. rewrite plus_comm. unfold CRminus.
    rewrite sum_assoc. simpl. rewrite CRplus_comm, <- CRplus_assoc.
    rewrite CRplus_opp_l, CRplus_0_l.
    apply CRsum_eq. intros. rewrite (plus_comm i). reflexivity.
    apply CR_cv_plus. apply (CR_cv_shift' _ (S p) _ H).
    intros n. exists (Pos.to_nat n). intros.
    unfold CRminus. simpl.
    rewrite CRopp_involutive, CRplus_opp_l. rewrite CRabs_right.
    rewrite <- CR_of_Q_zero. apply CR_of_Q_le. discriminate. apply CRle_refl.
Qed.
