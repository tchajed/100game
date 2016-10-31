Require Import problem.
Require Import Arith Omega.
Import PeanoNat.Nat.

Definition pre_strategy :=
  state -> {m | m < 10}.

Definition strategy (s: pre_strategy) :
  forall n : state, {m | action (S n) m}.
Proof.
  intros.
  destruct (s (S n)) as [m ?].
  exists ((S n) - (1 + m)).
  unfold action; constructor; omega.
Qed.

Definition winning_pre_strategy : pre_strategy.
Proof.
  intro n.
  exists (n mod 11 - 1).
  pose proof (Nat.mod_upper_bound n 11); omega.
Defined.

Definition winning_strategy := strategy winning_pre_strategy.

Theorem mod_principle k (Heq0: k <> 0) :
  forall (P: nat -> Prop)
    (Hsmall: forall n, n < k -> P n)
    (Hind: forall p, (forall n, n < k -> P (k *   p + n)) ->
                (forall n, n < k -> P (k * S p + n))),
    (forall n, P n).
Proof.
  intros.
  pose proof (div_mod n k ltac:(auto)).
  remember (n / k) as p. remember (n mod k) as r.
  rewrite H.
  pose proof (mod_upper_bound n k ltac:(assumption)).
  rewrite <- Heqr in H0.
  clear n H Heqp Heqr.
  generalize dependent r.
  induction p.
  - rewrite mul_0_r in *; simpl in *.
    auto.
  - apply Hind. apply IHp.
Qed.

Inductive action' (n : state) : state -> Prop :=
  | mkaction : forall k, k < 10 -> action' n (n + S k).

Lemma action_action' : forall n m,
  action n m <-> action' m n.
Proof.
intros. split; intros.
- inversion H. clear H. subst.
  rewrite (le_plus_minus m n).
  pose proof (mkaction m (pred (n - m))).
  assert (n - m <> 0).
  unfold not. intros. omega.
  rewrite succ_pred in H by assumption. apply H.
  unfold "<". rewrite succ_pred by assumption.
  assumption. apply lt_le_weak.
  apply lt_O_minus_lt. assumption.
- induction H. econstructor; omega.
Qed.

Lemma LoseFrom0 : LoseFrom 0.
Proof.
econstructor.
intros. rewrite action_action' in H.
inversion H. omega.
Qed.

Lemma WinFrom_n : forall n k x, x = n + S k -> LoseFrom n -> k < 10 -> WinFrom x.
Proof.
intros. subst.
econstructor. 2:eassumption.
apply action_action'.
constructor. assumption.
Qed.

Lemma LoseFrom_n : forall n, LoseFrom n -> LoseFrom (11 + n).
Proof.
intros.
constructor.
intros.
inversion H0; subst.
eapply WinFrom_n.
2: eauto.
instantiate (1 := n' - n - 1).
omega.
omega.
Qed.

Theorem solution_all : forall n,
    match n mod 11 with
    | 0 => LoseFrom n
    | S _ => WinFrom n
    end.
Proof.
  intros.
  induction n using (mod_principle 11 ltac:(omega)).
  - rewrite mod_small by auto.
    destruct n.
    + apply LoseFrom0.
    + eapply WinFrom_n with 0 n. reflexivity.
      apply LoseFrom0. omega.
  - assert (forall p x, x < 11 -> (11 * p + x) mod 11 = x).
    intros. rewrite (plus_comm _ x).
    rewrite (mul_comm 11).
    rewrite mod_add by omega.
    rewrite mod_small by assumption. reflexivity.
    rewrite H1 by assumption. destruct n2.
    + specialize (H 0 ltac:(omega)).
      rewrite H1 in H by omega.
      rewrite plus_0_r in *.
      rewrite mul_comm. rewrite mul_comm in H. apply LoseFrom_n. apply H.
    + specialize (H 0 ltac:(omega)).
      rewrite H1 in H by omega.
      rewrite plus_0_r in H.
      apply LoseFrom_n in H.
      eapply WinFrom_n. 2:eassumption.
      instantiate (1 := n2). omega. omega.
Qed.

Theorem solution : WinFrom 100.
Proof.
apply (solution_all 100).
Qed.