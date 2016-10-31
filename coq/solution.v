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

Hint Constructors LoseFrom WinFrom.
Hint Constructors validDiff.

Lemma action_def : forall n n',
    1 <= n - n' ->
    n - n' <= 10 ->
    action n n'.
Proof.
  unfold action; eauto.
Qed.

Hint Resolve action_def.

Hint Extern 3 (_ <= _) => omega.

Lemma LoseFrom0 : LoseFrom 0.
Proof.
  constructor.
  inversion 1.
  omega.
Qed.

Lemma WinFrom_n : forall n,
    LoseFrom n ->
    forall n' k,
      n' = n + S k ->
      k < 10 ->
      WinFrom n'.
Proof.
  intros. subst.
  econstructor; eauto.
  eauto.
Qed.

Ltac winfrom_n :=
  match goal with
  | [ H: LoseFrom ?n |- WinFrom ?n' ] =>
    apply (WinFrom_n _ H n' (n' - n - 1)); try omega
  end.

Lemma LoseFrom_n : forall n,
    LoseFrom n ->
    forall m, 11 + n = m ->
    LoseFrom m.
Proof.
  intros; subst.
  constructor; intros.
  inversion H0; subst.
  winfrom_n.
Qed.

Lemma mod_add_rem : forall k n r,
    k <> 0 ->
    r < k ->
    (k * n + r) mod k = r.
Proof.
  intros.
  rewrite plus_comm.
  rewrite mul_comm.
  rewrite mod_add by auto.
  apply mod_small; auto.
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
    + pose proof LoseFrom0.
      winfrom_n.
  - rewrite mod_add_rem by omega. destruct n2.
    + specialize (H 0 ltac:(auto)).
      rewrite mod_add_rem in H by omega.
      eapply LoseFrom_n; eauto.
      omega.
    + specialize (H 0 ltac:(omega)).
      rewrite mod_add_rem in H by omega.
      eapply LoseFrom_n in H; eauto.
      winfrom_n.
Qed.

Theorem solution : WinFrom 100.
Proof.
  apply (solution_all 100).
Qed.