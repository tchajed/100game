(** * Puzzle: The Sum Game *)

(** Consider the following game: two players take turns adding a
    number from 1-10 to a shared sum. The player who makes the
    sum 100 wins. Who wins, and how?

    #
    <a href="coq/problem.v">Download the Coq source!</a>
    #

*)

(** A "state" is a natural number representing how much
    remains between the current sum and the total (which
    is 100 in this case. *)
Definition state := nat.

(** A valid change in state is one which is between 1 and 10. *)
Inductive validDiff : nat -> Prop :=
| validDiff_inbounds : forall n, 1 <= n ->
                            n <= 10 ->
                            validDiff n.

(** [action n n'] is true if it is a valid move to
    change the state from [n] to [n'] *)
Definition action : state -> state -> Prop :=
  fun n n' => validDiff (n - n').

(** A definition of what it means for the current player
    to lose or win from a current state. *)
Inductive LoseFrom : state -> Prop :=
| AllWin : forall n,
    (forall n', action n n' -> WinFrom n') ->
    LoseFrom n
with WinFrom : nat -> Prop :=
     | CanForce : forall n n',
         action n n' ->
         LoseFrom n' ->
         WinFrom n.

(** The total target cumulative sum, which is also the starting
    state.*)
Definition total : nat := 100.

(** The formal problem statement: Does the first player to play
    win or lose? *)
Definition Puzzle : Type := WinFrom total + LoseFrom total.

Theorem PuzzleSolution : Puzzle.
Proof.
unfold Puzzle.
Abort.