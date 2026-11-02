(** * System T: functions and iteration

    System T extends Razor's idea with functions, variables and iteration
    over natural numbers. Terms use de Bruijn indices: a variable is a
    position in the context of types. *)

From Stdlib Require Import List.
Import ListNotations.

(** * Syntax *)

Inductive Ty : Type :=
| Nat : Ty
| Arr : Ty -> Ty -> Ty.
Notation "A ==> B" := (Arr A B) (at level 55, right associativity).

Definition Ctx := list Ty.

Inductive Var : Ctx -> Ty -> Type :=
| vz : forall {G A}, Var (A :: G) A
| vs : forall {G A B}, Var G A -> Var (B :: G) A.

(** [ite z s n] starts from [z] and applies [s] to it [n] times. The body of
    [s] sees the previous result as variable [vz]. *)
Inductive Tm : Ctx -> Ty -> Type :=
| var  : forall {G A}, Var G A -> Tm G A
| lam  : forall {G A B}, Tm (A :: G) B -> Tm G (A ==> B)
| app  : forall {G A B}, Tm G (A ==> B) -> Tm G A -> Tm G B
| zero : forall {G}, Tm G Nat
| suc  : forall {G}, Tm G Nat -> Tm G Nat
| ite  : forall {G A}, Tm G A -> Tm (A :: G) A -> Tm G Nat -> Tm G A.

(** * Evaluator

    Each type means a Rocq type, and a term becomes a Rocq function of its
    environment. Rocq accepts [eval], so evaluation always terminates. *)

Fixpoint den (A : Ty) : Type :=
  match A with
  | Nat => nat
  | A ==> B => den A -> den B
  end.

Fixpoint Env (G : Ctx) : Type :=
  match G with
  | [] => unit
  | A :: G => den A * Env G
  end.

Fixpoint lookup {G A} (x : Var G A) : Env G -> den A :=
  match x with
  | vz => fun env => fst env
  | vs y => fun env => lookup y (snd env)
  end.

Fixpoint iter {A : Type} (z : A) (s : A -> A) (n : nat) : A :=
  match n with
  | 0 => z
  | S n => s (iter z s n)
  end.

Fixpoint eval {G A} (t : Tm G A) : Env G -> den A :=
  match t with
  | var x => fun env => lookup x env
  | lam b => fun env a => eval b (a, env)
  | app f a => fun env => eval f env (eval a env)
  | zero => fun _ => 0
  | suc n => fun env => S (eval n env)
  | ite z s n => fun env =>
      iter (eval z env) (fun r => eval s (r, env)) (eval n env)
  end.

Definition run {A} (t : Tm [] A) : den A := eval t tt.

(** * Iteration law *)

Lemma iter_add : forall (A : Type) (z : A) s m n,
  iter z s (m + n) = iter (iter z s n) s m.
Proof.
  intros A z s m n.
  induction m.
  - reflexivity.
  - simpl. rewrite IHm. reflexivity.
Qed.

(** * Programs

    The theorems below hold for every input, not only for tested values. *)

Definition v0 {G A} : Tm (A :: G) A := var vz.
Definition v1 {G A B} : Tm (B :: A :: G) A := var (vs vz).
Definition v2 {G A B C} : Tm (C :: B :: A :: G) A := var (vs (vs vz)).

(** ** Doubling *)

Definition double : Tm [] (Nat ==> Nat) :=
  lam (ite zero (suc (suc v0)) v0).

Theorem double_correct : forall n, run double n = n + n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - cbn in *. rewrite IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.

(** ** Parity

    [flip] maps 0 to 1 and every other number to 0. *)

Definition flip {G} (t : Tm G Nat) : Tm G Nat :=
  ite (suc zero) zero t.

Definition parity : Tm [] (Nat ==> Nat) :=
  lam (ite zero (flip v0) v0).

Lemma parity_suc : forall n,
  run parity (S n) = iter 1 (fun _ => 0) (run parity n).
Proof. reflexivity. Qed.

(** The result is always 0 or 1. *)
Lemma parity_bit : forall n, run parity n = 0 \/ run parity n = 1.
Proof.
  intros n.
  induction n.
  - left. reflexivity.
  - rewrite parity_suc. destruct IHn as [H | H].
    + right. rewrite H. reflexivity.
    + left. rewrite H. reflexivity.
Qed.

Lemma parity_add2 : forall n, run parity (S (S n)) = run parity n.
Proof.
  intros n.
  rewrite parity_suc, parity_suc.
  destruct (parity_bit n) as [H | H].
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
Qed.

(** Every doubled number is even. *)
Theorem parity_double : forall n, run parity (run double n) = 0.
Proof.
  intros n.
  rewrite double_correct.
  induction n.
  - reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite parity_add2. exact IHn.
Qed.

(** ** Ackermann

    The Ackermann function is not primitive recursive, but System T defines
    it because [ite] can iterate at the function type [Nat ==> Nat]. *)

Definition ack : Tm [] (Nat ==> Nat ==> Nat) :=
  lam (ite (lam (suc v0))
           (lam (ite (app v1 (suc zero)) (app v2 v0) v0))
           v0).

Example ack_1_1 : run ack 1 1 = 3.
Proof. reflexivity. Qed.

Example ack_2_3 : run ack 2 3 = 9.
Proof. reflexivity. Qed.

Example ack_3_3 : run ack 3 3 = 61.
Proof. reflexivity. Qed.
