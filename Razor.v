(** * Razor: a small typed language with a verified compiler

    Razor has numbers, booleans, addition, a zero test and if-then-else.
    This file gives it an evaluator, an optimiser and a compiler to a stack
    machine, and proves that the optimiser and compiler preserve meaning. *)

From Stdlib Require Import List Program.Equality.
Import ListNotations.

(** * Syntax

    [Tm A] is the type of terms of type [A], so ill-typed terms such as
    [plus tru (num 1)] are rejected by Rocq. *)

Inductive Ty : Type := TBool | TNat.

Inductive Tm : Ty -> Type :=
| tru    : Tm TBool
| fls    : Tm TBool
| num    : nat -> Tm TNat
| plus   : Tm TNat -> Tm TNat -> Tm TNat
| isZero : Tm TNat -> Tm TBool
| ite    : forall {A}, Tm TBool -> Tm A -> Tm A -> Tm A.

(** * Evaluator *)

Definition den (A : Ty) : Type :=
  match A with
  | TBool => bool
  | TNat => nat
  end.

Definition zeroTest (n : nat) : bool :=
  match n with
  | 0 => true
  | S _ => false
  end.

Fixpoint eval {A} (t : Tm A) : den A :=
  match t with
  | tru => true
  | fls => false
  | num n => n
  | plus t u => eval t + eval u
  | isZero t => zeroTest (eval t)
  | ite b u v => if eval b then eval u else eval v
  end.

(** * Optimiser: constant folding

    Each helper simplifies one operator when its arguments are constants. *)

Definition optPlus (t u : Tm TNat) : Tm TNat :=
  match t, u with
  | num a, num b => num (a + b)
  | _, _ => plus t u
  end.

Definition optIsZero (t : Tm TNat) : Tm TBool :=
  match t with
  | num n => if zeroTest n then tru else fls
  | _ => isZero t
  end.

Definition optIte {A} (b : Tm TBool) (u v : Tm A) : Tm A :=
  match b with
  | tru => u
  | fls => v
  | _ => ite b u v
  end.

Fixpoint opt {A} (t : Tm A) : Tm A :=
  match t with
  | plus t u => optPlus (opt t) (opt u)
  | isZero t => optIsZero (opt t)
  | ite b u v => optIte (opt b) (opt u) (opt v)
  | t => t
  end.

Lemma optPlus_correct : forall t u, eval (optPlus t u) = eval t + eval u.
Proof.
  intros t u.
  dependent destruction t; dependent destruction u; reflexivity.
Qed.

Lemma optIsZero_correct : forall t, eval (optIsZero t) = zeroTest (eval t).
Proof.
  intros t.
  dependent destruction t; try reflexivity.
  destruct n; reflexivity.
Qed.

Lemma optIte_correct : forall A (b : Tm TBool) (u v : Tm A),
  eval (optIte b u v) = if eval b then eval u else eval v.
Proof.
  intros A b u v.
  dependent destruction b; reflexivity.
Qed.

Theorem opt_correct : forall A (t : Tm A), eval (opt t) = eval t.
Proof.
  intros A t.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite optPlus_correct, IHt1, IHt2. reflexivity.
  - rewrite optIsZero_correct, IHt. reflexivity.
  - rewrite optIte_correct, IHt1, IHt2, IHt3. reflexivity.
Qed.

Example opt_example :
  opt (ite (isZero (plus (num 0) (num 0))) (num 10) (num 20)) = num 10.
Proof. reflexivity. Qed.

(** * Stack machine

    [Code] is a sequence of instructions, each holding the code that runs
    after it. Both branches of [IF] continue on their own. *)

Inductive Val : Type :=
| B : bool -> Val
| N : nat -> Val.

Inductive Code : Type :=
| HALT   : Code
| PUSH   : Val -> Code -> Code
| ADD    : Code -> Code
| ISZERO : Code -> Code
| IF     : Code -> Code -> Code.

Definition Stack := list Val.

(** A badly formed stack stops the machine. The correctness theorem shows
    that compiled code never reaches those cases. *)
Fixpoint exec (c : Code) (s : Stack) : Stack :=
  match c, s with
  | HALT, s => s
  | PUSH v k, s => exec k (v :: s)
  | ADD k, N b :: N a :: s => exec k (N (a + b) :: s)
  | ISZERO k, N n :: s => exec k (B (zeroTest n) :: s)
  | IF k1 k2, B b :: s => if b then exec k1 s else exec k2 s
  | _, s => s
  end.

(** * Compiler

    [comp t k] is code that computes [t] and then continues with [k]. *)

Fixpoint comp {A} (t : Tm A) (k : Code) : Code :=
  match t with
  | tru => PUSH (B true) k
  | fls => PUSH (B false) k
  | num n => PUSH (N n) k
  | plus t u => comp t (comp u (ADD k))
  | isZero t => comp t (ISZERO k)
  | ite b u v => comp b (IF (comp u k) (comp v k))
  end.

Definition compile {A} (t : Tm A) : Code := comp t HALT.

Definition toVal {A} : den A -> Val :=
  match A with
  | TBool => B
  | TNat => N
  end.

(** The induction needs [k] and [s] to stay general, because subterms are
    compiled with a different continuation and run on a different stack. *)
Lemma comp_correct : forall A (t : Tm A) k s,
  exec (comp t k) s = exec k (toVal (eval t) :: s).
Proof.
  intros A t.
  induction t; intros k s; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1. simpl.
    destruct (eval t1).
    + rewrite IHt2. reflexivity.
    + rewrite IHt3. reflexivity.
Qed.

Theorem compile_correct : forall A (t : Tm A),
  exec (compile t) [] = [toVal (eval t)].
Proof.
  intros A t.
  unfold compile.
  rewrite comp_correct.
  reflexivity.
Qed.

(** Optimising first gives the same result. *)
Theorem compile_opt_correct : forall A (t : Tm A),
  exec (compile (opt t)) [] = [toVal (eval t)].
Proof.
  intros A t.
  rewrite compile_correct, opt_correct.
  reflexivity.
Qed.
