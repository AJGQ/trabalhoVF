Require Import ZArith. 
Require Import List.
Require Import String.
Open Scope Z_scope.
Open Scope string_scope.
Set Implicit Arguments.

(****Expressoes sem Variaveis****)
Print string.
(*1*)



Inductive Op : Type :=
  | P   : Op
  | M   : Op
  | MM  : Op.

Let var := string.
Inductive El : Type :=
  | Elem  : Z -> El
  | Var   : var -> El.

Inductive aexp :=
  | Leaf : El -> aexp
  | Node : aexp -> Op -> aexp -> aexp.

Let init : var -> Z := fun _ => 0.

Fixpoint update (s : var -> Z) (v : var) (z : Z)  : var -> Z :=
  fun x => if (String:eqb x v) then z else s x.
(*2*)

Eval compute in (Pair 1 2).

Fixpoint find (v : var) (s : state) : Z :=
  match s with
  | nil => 0
  | cons (Pair _ z) _ => z
  end.

Eval compute in find 1%nat (cons (Pair var Z 0%nat (-1)) nil).

Fixpoint aeval (a : aexp) (s : state) : Z :=
    match a with
    | Leaf (Elem n) => n
    | Leaf (Var n) => Z.of_nat n
    | Node L P R  => aeval L s + aeval R s
    | Node L M R  => aeval L s - aeval R s
    | Node L MM R => aeval L s * aeval R s
end.

Module TreeNotations.
Notation "( L ; + ; R )" := (Node L P R).
Notation "( L ; - ; R )" := (Node L M R).
Notation "( L ; * ; R )" := (Node L MM R).
Notation "[ x ]" := (Leaf x).
End TreeNotations.

Import TreeNotations.
Open Scope Z.

(*3*)

Eval compute in (2*3)+(3*(4-2)).

Eval compute in aeval (([2];*;[3]);+;([3];*;([4];-;[2]))).

Eval compute in (20-40)*(30+(1*1)).

Eval compute in aeval (([20];-;[40]);*;([30];+;([1];*;[1]))).

(*4*)

Fixpoint aevalR (a : aexp) (n : Z) : Prop :=
  match a with
  | Leaf z => z = n 
  | Node a1 op a2 => 
      match op with 
      | P =>
          exists (n1 n2: Z),  aevalR a1 n1 /\ aevalR a2 n2 /\ n1 + n2 = n
      | M => 
          exists (n1 n2: Z),  aevalR a1 n1 /\ aevalR a2 n2 /\ n1 - n2 = n
      | MM => 
          exists (n1 n2: Z),  aevalR a1 n1 /\ aevalR a2 n2 /\ n1 * n2 = n
     end
  end.
(*5*)

Theorem RelEqFun : forall (a : aexp) (n : Z),
                    (aevalR a n) <-> (aeval a = n).
Proof.
  induction a.
  - simpl. intros. reflexivity.
  - red. intros. induction o.
    + split.
        simpl. intros. 
        destruct H as [n1 H]. 
        destruct H as [n2 H]. 
        destruct H. destruct H0. 
        assert (IHa1 := (IHa1 n1)).
        assert (IHa2 := (IHa2 n2)).
        unfold iff in IHa1; destruct IHa1; clear H3.
        unfold iff in IHa2; destruct IHa2; clear H4.
        assert (H5 := (H2 H)).
        assert (H6 := (H3 H0)).
        rewrite H5; rewrite H6.
        assumption.
      * simpl. intros.
        assert (IHa1 := (IHa1 (aeval a1))).
        assert (IHa2 := (IHa2 (aeval a2))).
        unfold iff in IHa1; destruct IHa1; clear H0.
        unfold iff in IHa2. destruct IHa2. clear H0.
        exists (aeval a1); exists (aeval a2).
        auto.
    + split.
      * simpl. intros. 
        destruct H as [n1 H]. 
        destruct H as [n2 H]. 
        destruct H. destruct H0. 
        assert (IHa1 := (IHa1 n1)).
        assert (IHa2 := (IHa2 n2)).
        unfold iff in IHa1; destruct IHa1; clear H3.
        unfold iff in IHa2; destruct IHa2; clear H4.
        assert (H5 := (H2 H)).
        assert (H6 := (H3 H0)).
        rewrite H5; rewrite H6.
        assumption.
      * simpl. intros.
        assert (IHa1 := (IHa1 (aeval a1))).
        assert (IHa2 := (IHa2 (aeval a2))).
        unfold iff in IHa1; destruct IHa1; clear H0.
        unfold iff in IHa2. destruct IHa2. clear H0.
        exists (aeval a1); exists (aeval a2).
        auto.
    + split.
      * simpl. intros. 
        destruct H as [n1 H]. 
        destruct H as [n2 H]. 
        destruct H. destruct H0. 
        assert (IHa1 := (IHa1 n1)).
        assert (IHa2 := (IHa2 n2)).
        unfold iff in IHa1; destruct IHa1; clear H3.
        unfold iff in IHa2; destruct IHa2; clear H4.
        assert (H5 := (H2 H)).
        assert (H6 := (H3 H0)).
        rewrite H5; rewrite H6.
        assumption.
      * simpl. intros.
        assert (IHa1 := (IHa1 (aeval a1))).
        assert (IHa2 := (IHa2 (aeval a2))).
        unfold iff in IHa1; destruct IHa1; clear H0.
        unfold iff in IHa2. destruct IHa2. clear H0.
        exists (aeval a1); exists (aeval a2).
        auto.
Qed.

(****Maquina de Stack****)
Let stack     := list Z.

Inductive Exp : Type :=
  | Num   : Z -> Exp
  | Pls   : Exp
  | Min   : Exp
  | Mul   : Exp.

Let stack_exp := list Exp.

Fixpoint SPush (n : Z) (st : stack) : stack :=
  cons n st.

Fixpoint SPlus (st : stack) : option stack :=
  match st with
  | nil => None
  | cons a nil => None
  | cons a (cons b c) => Some (cons (b+a) c)
  end.

Fixpoint SMinus (st : stack) : option stack :=
  match st with
  | nil => None
  | cons a nil => None
  | cons a (cons b c) => Some (cons (b-a) c)
  end.


Fixpoint SMult (st : stack) : option stack :=
  match st with
  | nil => None
  | cons a nil => None
  | cons a (cons b c) => Some (cons (b*a) c)
  end.
(*1*)
Fixpoint execute (s : stack) (a : aexp) : option Z :=
  match a with
  | nil => 
      match s with
      | cons e nil => Some e
      | _ => None
      end
  | cons (Num n) a' => execute (SPush n s) a'
  | cons Pls a'     => 
      match SPlus s with
      | Some s' => execute s' a'
      | None => None
      end
  | cons Min a'     => 
      match SMinus s with
      | Some s' => execute s' a'
      | None => None
      end
  | cons Mul a'     => 
      match SMult s with
      | Some s' => execute s' a'
      | None => None
      end
  end.

(*2*)
Let stack_machine : stack := nil. 
Let expression    : aexp  := cons (Num 2) (
                             cons (Num 3) (
                             cons Mul ( 
                             cons (Num 3) ( 
                             cons (Num 4) ( 
                             cons (Num 2) ( 
                             cons Min ( 
                             cons Mul ( 
                             cons Pls ( 
                             nil))))))))).
Eval compute in execute stack_machine expression.

Fixpoint aeval (a : aexp) : option Z :=
  execute nil a.

Eval compute in aeval expression.

Eval compute in 10 = 10+2.

(*3*)
(*
    Decidimos usar o option para que saibamos quando realmente deu problema ou    nao.
    *)
