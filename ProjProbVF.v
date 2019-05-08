Require Import ZArith. 
Require Import List.

Set Implicit Arguments.

Open Scope Z.

(*Expressões sem variáveis*)
(*Usar "Section" seja melhor*)
(*1*)

Inductive Op : Type :=
  | P   : Op
  | M   : Op
  | MM  : Op.


Inductive aexp :=
  | Leaf : Z -> aexp
  | Node : aexp -> Op -> aexp -> aexp.

(*2*)

Fixpoint aeval (a : aexp) : Z :=
    match a with
    | Leaf n => n 
    | Node L P R  => aeval L + aeval R
    | Node L M R  => aeval L - aeval R
    | Node L MM R => aeval L * aeval R
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

Inductive Exp : Type :=
  | Num   : Z -> Exp
  | Pls   : Exp
  | Min   : Exp
  | Mul   : Exp
  | LP    : Exp
  | RP    : Exp.

Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
End ListNotations.

Import ListNotations.

Fixpoint abc (a : aexp) : list Exp :=
   match a with
    | Node L P R  => [LP] ++ abc L ++ [RP] ++ [Pls] ++ [LP] ++ abc R ++ [RP] 
    | Node L M R  => [LP] ++ abc L ++ [RP] ++ [Min] ++ [LP] ++ abc R ++ [RP]  
    | Node L MM R => [LP] ++ abc L ++ [RP] ++ [Mul] ++ [LP] ++ abc R ++ [RP] 
    | Leaf n => [Num n] 
end.
Eval compute in abc ([2];*;[3]).

Eval compute in abc (([2];*;[3]);+;([3];*;([4];-;[2])))

isto é equivalente a : ((2) * (3)) + ((3) *((4)-(2)))

Eval compute in ((2) * (3)) + ((3) *((4)-(2))).

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

