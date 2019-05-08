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
  | MM   : Op.


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

(* Module ListNotations. *)
(* Notation "[ ]" := nil (format "[ ]") : list_scope. *)
(* Notation "[ x ]" := (cons x nil) : list_scope. *)
(* Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope. *)
(* End ListNotations. *)
(*  *)
(* Import ListNotations. *)
(*  *)
(* Fixpoint abc (a : aexp) : list Exp := *)
(*    match a with *)
(*     | Node L P R  => [LP] ++ abc L ++ [RP] ++ [Pls] ++ [LP] ++ abc R ++ [RP]  *)
(*     | Node L M R  => [LP] ++ abc L ++ [RP] ++ [Min] ++ [LP] ++ abc R ++ [RP]   *)
(*     | Node L MM R => [LP] ++ abc L ++ [RP] ++ [Mul] ++ [LP] ++ abc R ++ [RP]  *)
(*     | Leaf n => [Num n]  *)
(* end. *)
(* Eval compute in abc ([2];*;[3]). *)
(*  *)
(* Eval compute in abc (([2];*;[3]);+;([3];*;([4];-;[2]))). *)

(* isto é equivalente a : ((2) * (3)) + ((3) *((4)-(2))) *) 

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

Theorem RelEqFun : forall (a : aexp) (n : Z),
                    (aevalR a n) <-> (aeval a = n).
Proof.
  induction a.
  - red;intros;split.
      + intros. simpl. simpl in H. assumption.
      + intros; simpl; simpl in H; assumption.
  - intros;red;split.
      + intros. induction o.
          ++ simpl; simpl in H.
            destruct H. destruct H. destruct H. destruct H0.
            destruct IHa1 with x. destruct IHa2 with x0; clear IHa1; clear IHa2.
            symmetry.
            rewrite H4.
              * rewrite H2.
                -- symmetry. assumption.
                -- assumption.
              * assumption.
          ++  simpl; simpl in H; destruct H; destruct H; destruct H; destruct H0.
              destruct IHa1 with x; destruct IHa2 with x0; clear IHa1; clear IHa2.
              symmetry; rewrite H4.
                -- rewrite H2;[symmetry; assumption|assumption].
                -- assumption. 
          ++  simpl; simpl in H; destruct H; destruct H; destruct H; destruct H0.
              destruct IHa1 with x; destruct IHa2 with x0; clear IHa1; clear IHa2.
              symmetry;rewrite H4.
                -- rewrite H2;[symmetry; assumption|assumption].
                -- assumption.
        + intros. induction o.
            * simpl; simpl in H.
              exists (aeval a1). exists (aeval a2).
              split.
                **  apply IHa1.
                    reflexivity.
                ** split.
                    *** apply IHa2.
                        reflexivity.
                    *** assumption.
            * simpl; simpl in H; exists (aeval a1). exists (aeval a2);split.
                **  apply IHa1;reflexivity.
                ** split;[apply IHa2; reflexivity | assumption].
            * simpl; simpl in H; exists (aeval a1). exists (aeval a2);split.
                **  apply IHa1;reflexivity.
                ** split;[apply IHa2; reflexivity | assumption].
Qed.
