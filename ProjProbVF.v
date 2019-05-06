Require Import ZArith. 
Require Import List.

Set Implicit Arguments.

Open Scope Z_scope.

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

Notation a := aexp.

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

(*3*)

(*(2*3)+(3*(4-2))*)

Eval compute in (2*3)+(3*(4-2)).

Eval compute in aeval (([2];*;[3]);+;([3];*;([4];-;[2]))).

(*(20-40)*(30+(1*1)) *)

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

Eval compute in abc (([2];*;[3]);+;([3];*;([4];-;[2]))).

(* isto é equivalente a : ((2) * (3)) + ((3) *((4)-(2))) *) 

Eval compute in ((2) * (3)) + ((3) *((4)-(2))).

Fixpoint aevalR (a : aexp) (n : Z) : Prop :=
  (aeval a) = n.

(*5*)

Theorem RelEqFun : forall (a : aexp) (n : Z),
                    (aevalR a n) <-> (aeval a = n).
Proof.
  induction a.
    - intros.
      red.
      simpl.
      split;[intros; assumption | intros; assumption].
    - intros.
      red.
      split;[simpl; intros;assumption| simpl; intros;assumption].
Qed.


