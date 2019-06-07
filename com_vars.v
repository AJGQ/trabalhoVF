Require Import ZArith. 
Require Import List.
Require Import String.

Open Scope Z_scope.
Delimit Scope string_scope with string.
Local Open Scope string_scope.
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
  | Num  : Z -> El
  | Var   : var -> El.

Inductive aexp :=
  | Leaf : El -> aexp
  | Node : aexp -> Op -> aexp -> aexp.

Let state := var -> Z.
Let init : state := fun _ => 0.

Let update (s : state) (v : var) (z : Z) : state :=
  fun x => if (string_dec x v)%string then z else s x.
(*2*)

Eval compute in "123".
Eval compute in init "x".
Eval compute in update init "x" 3 "x".
Eval compute in update init "x" 3 "y".

Fixpoint aeval (a : aexp) (s : state) : Z :=
    match a with
    | Leaf (Num n) => n
    | Leaf (Var n) => s n
    | Node L P R  => aeval L s + aeval R s
    | Node L M R  => aeval L s - aeval R s
    | Node L MM R => aeval L s * aeval R s
end.

Module TreeNotations.
Notation "( L ; + ; R )" := (Node L P R).
Notation "( L ; - ; R )" := (Node L M R).
Notation "( L ; * ; R )" := (Node L MM R).
Notation "[ x ]" := (Leaf (Num x)).
Notation "[[ x ]]" := (Leaf (Var x)).
End TreeNotations.

Import TreeNotations.
Open Scope Z.

(*3*)

Eval compute in (2*3)+(3*(4-2)).

Eval compute in aeval (([2];*;[3]);+;([3];*;([4];-;[2]))) init.

Eval compute in (20-40)*(30+(1*1)).

Eval compute in aeval (([20];-;[40]);*;([30];+;([1];*;[1]))) init.

Eval compute in aeval (([20];-;[40]);*;([30];+;([["x"]];*;[["x"]]))) (update init "x" 1).

(*4*)

Fixpoint aevalR (a : aexp) (n : Z) (s : state) : Prop :=
  match a with
  | Leaf (Num z) => z = n 
  | Leaf (Var v)  => s v = n 
  | Node a1 op a2 => 
      match op with 
      | P =>
          exists (n1 n2: Z),  aevalR a1 n1 s /\ aevalR a2 n2 s /\ n1 + n2 = n
      | M => 
          exists (n1 n2: Z),  aevalR a1 n1 s /\ aevalR a2 n2 s /\ n1 - n2 = n
      | MM => 
          exists (n1 n2: Z),  aevalR a1 n1 s /\ aevalR a2 n2 s /\ n1 * n2 = n
     end
  end.
(*5*)

Theorem RelEqFun : forall (a : aexp) (n : Z) (s : state),
                    (aevalR a n s) <-> (aeval a s = n).
Proof.
  induction a.
  - intros. 
    induction e.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - red. intros. induction o.
    + split.
      * simpl. intros. 
        destruct H as [n1 H]. 
        destruct H as [n2 H]. 
        destruct H. destruct H0. 
        assert (IHa1 := (IHa1 n1 s)).
        assert (IHa2 := (IHa2 n2 s)).
        unfold iff in IHa1; destruct IHa1; clear H3.
        unfold iff in IHa2; destruct IHa2; clear H4.
        assert (H5 := (H2 H)).
        assert (H6 := (H3 H0)).
        rewrite H5; rewrite H6.
        assumption.
      * simpl. intros.
        assert (IHa1 := (IHa1 (aeval a1 s) s)).
        assert (IHa2 := (IHa2 (aeval a2 s) s)).
        unfold iff in IHa1; destruct IHa1; clear H0.
        unfold iff in IHa2. destruct IHa2. clear H0.
        exists (aeval a1 s); exists (aeval a2 s).
        auto.
    + split.
      * simpl. intros. 
        destruct H as [n1 H]. 
        destruct H as [n2 H]. 
        destruct H. destruct H0. 
        assert (IHa1 := (IHa1 n1 s)).
        assert (IHa2 := (IHa2 n2 s)).
        unfold iff in IHa1; destruct IHa1; clear H3.
        unfold iff in IHa2; destruct IHa2; clear H4.
        assert (H5 := (H2 H)).
        assert (H6 := (H3 H0)).
        rewrite H5; rewrite H6.
        assumption.
      * simpl. intros.
        assert (IHa1 := (IHa1 (aeval a1 s) s)).
        assert (IHa2 := (IHa2 (aeval a2 s) s)).
        unfold iff in IHa1; destruct IHa1; clear H0.
        unfold iff in IHa2. destruct IHa2. clear H0.
        exists (aeval a1 s); exists (aeval a2 s).
        auto.
    + split.
      * simpl. intros. 
        destruct H as [n1 H]. 
        destruct H as [n2 H]. 
        destruct H. destruct H0. 
        assert (IHa1 := (IHa1 n1 s)).
        assert (IHa2 := (IHa2 n2 s)).
        unfold iff in IHa1; destruct IHa1; clear H3.
        unfold iff in IHa2; destruct IHa2; clear H4.
        assert (H5 := (H2 H)).
        assert (H6 := (H3 H0)).
        rewrite H5; rewrite H6.
        assumption.
      * simpl. intros.
        assert (IHa1 := (IHa1 (aeval a1 s) s)).
        assert (IHa2 := (IHa2 (aeval a2 s) s)).
        unfold iff in IHa1; destruct IHa1; clear H0.
        unfold iff in IHa2. destruct IHa2. clear H0.
        exists (aeval a1 s); exists (aeval a2 s).
        auto.
Qed.

(****Maquina de Stack****)
Let stack     := list Z.

Inductive Exp : Type :=
  | Elm   : El -> Exp
  | Pls   : Exp
  | Min   : Exp
  | Mul   : Exp.

Let stack_exp := list Exp.

Definition SPush (n : Z) (st : stack) : stack :=
  cons n st.

Definition SLoad (x : var) (st : stack) (s : state) : stack :=
  cons (s x) st. 

Definition SPlus (st : stack) : option stack :=
  match st with
    | nil => None
    | cons a nil => None
    | cons a (cons b c) => Some (cons (b+a) c)
  end.

Definition SMinus (st : stack) : option stack :=
  match st with
    | nil => None
    | cons a nil => None
    | cons a (cons b c) => Some (cons (b-a) c)
  end.


Definition SMult (st : stack) : option stack :=
  match st with
    | nil => None
    | cons a nil => None
    | cons a (cons b c) => Some (cons (b*a) c)
  end.

(*1*)
Fixpoint execute (s : state) (st : stack) (a : stack_exp) : option stack :=
  match a with
  | nil => Some st
  | cons (Elm (Num n)) a' => execute s (SPush n st) a'
  | cons (Elm (Var v)) a' => execute s (SLoad v st s) a'
  | cons Pls a'     => 
      match SPlus st with
      | Some st' => execute s st' a'
      | None => None
      end
  | cons Min a'     => 
      match SMinus st with
      | Some st' => execute s st' a'
      | None => None
      end
  | cons Mul a'     => 
      match SMult st with
      | Some st' => execute s st' a'
      | None => None
      end
  end.


(*2*)
Let stack_machine : stack := nil. 
Let expression    : stack_exp  := cons (Elm(Num 2)) (
                             cons (Elm(Num 3)) (
                             cons Mul ( 
                             cons (Elm(Num 3)) ( 
                             cons (Elm(Num 4)) ( 
                             cons (Elm(Num 2)) ( 
                             cons Min ( 
                             cons Mul ( 
                             cons Pls ( 
                             nil))))))))).
Eval compute in execute init stack_machine expression.

(*3*)
(*
    Decidimos usar o option para que saibamos quando realmente deu problema ou nao.
    *)


Local Open Scope list.

(****Compilador****)
Fixpoint compile (a : aexp) : stack_exp := 
  match a with
  | Leaf e => cons (Elm e) nil
  | Node l P r => compile l ++ compile r ++ cons Pls nil
  | Node l M r => compile l ++ compile r ++ cons Min nil
  | Node l MM r => compile l ++ compile r ++ cons Mul nil
  end.


Eval compute in execute init nil (compile (([2];*;[3]);+;([3];*;([4];-;[2])))).

Lemma Dinamic_Execute (z : Z) (se1 se2 : stack_exp) :
  forall (st st1 : stack) (s : state),
    execute s st se1 = Some (z :: nil) -> 
    execute s (st ++ st1) (se1 ++ se2) = execute s (z :: st1) se2.
Proof.
  induction se1.
  - simpl.
    intros.
    inversion H.
    simpl.
    reflexivity.
  - induction a. induction e.
    + simpl.
      intros.
      apply (IHse1 (z0 :: st) st1 s).
      assumption.
    + simpl.
      intros.
      apply (IHse1 ((s v) :: st) st1 s).
      assumption.
    + induction st.
      * intros.
        simpl in H.
        inversion H.
      * induction st.
        -- intros.
           simpl in H.
           inversion H.
        -- simpl.
           intros.
           apply (IHse1 ((a0 + a) :: st) st1).
           assumption.
    + induction st.
      * intros.
        simpl in H.
        inversion H.
      * induction st.
        -- intros.
           simpl in H.
           inversion H.
        -- simpl.
           intros.
           apply (IHse1 ((a0 - a) :: st) st1).
           assumption.
    + induction st.
      * intros.
        simpl in H.
        inversion H.
      * induction st.
        -- intros.
           simpl in H.
           inversion H.
        -- simpl.
           intros.
           apply (IHse1 ((a0 * a) :: st) st1).
           assumption.
Qed. 
(*
Lemma Dinamic_Execute (z : Z) (se1 se2 : stack_exp):
  forall (st st1 : stack),
    execute st se1 = Some (z :: nil) -> 
    execute (st ++ st1) (se1 ++ se2) = execute (z :: st1) se2.
      *)
Theorem Correction : forall (a : aexp) (s : state),
                     (execute s nil (compile a) = Some (cons (aeval a s) nil)).
Proof.
  intros.
  induction a. induction e.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - induction o.
    + simpl. 
      assert (H := ((Dinamic_Execute (aeval a1 s) (compile a1) (compile a2 ++ Pls :: nil) nil nil s) IHa1)).
      assert (H1 := ((Dinamic_Execute (aeval a2 s) (compile a2) (Pls :: nil) nil (aeval a1 s :: nil) s) IHa2)).
      rewrite <- (app_nil_end nil) in H.
      simpl in H1.
      rewrite H.
      rewrite H1.
      simpl.
      reflexivity.
    + simpl. 
      assert (H := ((Dinamic_Execute (aeval a1 s) (compile a1) (compile a2 ++ Min :: nil) nil nil s) IHa1)).
      assert (H1 := ((Dinamic_Execute (aeval a2 s) (compile a2) (Min :: nil) nil (aeval a1 s :: nil) s) IHa2)).
      rewrite <- (app_nil_end nil) in H.
      simpl in H1.
      rewrite H.
      rewrite H1.
      simpl.
      reflexivity.
    + simpl. 
      assert (H := ((Dinamic_Execute (aeval a1 s) (compile a1) (compile a2 ++ Mul :: nil) nil nil s) IHa1)).
      assert (H1 := ((Dinamic_Execute (aeval a2 s) (compile a2) (Mul :: nil) nil (aeval a1 s :: nil) s) IHa2)).
      rewrite <- (app_nil_end nil) in H.
      simpl in H1.
      rewrite H.
      rewrite H1.
      simpl.
      reflexivity.
Qed.
