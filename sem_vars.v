Require Import ZArith. 
Require Import List.
Open Scope Z_scope.

(****Expressoes sem Variaveis****)

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

Let SPush (n : Z) (st : stack) : stack :=
  cons n st.

Let SPlus (st : stack) : option stack :=
  match st with
    | nil => None
    | cons a nil => None
    | cons a (cons b c) => Some (cons (b+a) c)
  end.

Let SMinus (st : stack) : option stack :=
  match st with
    | nil => None
    | cons a nil => None
    | cons a (cons b c) => Some (cons (b-a) c)
  end.


Let SMult (st : stack) : option stack :=
  match st with
    | nil => None
    | cons a nil => None
    | cons a (cons b c) => Some (cons (b*a) c)
  end.

(*1*)
Fixpoint execute (s : stack) (a : stack_exp) : option stack :=
  match a with
  | nil => Some s 
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
Let expression    : stack_exp  := cons (Num 2) (
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

(*3*)
(*
    Decidimos usar o option para que saibamos quando realmente deu problema ou    nao.
    *)

(****Compilador****)
Fixpoint compile (a : aexp) : stack_exp := 
  match a with
  | Leaf z => cons (Num z) nil
  | Node l P r => compile l ++ compile r ++ cons Pls nil
  | Node l M r => compile l ++ compile r ++ cons Min nil
  | Node l MM r => compile l ++ compile r ++ cons Mul nil
  end.

Eval compute in execute nil (compile (([2];*;[3]);+;([3];*;([4];-;[2])))).

Let unSome (A : Type) (op : option A) (a : A) : A  := 
  match op with
  | Some a' => a'
  | None    => a
  end.
(*
Lemma Dinamic_Execute_aux (e : Exp) (se : stack_exp) (st st1 : stack) :
    execute st (e :: nil) = Some st1 ->
    execute st (e :: se) = execute st1 se.
Proof.
  intros.
  induction e.
  - simpl. 
    inversion H.
    reflexivity.
  - induction st.
    + inversion H.
    + induction st.
      * inversion H.
      * simpl. 
        inversion H.
        reflexivity.
  - induction st.
    + inversion H.
    + induction st.
      * inversion H.
      * simpl. 
        inversion H.
        reflexivity.
  - induction st.
    + inversion H.
    + induction st.
      * inversion H.
      * simpl. 
        inversion H.
        reflexivity.
Qed.  
*)
Lemma Dinamic_Execute (se1 se2 : stack_exp) (st1 st2 : stack) :
  forall (st : stack),
    execute st se1 = Some st1 -> 
    execute st1 se2 = Some st2 -> 
    execute st (se1 ++ se2) = Some st2.
Proof.
  induction se1.
  - simpl. intros. 
    inversion H.
    assumption.
  - induction a.
    + simpl.
      intros.
      apply (IHse1 (SPush z st)).
      assumption. assumption.
    + induction st.
      * simpl. intros. inversion H.
      * induction st.
        -- simpl. intros. inversion H.
        -- clear IHst0. simpl. intros.
           apply (IHse1 (a0 + a :: st)).
           assumption. assumption.
    + induction st.
      * simpl. intros. inversion H.
      * induction st.
        -- simpl. intros. inversion H.
        -- clear IHst0. simpl. intros.
           apply (IHse1 (a0 - a :: st)).
           assumption. assumption.
    + induction st.
      * simpl. intros. inversion H.
      * induction st.
        -- simpl. intros. inversion H.
        -- clear IHst0. simpl. intros.
           apply (IHse1 (a0 * a :: st)).
           assumption. assumption.
Qed.

Search list.
(*
Lemma Dinamic_Execute (se1 se2 : stack_exp) (st1 st2 : stack) :
  forall (st : stack),
    execute st se1 = Some st1 -> 
    execute st1 se2 = Some st2 -> 
    execute st (se1 ++ se2) = Some st2.
*)
Lemma Atomic_Union (se1 se2 : stack_exp) (st1 st2 : stack) :
    execute nil se1 = Some st1 ->
    execute nil se2 = Some st2 ->
    execute nil (se1 ++ se2) = Some (st2 ++ st1).
Proof.
  intros.
  apply (Dinamic_Execute se1 se2 st1 (st2 ++ st1) nil).
  - assumption.
  - induction se2.
    + inversion H0. simpl. reflexivity.
    + induction a.
      * induction st2.
        -- rewrite <- (app_nil_end st2). assumption.
        -- 
  (*
  intros.
  apply (Dinamic_Execute se1 se2 st1 (st2 ++ st1) nil).
  - assumption.
  - induction se2.
    + inversion H0. simpl. reflexivity.
    + induction se1.
      * inversion H.
        rewrite <- (app_nil_end st2).
        assumption.
      * induction st1.
        -- rewrite <- (app_nil_end st2).
           assumption.
        --  
           *)
Qed.

Theorem Correction : forall (a : aexp),
                     (execute nil (compile a) = Some (cons (aeval a) nil)) .
Proof.
  intros.
  induction a.
  - simpl. reflexivity.
  - induction o.
    + simpl execute.
Qed.

(*
Theorem Correction : forall (a : aexp), exists (z1 z2 : option stack) , z1 = execute nil (compile a) -> z2 = Some (cons (aeval a) nil) -> z1 = z2.
Proof.
induction a.
- simpl.
  exists (Some (z :: nil)).
  exists (Some (z :: nil)).
  intros.
  reflexivity.
- induction o.
  + exists (execute nil (compile (a1; + ; a2))).
    exists (execute nil (compile (a1; + ; a2))).
    intros.
    reflexivity.
  + exists (execute nil (compile (a1; - ; a2))).
    exists (execute nil (compile (a1; - ; a2))).
    intros.
    reflexivity.
  + exists (execute nil (compile (a1; * ; a2))).
    exists (execute nil (compile (a1; * ; a2))).
    intros.
    reflexivity.
Qed.
*)
