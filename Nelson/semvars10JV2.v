Require Import ZArith. 
Require Import List.
Require Import Classical_Prop.
Open Scope Z_scope.

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

(****Expressoes sem Variaveis****)

(*1*)

Inductive Op : Type :=
  | P   : Op
  | M   : Op
  | MM  : Op.

Check forAll.
Require Import String. Open Scope string.
Instance showOp : Show (Op) :=
  {| show o := 
      match o with
      | P => "+"
      | M => "-"
      | MM => "*"
      end
  |}.

Definition genOp : G Op :=
  elems [P ; M ; MM].

Inductive aexp :=
  | Leaf : Z -> aexp
  | Node : aexp -> Op -> aexp -> aexp.

Instance showAExp : Show (aexp) :=
  {| show := 
      let fix aux a := 
        match a with
        | Leaf z => show z
        | Node l o r => "(" ++ aux l ++ " " ++ show o ++ " " ++ aux r ++ ")"
        end
      in aux 
  |}.

Fixpoint genAExp (sz : nat) (gz : G Z) (go : G Op) :=
  match sz with
  | 0%nat => liftGen Leaf gz
  | S sz' => freq [ (1%nat, liftGen Leaf gz)
                  ; (sz, liftGen3 Node (genAExp sz' gz go) go (genAExp sz' gz go))
                  ]
  end.

(*

Sample (genAExp 3 (choose(0,10)) genOp).

*)

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
Notation "« x »" := (Leaf x).
End TreeNotations.

Import TreeNotations.

Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
End ListNotations.

Import ListNotations.

(*3*)

Eval compute in (2*3)+(3*(4-2)).

Eval compute in aeval ((«2»;*;«3»);+;(«3»;*;(«4»;-;«2»))).

Eval compute in (20-40)*(30+(1*1)).

Eval compute in aeval ((«20»;-;«40»);*;(«30»;+;(«1»;*;«1»))).

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


Fixpoint stack_eq (st1 st2 : stack) : bool :=
  match st1, st2 with
  | nil, nil => true
  | cons z1 st1', cons z2 st2' => Zeq_bool z1 z2 && stack_eq st1' st2'
  | _, _ => false
  end.

Definition option_stack_eq (o1 o2 : option stack) : bool :=
  match o1, o2 with
  | None, None => true
  | Some st1, Some st2 => stack_eq st1 st2
  | _, _ => false
  end.

(*2*)

Let stack_machine : stack := nil. 

Let expression    : stack_exp  := [Num 2; Num 3; Mul; Num 3; Num 4; Num 2; Min; Mul; Pls].

Eval compute in execute stack_machine expression.

(*3*)
(*
    Decidimos usar o option para saber se houve problema.
    *)

(****Compilador****)
Open Scope list.
Fixpoint compile (a : aexp) : stack_exp := 
  match a with
  | Leaf z => cons (Num z) nil
  | Node l P r => compile l ++ compile r ++ cons Pls nil
  | Node l M r => compile l ++ compile r ++ cons Min nil
  | Node l MM r => compile l ++ compile r ++ cons Mul nil
  end.


Definition Correction' (a : aexp) :=
  option_stack_eq (execute nil (compile a)) (Some (cons (aeval a) nil)).

(*

Check forAll.
Sample (genAExp 3 (choose(0,10)) genOp).

QuickChick (forAll (genAExp 3 (choose(0,10)) genOp) Correction').

*)


(*2*)

Eval compute in execute nil (compile ((«2»;*;«3»);+;(«3»;*;(«4»;-;«2»)))).

(*3*)

Lemma Dinamic_Execute (z : Z) (se1 se2 : stack_exp):
  forall (st st1 : stack),
    execute st se1 = Some (z :: nil) -> 
    execute (st ++ st1) (se1 ++ se2) = execute (z :: st1) se2.
Proof.
  induction se1.
  - simpl.
    intros.
    inversion H.
    simpl.
    reflexivity.
  - induction a.
    + simpl.
      intros.
      apply (IHse1 (z0 :: st) st1).
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

Theorem Correction : forall (a : aexp),
                     (execute nil (compile a) = Some (cons (aeval a) nil)).
Proof.
  intros.
  induction a.
  - simpl. reflexivity.
  - induction o.
    + simpl. 
      assert (H := ((Dinamic_Execute (aeval a1) (compile a1) (compile a2 ++ Pls :: nil) nil nil) IHa1)).
      assert (H1 := ((Dinamic_Execute (aeval a2) (compile a2) (Pls :: nil) nil (aeval a1 :: nil)) IHa2)).
      rewrite <- (app_nil_end nil) in H.
      simpl in H1.
      rewrite H.
      rewrite H1.
      simpl.
      reflexivity.
    + simpl. 
      assert (H := ((Dinamic_Execute (aeval a1) (compile a1) (compile a2 ++ Min :: nil) nil nil) IHa1)).
      assert (H1 := ((Dinamic_Execute (aeval a2) (compile a2) (Min :: nil) nil (aeval a1 :: nil)) IHa2)).
      rewrite <- (app_nil_end nil) in H.
      simpl in H1;rewrite H;rewrite H1;simpl; reflexivity.
    + simpl. 
      assert (H := ((Dinamic_Execute (aeval a1) (compile a1) (compile a2 ++ Mul :: nil) nil nil) IHa1)).
      assert (H1 := ((Dinamic_Execute (aeval a2) (compile a2) (Mul :: nil) nil (aeval a1 :: nil)) IHa2)).
      rewrite <- (app_nil_end nil) in H.
      simpl in H1;rewrite H;rewrite H1;simpl; reflexivity.
Qed.
