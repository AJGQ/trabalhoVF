Require Import ZArith. 
Require Import List.
Open Scope Z_scope.
Print nat.
Print Z.
Search Z.


Inductive Obj : Type :=
  | Num    : Z -> Obj
  | Pls    : Obj
  | Min    : Obj
  | Mul    : Obj.

Print list.
Print option.

Let aexp := list Obj.
Let stack:= list Z.

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

Print option.

(* in the future use states*)
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

Search option.
Eval compute in 10 = 10+2.

Fixpoint aevalR (a : aexp) (n : option Z) : Prop :=
  (execute nil a) = n.


Lemma RelEqFun : forall (a : aexp) (n : option Z),
                    (aevalR a n) <-> (aeval a = n).
Proof.
  intros.
  red.
  split.
    - intro.
   
Qed.

