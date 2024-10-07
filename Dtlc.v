Require Import List.
Require Import Nat.
Import ListNotations.

(* Syntax *)
Inductive term : Type :=
  | Var : nat -> term
  | Star : term
  | Pi : term -> term -> term
  | Fun : term -> term -> term
  | App : term -> term -> term
  | Nat : term
  | Zero : term
  | Succ : term -> term
  | ElimNat : term -> term -> term -> term -> term.

(* Term Equality *)
Fixpoint term_beq (t1 t2 : term) : bool :=
  match t1, t2 with
  | Var n1, Var n2 => n1 =? n2
  | Star, Star => true
  | Pi ty1 t1, Pi ty2 t2 => term_beq ty1 ty2 && term_beq t1 t2
  | Fun ty1 t1, Fun ty2 t2 => term_beq ty1 ty2 && term_beq t1 t2
  | App t11 t12, App t21 t22 => term_beq t11 t21 && term_beq t12 t22
  | Nat, Nat => true
  | Zero, Zero => true
  | Succ t1, Succ t2 => term_beq t1 t2
  | ElimNat t1 t2 t3 t4, ElimNat t5 t6 t7 t8 =>
      term_beq t1 t5 && term_beq t2 t6 && term_beq t3 t7 && term_beq t4 t8
  | _, _ => false
  end.

(* De Bruijn Lifting *)
Fixpoint lift (n : nat) (k : nat) (t : term) : term :=
  match t with
  | Var x => if x <? k then Var x else Var (x + n)
  | Star => Star
  | Pi ty t' => Pi (lift n k ty) (lift n (S k) t')
  | Fun ty t' => Fun (lift n k ty) (lift n (S k) t')
  | App t1 t2 => App (lift n k t1) (lift n k t2)
  | Nat => Nat
  | Zero => Zero
  | Succ t' => Succ (lift n k t')
  | ElimNat t t0 tsuc t' => ElimNat (lift n k t) (lift n k t0) (lift n k tsuc) (lift n k t')
  end.

(* De Bruijn Substitution *)
Fixpoint subst (n : nat) (repl : term) (t : term) : term :=
  match t with
  | Var x => if x =? n then repl else if x <? n then Var x else Var (x - 1)
  | Star => Star
  | Pi ty t' => Pi (subst n repl ty) (subst (S n) (lift 1 0 repl) t')
  | Fun ty t' => Fun (subst n repl ty) (subst (S n) (lift 1 0 repl) t')
  | App t1 t2 => App (subst n repl t1) (subst n repl t2)
  | Nat => Nat
  | Zero => Zero
  | Succ t' => Succ (subst n repl t')
  | ElimNat t t0 tsuc t' => ElimNat (subst n repl t) (subst n repl t0) (subst n repl tsuc) (subst n repl t')
  end.

(* Evaluation *)
Fixpoint eval (t : term) : term :=
  match t with
  | Var n => Var n
  | Star => Star
  | Pi ty t' => Pi (eval ty) (eval t')
  | Fun ty t' => Fun (eval ty) (eval t')
  | App t1 t2 =>
      let t1' := eval t1 in
      let t2' := eval t2 in
      match t1' with
      | Fun _ t' => subst 0 t2' t'
      | _ => App t1' t2'
      end
  | Nat => Nat
  | Zero => Zero
  | Succ t' => Succ (eval t')
  | ElimNat t t0 tsuc t' =>
      let t'' := eval t' in
      match t'' with
      | Zero => eval t0
      | Succ n => App (App tsuc n) (ElimNat t t0 tsuc n)
      | _ => ElimNat (eval t) (eval t0) (eval tsuc) t''
      end
  end.

(* Typing Relation *)
Fixpoint get_type (ctx : list term) (t : term) : option term :=
  match t with
  | Var n => nth_error ctx n
  | Star => Some Star
  | Pi ty t' =>
      match get_type ctx ty, get_type (ty :: ctx) t' with
      | Some Star, Some Star => Some Star
      | _, _ => None
      end
  | Fun ty t' =>
      match get_type (ty :: ctx) t' with
      | Some ty2 =>
          match get_type ctx ty with
          | Some Star => Some (Pi ty ty2)
          | _ => None
          end
      | None => None
      end
  | App t1 t2 =>
      match get_type ctx t1, get_type ctx t2 with
      | Some (Pi ty t'), Some ty' =>
          if term_beq ty ty' then Some (subst 0 t2 t') else None
      | _, _ => None
      end
  | Nat => Some Star
  | Zero => Some Nat
  | Succ t' =>
      match get_type ctx t' with
      | Some Nat => Some Nat
      | _ => None
      end
  | ElimNat t t0 tsuc t' =>
      match get_type ctx t, get_type ctx t0, get_type ctx tsuc, get_type ctx t' with
      | Some (Fun Nat Star), Some (App t'' Zero), Some (Fun Nat (Fun t1 t2)), Some Nat =>
          if negb (term_beq t'' t) then None else
          match t1, t2 with
          | App t1' (Var n1), App t2' (Succ (Var n2)) =>
              if andb (term_beq t1' t2') (n1 =? n2) then Some (App t t') else None
          | _, _ => None
          end
      | _, _, _, _ => None
      end
  end.

Definition t1 := Fun Nat (App (App (Var 1) (Fun Nat (Var 3))) (Var 2)).

(* fun.((1 (fun.3)) 2)[1 <- 0] = fun.((1 (fun.2)) 1) *)
Example subst1 :
  subst 1 (Var 0) t1 = Fun Nat (App (App (Var 1) (Fun Nat (Var 2))) (Var 1)).

Proof. simpl. reflexivity. Qed.

Definition t2 := Fun Nat (Fun Nat (Var 1)).

(* ((fun.fun.1) succ succ zero) zero = succ succ zero *)
Example eval1 :
  eval (App (App t2 (Succ (Succ Zero))) Zero) = Succ (Succ Zero).

Proof. simpl. reflexivity. Qed.

Definition t3 := Fun Nat (App (Var 0) (Var 0)).

(* (fun.0 0) (fun.0 0) = (fun.0 0) (fun.0 0) *)
Example eval2 :
  eval (App t3 t3) = (App t3 t3).

Proof. simpl. reflexivity. Qed.

(* Polymorphic Identity Function *)
Definition t4 := Fun Star (Fun (Var 0) (Var 0)).

Example get_type1 :
  get_type [] t4 = Some (Pi Star (Pi (Var 0) (Var 0))).
  
Proof. simpl. reflexivity. Qed.
