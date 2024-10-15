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

(* Convert Nat to Term *)
Fixpoint nat_to_term (n : nat) : term :=
  match n with
  | O => Zero
  | S n' => Succ (nat_to_term n')
  end.

(* Convert Term to Nat *)
Fixpoint term_to_nat (t : term) : option nat :=
  match t with
  | Zero => Some O
  | Succ t' =>
      match term_to_nat t' with
      | Some n => Some (S n)
      | None => None
      end
  | _ => None
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

(* Evaluation with Fuel *)
Fixpoint eval_fuel (fuel : nat) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel' => eval_fuel fuel' (eval t)
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
      let ty := eval (App t Zero) in
      match get_type ctx t, get_type ctx t0, get_type ctx tsuc, get_type ctx t' with
      | Some (Pi Nat Star), Some ty1, Some (Pi Nat (Pi ty2 ty3)), Some Nat =>
          if andb (andb (term_beq ty ty1) (term_beq ty ty2)) (term_beq ty ty3) then Some ty else None
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

(* Plus Function *)
Definition plus : term :=
  Fun Nat (Fun Nat (ElimNat (Fun Nat Nat) (Var 1) (Fun Nat (Fun Nat (Succ (Var 0)))) (Var 0))).

Example plus1 :
  eval_fuel 10 (App (App plus (nat_to_term 3)) Zero) = nat_to_term 3.

Proof. simpl. reflexivity. Qed.

Example plus2 :
  eval_fuel 100 (App (App plus (nat_to_term 37)) (nat_to_term 43)) = nat_to_term 80.

Proof. reflexivity. Qed.

Example plus3 :
  get_type [] plus = Some (Pi Nat (Pi Nat Nat)).

Proof. simpl. reflexivity. Qed.

(* Multiplication Function *)
Definition mult : term :=
  Fun Nat (Fun Nat (ElimNat (Fun Nat Nat) Zero (Fun Nat (Fun Nat (App (App plus (Var 0)) (Var 3)))) (Var 0))).

Example mult1 :
  eval_fuel 10 (App (App mult (nat_to_term 3)) Zero) = Zero.

Proof. simpl. reflexivity. Qed.

Example mult2 :
  eval_fuel 200 (App (App mult (nat_to_term 17)) (nat_to_term 11)) = nat_to_term 187.

Proof. reflexivity. Qed.

Example mult3 :
  get_type [] mult = Some (Pi Nat (Pi Nat Nat)).

Proof. simpl. reflexivity. Qed.

(* Commutative Property *)
Example comm1 :
  eval_fuel 200 (App (App plus (nat_to_term 29)) (nat_to_term 163)) = eval_fuel 200 (App (App plus (nat_to_term 163)) (nat_to_term 29)).

Proof. reflexivity. Qed.

Example comm2 :
  eval_fuel 200 (App (App mult (nat_to_term 7)) (nat_to_term 23)) = eval_fuel 200 (App (App mult (nat_to_term 23)) (nat_to_term 7)).

Proof. reflexivity. Qed.

(* Associative Property *)
Example assoc1 :
  eval_fuel 200 (App (App plus (App (App plus (nat_to_term 24)) (nat_to_term 98))) (nat_to_term 47)) =
  eval_fuel 200 (App (App plus (nat_to_term 24)) (App (App plus (nat_to_term 98)) (nat_to_term 47))).

Proof. reflexivity. Qed.

Example assoc2 :
  eval_fuel 200 (App (App mult (App (App mult (nat_to_term 4)) (nat_to_term 5))) (nat_to_term 6)) =
  eval_fuel 200 (App (App mult (nat_to_term 4)) (App (App mult (nat_to_term 5)) (nat_to_term 6))).

Proof. reflexivity. Qed.

(* Power Function *)
Definition pow : term :=
  Fun Nat (Fun Nat (ElimNat (Fun Nat Nat) (Succ Zero) (Fun Nat (Fun Nat (App (App mult (Var 3)) (Var 0)))) (Var 0))).

Example pow1 :
  eval_fuel 10 (App (App pow (nat_to_term 5)) Zero) = Succ Zero.

Proof. simpl. reflexivity. Qed.

Example pow2 :
  eval_fuel 10 (App (App pow Zero) (nat_to_term 5)) = Zero.

Proof. simpl. reflexivity. Qed.

Example pow3 :
  eval_fuel 10 (App (App pow Zero) Zero) = Succ Zero.

Proof. simpl. reflexivity. Qed.

Example pow4 :
  eval_fuel 100 (App (App pow (nat_to_term 5)) (nat_to_term 2)) = nat_to_term 25.

Proof. reflexivity. Qed.

Example pow5 :
  eval_fuel 100 (App (App pow (nat_to_term 2)) (nat_to_term 5)) = nat_to_term 32.

Proof. reflexivity. Qed.

(* Factorial Function *)
Definition fact : term :=
  Fun Nat (ElimNat (Fun Nat Nat) (Succ Zero) (Fun Nat (Fun Nat (App (App mult (Succ (Var 1))) (Var 0)))) (Var 0)).

Example fact1 :
  eval_fuel 10 (App fact Zero) = Succ Zero.

Proof. simpl. reflexivity. Qed.

Example fact2 :
  eval_fuel 200 (App fact (nat_to_term 5)) = nat_to_term 120.

Proof. reflexivity. Qed.
