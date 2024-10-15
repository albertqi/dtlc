Require Import List.
Require Import Nat.
Import ListNotations.

(******************************** DEFINITIONS ********************************)

(*** Syntax ***)
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

(*** Term Equality ***)
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

(*** Convert Nat to Term ***)
Fixpoint nat_to_term (n : nat) : term :=
  match n with
  | O => Zero
  | S n' => Succ (nat_to_term n')
  end.

(*** Convert Term to Nat ***)
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

(*** De Bruijn Lifting ***)
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

(*** De Bruijn Substitution ***)
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

(*** Evaluation ***)
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

(*** Evaluation with Fuel ***)
Fixpoint eval_fuel (fuel : nat) (t : term) : term :=
  match fuel with
  | O => t
  | S fuel' => eval_fuel fuel' (eval t)
  end.

(*** Typing Relation ***)
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

(********************************** EXAMPLES **********************************)

(*** Substitution ***)

(* Fun.((1 (Fun.3)) 2)[1 <- 0] = Fun.((1 (Fun.2)) 1) *)
Example subst1 :
  subst 1 (Var 0) (Fun Nat (App (App (Var 1) (Fun Nat (Var 3))) (Var 2))) =
  Fun Nat (App (App (Var 1) (Fun Nat (Var 2))) (Var 1)).

Proof. simpl. reflexivity. Qed.

(*** Evaluation ***)

(* ((Fun.Fun.1) Succ Succ Zero) Zero = Succ Succ Zero *)
Example eval1 :
  eval (App (App (Fun Nat (Fun Nat (Var 1))) (Succ (Succ Zero))) Zero) = Succ (Succ Zero).

Proof. simpl. reflexivity. Qed.

(*** Omega Combinator ***)

Definition omega := App (Fun Nat (App (Var 0) (Var 0))) (Fun Nat (App (Var 0) (Var 0))).

(* (Fun.0 0) (Fun.0 0) = (Fun.0 0) (Fun.0 0) *)
Example omega1 :
  eval omega = omega.

Proof. simpl. reflexivity. Qed.

(*** Polymorphic Identity Function ***)

Definition id := Fun Star (Fun (Var 0) (Var 0)).

(* 100 = 100 *)
Example id1 :
  eval (App (App id Nat) (nat_to_term 100)) = nat_to_term 100.

Proof. simpl. reflexivity. Qed.

(* Fun.Succ 0 = Fun.Succ 0 *)
Example id2 :
  eval (App (App id (Pi Nat Nat)) (Fun Nat (Succ (Var 0)))) = Fun Nat (Succ (Var 0)).

Proof. simpl. reflexivity. Qed.

(* id : (A : Star) -> A -> A *)
Example id3 :
  get_type [] id = Some (Pi Star (Pi (Var 0) (Var 0))).
  
Proof. simpl. reflexivity. Qed.

(*** Plus Function ***)

Definition plus : term :=
  Fun Nat (Fun Nat (ElimNat (Fun Nat Nat) (Var 1) (Fun Nat (Fun Nat (Succ (Var 0)))) (Var 0))).

(* 3 + 0 = 3 *)
Example plus1 :
  eval_fuel 10 (App (App plus (nat_to_term 3)) Zero) = nat_to_term 3.

Proof. simpl. reflexivity. Qed.

(* 37 + 43 = 80 *)
Example plus2 :
  eval_fuel 100 (App (App plus (nat_to_term 37)) (nat_to_term 43)) = nat_to_term 80.

Proof. reflexivity. Qed.

(* plus : Nat -> Nat -> Nat *)
Example plus3 :
  get_type [] plus = Some (Pi Nat (Pi Nat Nat)).

Proof. simpl. reflexivity. Qed.

(*** Multiplication Function ***)

Definition mult : term :=
  Fun Nat (Fun Nat (ElimNat (Fun Nat Nat) Zero (Fun Nat (Fun Nat (App (App plus (Var 0)) (Var 3)))) (Var 0))).

(* 3 * 0 = 0 *)
Example mult1 :
  eval_fuel 10 (App (App mult (nat_to_term 3)) Zero) = Zero.

Proof. simpl. reflexivity. Qed.

(* 17 * 11 = 187 *)
Example mult2 :
  eval_fuel 200 (App (App mult (nat_to_term 17)) (nat_to_term 11)) = nat_to_term 187.

Proof. reflexivity. Qed.

(* mult : Nat -> Nat -> Nat *)
Example mult3 :
  get_type [] mult = Some (Pi Nat (Pi Nat Nat)).

Proof. simpl. reflexivity. Qed.

(*** Commutative Property ***)

(* 29 + 163 = 163 + 29 *)
Example comm1 :
  eval_fuel 200 (App (App plus (nat_to_term 29)) (nat_to_term 163)) =
  eval_fuel 200 (App (App plus (nat_to_term 163)) (nat_to_term 29)).

Proof. reflexivity. Qed.

(* 7 * 23 = 23 * 7 *)
Example comm2 :
  eval_fuel 200 (App (App mult (nat_to_term 7)) (nat_to_term 23)) =
  eval_fuel 200 (App (App mult (nat_to_term 23)) (nat_to_term 7)).

Proof. reflexivity. Qed.

(*** Associative Property ***)

(* (24 + 98) + 47 = 24 + (98 + 47) *)
Example assoc1 :
  eval_fuel 200 (App (App plus (App (App plus (nat_to_term 24)) (nat_to_term 98))) (nat_to_term 47)) =
  eval_fuel 200 (App (App plus (nat_to_term 24)) (App (App plus (nat_to_term 98)) (nat_to_term 47))).

Proof. reflexivity. Qed.

(* (4 * 5) * 6 = 4 * (5 * 6) *)
Example assoc2 :
  eval_fuel 200 (App (App mult (App (App mult (nat_to_term 4)) (nat_to_term 5))) (nat_to_term 6)) =
  eval_fuel 200 (App (App mult (nat_to_term 4)) (App (App mult (nat_to_term 5)) (nat_to_term 6))).

Proof. reflexivity. Qed.

(*** Power Function ***)

Definition pow : term :=
  Fun Nat (Fun Nat (ElimNat (Fun Nat Nat) (Succ Zero) (Fun Nat (Fun Nat (App (App mult (Var 3)) (Var 0)))) (Var 0))).

(* 5 ^ 0 = 1 *)
Example pow1 :
  eval_fuel 10 (App (App pow (nat_to_term 5)) Zero) = Succ Zero.

Proof. simpl. reflexivity. Qed.

(* 0 ^ 5 = 0 *)
Example pow2 :
  eval_fuel 10 (App (App pow Zero) (nat_to_term 5)) = Zero.

Proof. simpl. reflexivity. Qed.

(* 0 ^ 0 = 1 *)
Example pow3 :
  eval_fuel 10 (App (App pow Zero) Zero) = Succ Zero.

Proof. simpl. reflexivity. Qed.

(* 5 ^ 2 = 25 *)
Example pow4 :
  eval_fuel 100 (App (App pow (nat_to_term 5)) (nat_to_term 2)) = nat_to_term 25.

Proof. reflexivity. Qed.

(* 2 ^ 5 = 32 *)
Example pow5 :
  eval_fuel 100 (App (App pow (nat_to_term 2)) (nat_to_term 5)) = nat_to_term 32.

Proof. reflexivity. Qed.

(* (2 ^ 3) * (2 ^ 4) = 2 ^ (3 + 4) *)
Example pow6 :
  eval_fuel 200 (App (App mult (App (App pow (nat_to_term 2)) (nat_to_term 3))) (App (App pow (nat_to_term 2)) (nat_to_term 4))) =
  eval_fuel 200 (App (App pow (nat_to_term 2)) (App (App plus (nat_to_term 3)) (nat_to_term 4))).

Proof. reflexivity. Qed.

(* (2 ^ 3) ^ 2 = 2 ^ (3 * 2) *)
Example pow7 :
  eval_fuel 200 (App (App pow (App (App pow (nat_to_term 2)) (nat_to_term 3))) (nat_to_term 2)) =
  eval_fuel 200 (App (App pow (nat_to_term 2)) (App (App mult (nat_to_term 3)) (nat_to_term 2))).

Proof. reflexivity. Qed.

(* (3 * 4) ^ 2 = (3 ^ 2) * (4 ^ 2) *)
Example pow8 :
  eval_fuel 200 (App (App pow (App (App mult (nat_to_term 3)) (nat_to_term 4))) (nat_to_term 2)) =
  eval_fuel 200 (App (App mult (App (App pow (nat_to_term 3)) (nat_to_term 2))) (App (App pow (nat_to_term 4)) (nat_to_term 2))).

Proof. reflexivity. Qed.

(* pow : Nat -> Nat -> Nat *)
Example pow9 :
  get_type [] pow = Some (Pi Nat (Pi Nat Nat)).

Proof. simpl. reflexivity. Qed.

(*** Factorial Function ***)

Definition fact : term :=
  Fun Nat (ElimNat (Fun Nat Nat) (Succ Zero) (Fun Nat (Fun Nat (App (App mult (Succ (Var 1))) (Var 0)))) (Var 0)).

(* 0! = 1 *)
Example fact1 :
  eval_fuel 10 (App fact Zero) = Succ Zero.

Proof. simpl. reflexivity. Qed.

(* 5! = 120 *)
Example fact2 :
  eval_fuel 200 (App fact (nat_to_term 5)) = nat_to_term 120.

Proof. reflexivity. Qed.

(* fact : Nat -> Nat *)
Example fact3 :
  get_type [] fact = Some (Pi Nat Nat).

Proof. simpl. reflexivity. Qed.
