Require Import List.
Require Import Nat.
Import ListNotations.

Notation varid := nat.

Inductive term : Type :=
  | Var : varid -> term
  | Star : term
  | Pi : varid -> term -> term -> term
  | Fun : varid -> term -> term -> term
  | App : term -> term -> term
  | Nat : term
  | Zero : term
  | Succ : term -> term
  | ElimNat : term -> term -> term -> term -> term.

Definition context := list term.

(* Context Lookup *)
Fixpoint lookup (x : varid) (ctx : context) : option term :=
  match x, ctx with
  | O, hd :: _ => Some hd
  | S x', _ :: tl => lookup x' tl
  | _, _ => None
  end.

Fixpoint inb (x : varid) (l : list varid) : bool :=
  match l with
  | [] => false
  | hd :: tl => if hd =? x then true else inb x tl
  end.

Fixpoint union (l1 l2 : list varid) : list varid :=
  match l1 with
  | [] => l2
  | hd :: tl => if inb hd l2 then union tl l2 else hd :: union tl l2
  end.

Fixpoint diff (l1 l2 : list varid) : list varid :=
  match l1 with
  | [] => []
  | hd :: tl => if inb hd l2 then diff tl l2 else hd :: diff tl l2
  end.

(* Free Variables *)
Fixpoint fv (t : term) : list varid :=
  match t with
  | Var x => [x]
  | Star => []
  | Pi x ty1 ty2 => union (fv ty1) (diff (fv ty2) [x])
  | Fun x ty t' => union (fv ty) (diff (fv t') [x])
  | App t1 t2 => union (fv t1) (fv t2)
  | Nat => []
  | Zero => []
  | Succ t' => fv t'
  | ElimNat t t0 tsuc t' => union (union (union (fv t) (fv t0)) (fv tsuc)) (fv t')
  end.

(* Capture-Avoiding Substitution *)
Fixpoint subst (x : varid) (repl : term) (t : term) : term :=
  if negb (inb x (fv t)) then t else
  match t with
  | Var y => if x =? y then repl else t
  | Star => Star
  | Pi y ty1 ty2 => if inb y (union [x] (fv repl)) then t else
    Pi y (subst x repl ty1) (subst x repl ty2)
  | Fun y ty t' => if inb y (union [x] (fv repl)) then t else
    Fun y (subst x repl ty) (subst x repl t')
  | App t1 t2 => App (subst x repl t1) (subst x repl t2)
  | Nat => Nat
  | Zero => Zero
  | Succ t' => Succ (subst x repl t')
  | ElimNat t t0 tsuc t' => ElimNat (subst x repl t) (subst x repl t0) (subst x repl tsuc) (subst x repl t')
  end.
