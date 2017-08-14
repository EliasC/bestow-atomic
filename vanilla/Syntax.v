Require Import List.
Import ListNotations.

Require Export Map.
Require Export Shared.

Definition var := nat.
Definition id := nat.
Definition loc := nat.

(*
======
Types
======
*)

Inductive ty : Type :=
  | TAct : ty
  | TBes : ty
  | TPas : ty
  | TArr : ty -> ty -> ty
  | TUnit: ty
.

Function is_active (t : ty) : bool :=
  match t with
    | TAct => true
    | TBes => true
    | _ => false
  end.

(*
============
Expressions
============
*)

Inductive expr : Type :=
  | EVar : var -> expr
  | EApp : expr -> expr -> expr
  | ESend : expr -> var -> ty -> expr -> expr
  | EMut : expr -> expr
  | ENew : ty -> expr
  | EBes : expr -> expr
  | ELam : var -> ty -> expr -> expr
  | EUnit : expr
  | EId : id -> expr
  | ELoc : loc -> expr
  | EBId : loc -> id -> expr
.

Tactic Notation "expr_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "EVar"
  | Case_aux c "EApp"
  | Case_aux c "ESend"
  | Case_aux c "EMut"
  | Case_aux c "ENew"
  | Case_aux c "EBes"
  | Case_aux c "ELam"
  | Case_aux c "EUnit"
  | Case_aux c "EId"
  | Case_aux c "ELoc"
  | Case_aux c "EBId"
].

Inductive is_val : expr -> Prop :=
  | LamIsVal : forall x t e, is_val (ELam x t e)
  | UnitIsVal : is_val EUnit
  | IdIsVal : forall id, is_val (EId id)
  | LocIsVal : forall l, is_val (ELoc l)
  | BIdIsVal : forall l id, is_val (EBId l id)
.

Definition econtext := expr -> expr.

Definition ctx_appl (e' : _) : econtext := (fun e => EApp e e').
Hint Unfold ctx_appl.
Definition ctx_appr (v : _) : econtext := (fun e => EApp v e).
Hint Unfold ctx_appr.
Definition ctx_send (x : _) (ty : _) (e' : _): econtext := (fun e => ESend e x ty e').
Hint Unfold ctx_send.
Definition ctx_mut : econtext := (fun e => EMut e).
Hint Unfold ctx_mut.
Definition ctx_bes : econtext := (fun e => EBes e).
Hint Unfold ctx_bes.

Inductive is_econtext : econtext -> Prop :=
  | EC_AppL :
      forall e',
        is_econtext (ctx_appl e')
  | EC_AppR :
      forall v,
        is_val v ->
        is_econtext (ctx_appr v)
  | EC_Send :
      forall x t e,
        is_econtext (ctx_send x t e)
  | EC_Mut :
        is_econtext ctx_mut
  | EC_Bes :
        is_econtext ctx_bes
.

Fixpoint freeVars (e : expr) : list var :=
  match e with
    | EVar x => [x]
    | EApp e1 e2 => freeVars e1 ++ freeVars e2
    | ESend e1 x _ e2 => freeVars e1 ++ List.remove id_eq_dec x (freeVars e2)
    | EMut e' => freeVars e'
    | EBes e' => freeVars e'
    | ELam x _ e' => List.remove id_eq_dec x (freeVars e')
    | _ => []
  end.

Fixpoint freeLocs (e : expr) : list loc :=
  match e with
    | ELoc l => [l]
    | EApp e1 e2 => freeLocs e1 ++ freeLocs e2
    | ESend e1 x _ e2 => freeLocs e1 ++ freeLocs e2
    | EMut e' => freeLocs e'
    | EBes e' => freeLocs e'
    | ELam x _ e' => freeLocs e'
    | _ => []
  end.

Fixpoint freeIds (e : expr) : list id :=
  match e with
    | EId id => [id]
    | EApp e1 e2 => freeIds e1 ++ freeIds e2
    | ESend e1 x _ e2 => freeIds e1 ++ freeIds e2
    | EMut e' => freeIds e'
    | EBes e' => freeIds e'
    | ELam x _ e' => freeIds e'
    | _ => []
  end.

Fixpoint freeBIds (e : expr) : list (loc * id) :=
  match e with
    | EBId l id => [(l, id)]
    | EApp e1 e2 => freeBIds e1 ++ freeBIds e2
    | ESend e1 x _ e2 => freeBIds e1 ++ freeBIds e2
    | EMut e' => freeBIds e'
    | EBes e' => freeBIds e'
    | ELam x _ e' => freeBIds e'
    | _ => []
  end.

Fixpoint subst (x : var) (v : expr) (e : expr) : expr :=
  match e with
    | EVar y => if id_eq_dec x y then v else e
    | EApp e1 e2 => EApp (subst x v e1) (subst x v e2)
    | ESend e1 y t e2 =>
      ESend (subst x v e1) y t
            (if id_eq_dec x y
             then e2
             else subst x v e2)
    | EMut e' => EMut (subst x v e')
    | EBes e' => EBes (subst x v e')
    | ELam y t e' =>
      ELam y t
           (if id_eq_dec x y then
              e'
            else
              (subst x v e'))
    | _ => e
  end.

(*
==============
Configuration
==============
*)

Inductive is_msg : expr -> Prop :=
  | LamIsMsg : forall x t e, is_msg (ELam x t e)
.

Definition actor := (loc * list loc * list expr * expr)%type.

Definition heap := list actor.

Definition heapExtend (H : heap) (a : actor) := snoc H a.

Definition heapLookup (H : heap) (id : id) :=
  nth_error H id.

Fixpoint heapUpdate (H : heap) (id : id) (a : actor) :=
  match H with
  | nil => nil
  | a' :: H' =>
    match id with
    | O    => a :: H'
    | S id' => a' :: (heapUpdate H' id' a)
    end
  end.

Definition LH (H : heap) (id : id) :=
  match heapLookup H id with
    | Some (_, L, _, _) => Some L
    | None => None
  end.

(*
--------------
Configuration
--------------
*)

Inductive actor_idle : actor -> Prop :=
  | ActorIdle : forall l L v, is_val v -> actor_idle (l, L, [], v)
.

Definition heap_done := Forall actor_idle.

Definition configuration := (heap * nat)%type.

Definition actor_done (cfg : configuration) (id : id) : Prop :=
  match cfg with
    | (h, _) => match heapLookup h id with
                  | Some a => actor_idle a
                  | None => False
                end
  end
.

Definition cfg_done (cfg : configuration) : Prop :=
  match cfg with
    | (h, _) => heap_done h
  end
.