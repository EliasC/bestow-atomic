Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import List.

Require Export Syntax.

Reserved Notation " id '/' cfg ';' e '==>' cfg' ';' e' " (at level 40).

Inductive step_actor (id : id) : configuration -> expr -> configuration -> expr -> Prop :=
  | EvalContext :
      forall H H' n n' ctx e e',
        is_econtext ctx ->
        id / (H, n) ; e ==>
          (H', n') ; e' ->
        id / (H, n) ; ctx e ==>
          (H', n') ; ctx e'
  | EvalMutate :
      forall H n l,
        id / (H, n) ; EMut (ELoc l) ==>
           (H, n) ; EUnit
  | EvalBestow :
      forall H n l,
        id / (H, n) ; EBes (ELoc l) ==>
           (H, n) ; EBId l id
  | EvalApply :
      forall H n x t e v,
        is_val v ->
        id / (H, n) ; EApp (ELam x t e) v ==>
           (H, n) ; subst x v e
  | EvalNewPassive :
      forall H n l L Q e,
        heapLookup H id = Some (l, L, Q, e) ->
        id / (H, n) ; ENew TPas ==>
           (heapUpdate H id (l, n :: L, Q, e), S n) ; ELoc n
  | EvalNewActive :
      forall H n,
        id / (H, n) ; ENew TAct ==>
           (heapExtend H (n, n :: nil, nil, EUnit), S n) ; EId (length H)
  | EvalSendActor :
      forall H n id' x e l' L Q e',
        heapLookup H id' = Some (l', L, Q, e') ->
        id / (H, n) ; ESend (EId id') x TPas e ==>
           (heapUpdate H id' (l', L, snoc Q (ELam x TPas e), e'), n) ; EUnit
  | EvalSendBestowed :
      forall H n l id' x e l' L Q e',
        heapLookup H id' = Some (l', L, Q, e') ->
        id / (H, n) ; ESend (EBId l id') x TPas e ==>
           (heapUpdate H id' (l', L, snoc Q (ELam O TPas (EApp (ELam x TPas e) (ELoc l))), e'), n) ; EUnit
where " id '/' cfg ';' e '==>' cfg' ';' e' " := (step_actor id cfg e cfg' e').

Inductive step (id : id) : configuration -> configuration -> Prop :=
  | EvalActorMsg :
      forall H n l L v' Q v,
        heapLookup H id = Some (l, L, v'::Q, v) ->
        is_val v ->
        step id (H, n) (heapUpdate H id (l, L, Q, EApp v' (ELoc l)), n)
  | EvalActorRun :
      (* e will always be equal to e'' *)
      forall H H' n n' l L L' Q Q' e e' e'',
        heapLookup H id = Some (l, L, Q, e) ->
        id / (H, n) ; e ==> (H', n') ; e' ->
        heapLookup H' id = Some (l, L', Q', e'') ->
        step id (H, n) (heapUpdate H' id (l, L', Q', e'), n')
.