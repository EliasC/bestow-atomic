Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import List.

Require Export Syntax.

Reserved Notation " id '/' cfg ';' e '==>' cfg' ';' e' " (at level 40).

Inductive step_actor (id : id) : configuration -> expr -> configuration -> expr -> Prop :=
  | EvalContext :
      forall O O' H H' n n' ctx e e',
        is_econtext ctx ->
        id / (O, H, n) ; e ==>
          (O', H', n') ; e' ->
        id / (O, H, n) ; ctx e ==>
          (O', H', n') ; ctx e'
  | EvalMutate :
      forall O H n l,
        id / (O, H, n) ; EMut (ELoc l) ==>
           (O, H, n) ; EUnit
  | EvalApply :
      forall O H n x t e v,
        is_val v ->
        id / (O, H, n) ; EApp (ELam x t e) v ==>
           (O, H, n) ; subst x v e
  | EvalNewPassive :
      forall O H n l L Q e,
        heapLookup H id = Some (l, L, Q, e) ->
        id / (O, H, n) ; ENew TPas ==>
           (O, heapUpdate H id (l, n :: L, Q, e), S n) ; ELoc n
  | EvalNewActive :
      forall O H n,
        id / (O, H, n) ; ENew TAct ==>
           (O, heapExtend H (n, n :: nil, nil, EUnit), S n) ; EId (length H)
  | EvalNewTrans :
      forall O H n l L Q e,
        heapLookup H id = Some (l, L, Q, e) ->
        id / (O, H, n) ; ENew TTrans ==>
           (extend O n id, heapUpdate H id (l, n :: L, Q, e), S n) ; ETId n
  | EvalSendActor :
      forall O H n id' x e l' L Q e',
        heapLookup H id' = Some (l', L, Q, e') ->
        id / (O, H, n) ; ESend (EId id') x TPas e ==>
           (O, heapUpdate H id' (l', L, snoc Q (ELam x TPas e), e'), n) ; EUnit
  | EvalSendTransDelegate :
      forall O H n l id' x e l' L Q e',
        O l = Some id' ->
        id <> id' ->
        heapLookup H id' = Some (l', L, Q, e') ->
        id / (O, H, n) ; ESend (ETId l) x TPas e ==>
           (O, heapUpdate H id' (l', L, snoc Q (ELam 0 TPas (ESend (ETId l) x TPas e)), e'), n) ; EUnit
  | EvalSendTransRun :
      forall O H n l x e,
        O l = Some id ->
        id / (O, H, n) ; ESend (ETId l) x TPas e ==>
           (O, H, n) ; EApp (ELam x TPas e) (ELoc l)
where " id '/' cfg ';' e '==>' cfg' ';' e' " := (step_actor id cfg e cfg' e').

Inductive step (id : id) : configuration -> configuration -> Prop :=
  | EvalActorMsg :
      forall O H n l L v' Q v,
        heapLookup H id = Some (l, L, v'::Q, v) ->
        is_val v ->
        step id (O, H, n) (O, heapUpdate H id (l, L, Q, EApp v' (ELoc l)), n)
  | EvalActorTransfer :
      forall id' O H n l l1 l2 L L' Q Q' v e,
        heapLookup H id = Some (l1, L, Q, v) ->
        is_val v ->
        O l = Some id ->
        id <> id' ->
        heapLookup H id' = Some (l2, L', Q', e) ->
        step id (O, H, n) (extend O l id', heapUpdate (heapUpdate H id (l1, remove id_eq_dec l L, Q, EUnit)) id' (l2, l :: L', Q', e), n)
  | EvalActorRun :
      (* e will always be equal to e'' *)
      forall O O' H H' n n' l L L' Q Q' e e' e'',
        heapLookup H id = Some (l, L, Q, e) ->
        id / (O, H, n) ; e ==> (O', H', n') ; e' ->
        heapLookup H' id = Some (l, L', Q', e'') ->
        step id (O, H, n) (O', heapUpdate H' id (l, L', Q', e'), n')
.