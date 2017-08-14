Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import List.

Require Export Syntax.

Reserved Notation " id '/' cfg ';' e '==>' cfg' ';' e' " (at level 40).

Inductive step_actor (id : id) : configuration -> expr -> configuration -> expr -> Prop :=
  | EvalContext :
      forall M M' H H' n n' ctx e e',
        is_econtext ctx ->
        id / (M, H, n) ; e ==>
          (M', H', n') ; e' ->
        id / (M, H, n) ; ctx e ==>
          (M', H', n') ; ctx e'
  | EvalMutate :
      forall M H n l,
        id / (M, H, n) ; EMut (ELoc l) ==>
           (M, H, n) ; EUnit
  | EvalBestow :
      forall M H n l,
        id / (M, H, n) ; EBes (ELoc l) ==>
           (M, H, n) ; EBId l id
  | EvalApply :
      forall M H n x t e v,
        is_val v ->
        id / (M, H, n) ; EApp (ELam x t e) v ==>
           (M, H, n) ; subst x v e
  | EvalNewPassive :
      forall M H n l C L Q e,
        heapLookup H id = Some (l, L, C, Q, e) ->
        id / (M, H, n) ; ENew TPas ==>
           (M, heapUpdate H id (l, n :: L, C, Q, e), S n) ; ELoc n
  | EvalNewActive :
      forall M H n,
        id / (M, H, n) ; ENew TAct ==>
           (M, heapExtend H (n, n :: nil, empty, nil, EUnit), S n) ; EId (length H)
  | EvalAtomicStartActor :
      forall M H H' n l l' L L' C C' Q Q' e e' id',
        heapLookup H id = Some (l, L, C, Q, e) ->
        C id' = None ->
        H' = heapUpdate H id (l, L, extend C id' n, Q, e) ->
        heapLookup H' id' = Some (l', L', C', Q', e') ->
        id / (M, H, n) ; EAtStart (EId id') ==>
           (extend M n (nil, id'), heapUpdate H' id' (l', L', C', snoc Q' (Atomic n), e'), S n) ; EUnit
  | EvalAtomicStartBestowed :
      forall M H H' n l l' l'' L L' C C' Q Q' e e' id',
        heapLookup H id = Some (l, L, C, Q, e) ->
        C id' = None ->
        H' = heapUpdate H id (l, L, extend C id' n, Q, e) ->
        heapLookup H' id' = Some (l', L', C', Q', e') ->
        id / (M, H, n) ; EAtStart (EBId l'' id') ==>
           (extend M n (nil, id'), heapUpdate H' id' (l', L', C', snoc Q' (Atomic n), e'), S n) ; EUnit
  | EvalAtomicStartActorFail :
      forall M H n l L C Q e id' qid,
        heapLookup H id = Some (l, L, C, Q, e) ->
        C id' = Some qid ->
        id / (M, H, n) ; EAtStart (EId id') ==>
           (M, H, n) ; EUnit
  | EvalAtomicStartBestowedFail :
      forall M H n l l' L C Q e id' qid,
        heapLookup H id = Some (l, L, C, Q, e) ->
        C id' = Some qid ->
        id / (M, H, n) ; EAtStart (EBId l' id') ==>
           (M, H, n) ; EUnit
  | EvalAtomicEndActor :
      forall M H n l L C Q Q' e id' qid,
        heapLookup H id = Some (l, L, C, Q, e) ->
        C id' = Some qid ->
        M qid = Some (Q', id') ->
        id / (M, H, n) ; EAtEnd (EId id') ==>
           (extend M n (snoc Q' EndAtomic, id'), heapUpdate H id (l, L, drop C id', Q, e), S n) ; EUnit
  | EvalAtomicEndBestowed :
      forall M H n l l' L C Q Q' e id' qid,
        heapLookup H id = Some (l, L, C, Q, e) ->
        C id' = Some qid ->
        M qid = Some (Q', id') ->
        id / (M, H, n) ; EAtEnd (EBId l' id') ==>
           (extend M n (snoc Q' EndAtomic, id'), heapUpdate H id (l, L, drop C id', Q, e), S n) ; EUnit
  | EvalAtomicEndActorFail :
      forall M H n l L C Q e id',
        heapLookup H id = Some (l, L, C, Q, e) ->
        C id' = None ->
        id / (M, H, n) ; EAtEnd (EId id') ==>
           (M, H, n) ; EUnit
  | EvalAtomicEndBestowedFail :
      forall M H n l l' L C Q e id',
        heapLookup H id = Some (l, L, C, Q, e) ->
        C id' = None ->
        id / (M, H, n) ; EAtEnd (EBId l' id') ==>
           (M, H, n) ; EUnit
  | EvalSendActor :
      forall M H n id' x body e' l' L' C C' Q',
        conv H id = Some C ->
        C id' = None ->
        heapLookup H id' = Some (l', L', C', Q', e') ->
        id / (M, H, n) ; ESend (EId id') x TPas body ==>
           (M, heapUpdate H id' (l', L', C', snoc Q' (Msg (ELam x TPas body)), e'), n) ; EUnit
  | EvalSendBestowed :
      forall M H n l'' id' x body l' L' C C' Q' e',
        conv H id = Some C ->
        C id' = None ->
        heapLookup H id' = Some (l', L', C', Q', e') ->
        id / (M, H, n) ; ESend (EBId l'' id') x TPas body ==>
           (M, heapUpdate H id' (l', L', C', snoc Q' (Msg (ELam O TPas (EApp (ELam x TPas body) (ELoc l'')))), e'), n) ; EUnit
  | EvalSendActorAtomic :
      forall M H n id' x body qid C Q',
        conv H id = Some C ->
        C id' = Some qid ->
        M qid = Some (Q', id') ->
        id / (M, H, n) ; ESend (EId id') x TPas body ==>
           (extend M qid (snoc Q' (Msg (ELam x TPas body)), id'), H, n) ; EUnit
  | EvalSendBestowedAtomic :
      forall M H n l'' id' x body qid C Q',
        conv H id = Some C ->
        C id' = Some qid ->
        M qid = Some (Q', id') ->
        id / (M, H, n) ; ESend (EBId l'' id') x TPas body ==>
           (extend M qid (snoc Q' (Msg (ELam O TPas (EApp (ELam x TPas body) (ELoc l'')))), id'), H, n) ; EUnit
where " id '/' cfg ';' e '==>' cfg' ';' e' " := (step_actor id cfg e cfg' e').

Inductive step (id : id) : configuration -> configuration -> Prop :=
  | EvalActorMsg :
      forall M H n l L v' C Q v,
        heapLookup H id = Some (l, L, C, Msg v'::Q, v) ->
        is_val v ->
        step id (M, H, n) (M, heapUpdate H id (l, L, C, Q, EApp v' (ELoc l)), n)
  | EvalActorPrivateMsg :
      forall M H n l L C Q Q' v qid v',
        heapLookup H id = Some (l, L, C, Atomic qid::Q, v) ->
        is_val v ->
        M qid = Some (Msg v'::Q', id) ->
        step id (M, H, n) (extend M qid (Q', id), heapUpdate H id (l, L, C, Atomic qid::Q, EApp v' (ELoc l)), n)
  | EvalActorPrivateEnd :
      forall M H n l L C Q Q' v qid,
        heapLookup H id = Some (l, L, C, Atomic qid::Q, v) ->
        is_val v ->
        M qid = Some (EndAtomic::Q', id) ->
        step id (M, H, n) (drop M qid, heapUpdate H id (l, L, C, Q, v), n)
  | EvalActorRun :
      (* e will always be equal to e'' *)
      forall M M' H H' n n' l L L' C C' Q Q' e e' e'',
        heapLookup H id = Some (l, L, C, Q, e) ->
        id / (M, H, n) ; e ==> (M', H', n') ; e' ->
        heapLookup H' id = Some (l, L', C', Q', e'') ->
        step id (M, H, n) (M', heapUpdate H' id (l, L', C', Q', e'), n')
.