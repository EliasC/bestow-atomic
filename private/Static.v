Require Export Syntax.
Require Export Map.

Definition env := partial_map var ty.

Definition activeEnv (Gamma : env) : env :=
  fun x =>
    match Gamma x with
      | Some t => if is_active t then Some t else None
      | None => None
    end.

Reserved Notation " Gamma '|-' expr '\in' ty " (at level 40).

Inductive hasType (Gamma : env) : expr -> ty -> Prop :=
  | T_Var :
      forall x t
        (Hlookup : Gamma x = Some t),
        Gamma |- EVar x \in t
  | T_Unit :
        Gamma |- EUnit \in TUnit
  | T_Loc :
      forall l,
        Gamma |- ELoc l \in TPas
  | T_Id :
      forall id,
        Gamma |- EId id \in TAct
  | T_Bestowed :
      forall l id,
        Gamma |- EBId l id \in TBes
  | T_AtStart :
      forall e a,
        Gamma |- e \in a ->
        forall (Hactive : is_active a = true),
        Gamma |- EAtStart e \in TUnit
  | T_AtEnd :
      forall e a,
        Gamma |- e \in a ->
        forall (Hactive : is_active a = true),
        Gamma |- EAtEnd e \in TUnit
  | T_NewPassive :
        Gamma |- ENew TPas \in TPas
  | T_NewActive :
        Gamma |- ENew TAct \in TAct
  | T_Mutate :
      forall e,
        Gamma |- e \in TPas ->
        Gamma |- EMut e \in TUnit
  | T_Bestow :
      forall e,
        Gamma |- e \in TPas ->
        Gamma |- EBes e \in TBes
  | T_Lam :
      forall x t1 e t2
        (bodyHasType : extend Gamma x t1 |- e \in t2),
        Gamma |- ELam x t1 e \in TArr t1 t2
  | T_Apply :
      forall e1 e2 t1 t2,
        Gamma |- e1 \in TArr t1 t2 ->
        Gamma |- e2 \in t1 ->
        Gamma |- EApp e1 e2 \in t2
  | T_Send :
      forall x e e' a t,
        Gamma |- e \in a ->
        forall (Hactive : is_active a = true),
        extend (activeEnv Gamma) x TPas |- e' \in t ->
        freeLocs e' = nil ->
        Gamma |- ESend e x TPas e' \in TUnit
  where " Gamma '|-' expr '\in' ty " := (hasType Gamma expr ty).

Tactic Notation "hasType_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var"
  | Case_aux c "T_Unit"
  | Case_aux c "T_Loc"
  | Case_aux c "T_Id"
  | Case_aux c "T_Bestowed"
  | Case_aux c "T_AtStart"
  | Case_aux c "T_AtEnd"
  | Case_aux c "T_NewPassive"
  | Case_aux c "T_NewActive"
  | Case_aux c "T_Mutate"
  | Case_aux c "T_Bestow"
  | Case_aux c "T_Lam"
  | Case_aux c "T_Apply"
  | Case_aux c "T_Send"
  ]
.
