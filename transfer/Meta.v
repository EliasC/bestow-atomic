(*
====
Map
====
*)

Class ID (A : Type) :=
{
  id_eq_dec : forall (x y : A), {x = y} + {x <> y}
}.

Definition partial_map (from:Type) {eqd : ID from} (to:Type) := from -> option to.

Definition empty {A B:Type} {eqd : ID A} : partial_map A B := (fun _ => None).

Definition extend {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) (b:B) :=
  fun a' => if id_eq_dec a a' then
              Some b
            else
              Gamma a'.

Hint Unfold extend.

Definition drop {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) :=
  fun a' => if id_eq_dec a a' then
              None
            else
              Gamma a'.

Hint Unfold drop.

Definition fresh {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) := Gamma a = None.

Hint Unfold fresh.
