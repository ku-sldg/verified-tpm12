Require Import Bool Arith List.
Set Implicit Arguments.

Definition dom_ID := nat.
Definition KEY := nat.
Definition HASH := nat.
Definition LTN := nat.

Inductive vtpmDynamicType : Set :=
| vtpmDynamic : dom_ID -> dom_ID -> KEY -> HASH -> HASH -> vtpmDynamicType.

Eval simpl in (vtpmDynamic 1 2 3).

Inductive vtpmStaticType : Set :=
| vtpmStatic : LTN -> vtpmStaticType.

Eval simpl in (vtpmStatic 1).

Inductive vtpmEntryType : Set :=
| vtpmEntry : vtpmStaticType -> vtpmDynamicType -> vtpmEntryType.

Inductive lift (T:Set) : Set :=
| up : T -> lift T
| bottom : lift T.

Definition vtpmSet := list vtpmEntryType.

Fixpoint find (p:vtpmEntryType->bool) (l:vtpmSet) : (lift vtpmEntryType)  :=
  match l with
      | nil => bottom vtpmEntryType
      | cons v l' => if p v then (up v) else find p l'
  end.

Definition eqLTN : LTN -> vtpmEntryType -> Prop :=
  fun (l:LTN) (v:vtpmEntryType) =>
    match v with
    | vtpmEntry s _ =>
        match s with
        | vtpmStatic l' => (l=l')
        end
    end.

Eval simpl in eqLTN 1 (vtpmEntry (vtpmStatic 1) (vtpmDynamic 2 3 4 5 6)).

Definition findLTN : LTN -> vtpmSet -> lift vtpmEntryType :=
  fun (l:LTN) (s:vtpmSet) =>
    find (fun (v:vtpmEntryType) => eqLTN l v) s.