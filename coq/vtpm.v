Inductive vtpmDynamicType (dom_ID:Set) (KEY:Set) (HASH:Set) : Set :=
| vtpmDynamic : dom_ID -> dom_ID -> KEY -> HASH -> HASH -> vtpmDynamicType dom_ID KEY HASH.

Inductive vtpmStaticType (LTN:Set): Set :=
| vtpmStatic : LTN -> vtpmStaticType LTN.

Inductive vtpmEntryType (dom_ID:Set) (KEY:Set) (HASH:Set) (LTN:Set) : Set :=
| vtpmEntry : vtpmStaticType LTN -> vtpmDynamicType dom_ID KEY HASH -> vtpmEntryType dom_ID KEY HASH LTN.

Inductive Lift (T:Set) : Set :=
| up : T -> Lift T
| bottom : Lift T.

Inductive List (T:Set) : Set :=
| nil : List T
| cons : T -> List T -> List T.

Fixpoint findLTN (l : List (vtpmEntryType nat nat nat nat)) : (Lift (vtpmEntryType nat nat nat nat))
  match l with
      | nil => bottom
      | cons v l' => (up v)
  end.

