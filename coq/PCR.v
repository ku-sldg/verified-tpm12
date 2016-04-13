(** ----
%%
%% PCR Theory
%%
%% Author: Perry Alexander
%% Date: Wed Apr  6 13:06:18 BST 2016
%%
%% Description: Basic model of a TPM register file
%% 
%% Dependencies:
%%  None
%%
%% Todo: (key - => pending, + => done)
%%
%% ----
 *)

Require Import Ensembles.
Require Import Omega.
Require Import List.
Require Import Eqdep_dec.
Require Import EqdepFacts.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

(** [LOCALITY] defines PCR access control.  [LOCALITY_SELECTION] is a set of
 locality values. *)

Definition LOCALITY : Type := {n:nat | n <= 4}.
Definition LOCALITY_SELECTION : Type := Ensemble LOCALITY.

(** [PCRINDEX] is 0-23 by default.  This can be changed if needed *)
Definition PCRINDEX : Type := {n:nat | n <= 23}.

(** Various kinds of hash values.  Might be a good place for an indexed type *)

Definition PCRVAL : Type := nat.

Definition TPM_COMPOSITE_HASH : Type := nat.

(** [PCR_SELECTION] defining what PCRs are needed for a composite. *)

Definition PCR_SELECTION : Type := PCRINDEX -> bool.

Inductive PCR : Type :=
| reset : PCR
| resetOne : PCR
| extend : PCR -> PCRVAL -> PCR.

Definition PCRVALUES : Type := PCRINDEX -> PCR.

Inductive PCRCOMPOSITE : Type :=
| pcrcomposite : PCR_SELECTION -> PCRVALUES -> PCRCOMPOSITE.

Inductive PCR_INFO : Type :=
| pcr_info : PCR_SELECTION -> TPM_COMPOSITE_HASH -> TPM_COMPOSITE_HASH -> PCR_INFO.

Inductive PCR_ATTRIBUTE : Type :=
| pcr_attribute : LOCALITY_SELECTION -> LOCALITY_SELECTION -> bool -> PCR_ATTRIBUTE.

Definition PCR_ATTRIBUTES : Type := PCRINDEX->PCR_ATTRIBUTE.

Print LOCALITY.

Definition lt4(x:nat) : Prop := x <= 3.

Lemma lt41 : 1 <= 3. omega. Qed.

Print exist.

Eval compute in exist lt4 1 lt41.

Check {n:nat | n <= 4}.

Print LOCALITY.

Eval compute in ((exist (fun x => x <= 3) 1) lt41).

Print sig.

(** Specific locality values. *)

Definition locality1 : { x : nat | x <= 4}.
  refine ((exist (fun x => x <= 4) 1) _). omega. Defined.
Definition locality2 : { x : nat | x <= 4}.
  refine ((exist (fun x => x <= 4) 2) _). omega. Defined.
Definition locality3 : { x : nat | x <= 4}.
  refine ((exist (fun x => x <= 4) 3) _). omega. Defined.
Definition locality4 : { x : nat | x <= 4}.
  refine ((exist (fun x => x <= 4) 4) _). omega. Defined.

(** Example locality sets. *)

Definition all_locs : LOCALITY_SELECTION.
  refine (Add _
              (Add _
                   (Add _
                        (Add _ (Empty_set _) locality1)
                        locality2)
                   locality3)
          locality4).
Defined.

(*
Definition pcrDebug : PCR_ATTRIBUTES.
Definition pcrInit : PCR_ATTRIBUTES.
 *)

(** PCR attributes are available on a per PCR basis. Differs by platform 
  configuration *)

Definition allResetAccess : PCR_ATTRIBUTES :=
  (fun i:PCRINDEX => (pcr_attribute all_locs all_locs true)).

(** Following startup clear.  Nonresettable PCRs to 0 and resettable PCRs
  %% to -1 *)

Definition pcrReset(flag : PCR_ATTRIBUTE) : bool :=
  match flag with
    pcr_attribute _ _ b => b
  end.

Definition pcrsReset(flags : PCR_ATTRIBUTES) : PCRVALUES :=
  (fun i => if (pcrReset (flags i)) then resetOne else reset).

(** Following SENTER.  Nonresettable PCRs to same and resettable PCRs to 0 *)
Definition pcrsSenter(curr : PCRVALUES)(flags : PCR_ATTRIBUTES) : PCRVALUES :=
  (fun i => if (pcrReset (flags i)) then reset else (curr i)).

Theorem pcrindex_eq_dec: forall (i j:PCRINDEX), {i=j}+{i<>j}.
Proof.
  intros i j.
  dependent inversion i.
  dependent inversion j.
  destruct (eq_nat_dec x x0).
  subst. left. assert (l=l0). apply proof_irrelevance. subst. reflexivity.
  right. unfold not. intros. inversion H. contradiction.
Defined.

Definition pcrsResetSelection(curr:PCRVALUES)(select:PCR_SELECTION) : PCRVALUES :=
  (fun (i:PCRINDEX) => if (select i) then reset else (curr i)).

(* This is a silly proof that appeared in the PVS file that can likely be
  discarded. *)

Theorem pcrsResetSelectCorrect:
   forall pcrs:PCRVALUES, forall pm:PCR_SELECTION,
     (pcrsResetSelection pcrs pm)=
     (fun (i:PCRINDEX) => if (pm i) then reset else pcrs(i)).
Proof.
  intros pcrs pm. unfold pcrsResetSelection. reflexivity.
Qed.

Definition pcrsExtend(pcrs:PCRVALUES)(i:PCRINDEX)(hv:PCRVAL):PCRVALUES :=
  (fun p => if pcrindex_eq_dec p i then (extend (pcrs i) hv) else pcrs p).

(*
Fixpoint getPCRs(pcrs:PCRVALUES)(pcrMask:PCR_SELECTION):list PCRVALUES :=
 *)

Theorem extend_antisym: forall h1 h2:PCRVAL, forall p:PCR,
      h1<>h2 -> (extend p h1) <> (extend p h2).
Proof.
  intros h1 h2 p H.
  unfold not. intros Heq.
  inversion Heq.
  contradiction.
Qed.