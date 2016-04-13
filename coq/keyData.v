(** ----
%%
%% keyData Theory
%%
%% Author: Brigid Halling
%% Date: Fri Jan 11 13:25:11 CST 2013
%%
%% Description: 
%% 
%% Dependencies:
%%  None
%%
%% Todo: (key - => pending, + => done)
%%
%% ----
*)

Require Import Omega.

(* %% Keys are integers. *)
Definition KVAL : Type := nat.

(** Key types are [symmetric], [public] and [private]. *)
Inductive keyType: Type :=
| symmetric : KVAL -> keyType
| private : KVAL -> keyType
| public : KVAL -> keyType.

(** A [symmetric] key is its own inverse.  A [public] key is the inverse of
  the [private] key with the same [KVAL].  A [private] key is the inverse of
  the [public] key with the same [KVAL]. *)

Fixpoint inverse(k:keyType):keyType :=
match k with
| symmetric k => symmetric k
| public k => private k
| private k => public k
end.


(** The bad key value is 0 *)

Definition badkey:KVAL := 0.

Definition goodkey(key:KVAL) : bool := if (eq_nat_dec key badkey) then true else false.

(**  TPM_KEY_USAGE							(5.8) *)
Inductive KEY_USAGE : Type :=
| signing : KEY_USAGE
| storage : KEY_USAGE
| identity : KEY_USAGE
| authChange : KEY_USAGE
| bind : KEY_USAGE
| legacy : KEY_USAGE
| migration : KEY_USAGE.

(** TPM_ENC_SCHEME							(5.8.1) *)
Inductive ENC_SCHEME : Type :=
| SHA1_MGF1 : ENC_SCHEME
| PVCS : ENC_SCHEME
| SYM_CTR : ENC_SCHEME
| SYM_OFB : ENC_SCHEME
| ENC_NONE : ENC_SCHEME.

Lemma enc_scheme_dec : forall x y:ENC_SCHEME, {x=y}+{x<>y}.
Proof.
  decide equality.
Defined.

(** TPM_SIG_SCHEME							(5.8.1) *)
Inductive SIG_SCHEME : Type :=
| SHA1 : SIG_SCHEME
| DER : SIG_SCHEME
| INFO : SIG_SCHEME
| SIG_NONE : SIG_SCHEME.

Lemma sig_scheme_dec : forall x y:SIG_SCHEME, {x=y}+{x<>y}.
Proof.
  decide equality.
Defined.

Definition validEncScheme(u:KEY_USAGE)(e:ENC_SCHEME) : bool :=
  match u with
  | signing => true
  | storage => if enc_scheme_dec SHA1_MGF1 e then true else false
  | identity => true
  | authChange => if enc_scheme_dec SHA1_MGF1 e then true else false
  | bind => if (enc_scheme_dec SHA1_MGF1 e) then true else if (enc_scheme_dec PVCS e) then true else false
  | legacy => if (enc_scheme_dec SHA1_MGF1 e)then true else if (enc_scheme_dec PVCS e) then true else false
  | migrate => if enc_scheme_dec SHA1_MGF1 e then true else false
  end.

Definition validSigScheme(u:KEY_USAGE)(s:SIG_SCHEME) : bool := 
  match u with
  | signing => if (sig_scheme_dec SHA1 s)
              then true
              else if (sig_scheme_dec DER s) then true
                   else if (sig_scheme_dec INFO s)
                        then true
                        else false
  | storage => true
  | identity => if (sig_scheme_dec SHA1) s then true else false
  | authChange => true
  | bind => true
  | legacy => if (sig_scheme_dec SHA1 s) then true
             else if (sig_scheme_dec s DER) then true
                  else false
  | migrate => true
  end.

(*  keyUsage : KEY_USAGE; *)

(** Flags for defining key properties					(5.10) *)

Record KEY_FLAGS := mk_KEY_FLAGS
                      {redirection : bool;
		       migratable : bool;
		       isVolatile : bool;
		       pcrIgnoredOnRead : bool;
		       migrateAuthority : bool
  	      	      }.

(*  keyFlags : KEY_FLAGS; *)

Definition keyFlagsF : KEY_FLAGS := {| redirection:= false;
     	      		  migratable := false;
	     		  isVolatile := false;
	     		  pcrIgnoredOnRead := false;
	     		  migrateAuthority := false |}.

Eval compute in keyFlagsF.(migratable).

(**  %% This table defines the types of algorithms that may be supported by the TPM
  %% TPM_ALG_AESxxx is used to represent any of TPM_ALG_AES128, TPM_ALG_AES192, 
  %%  or TPM_ALG_AES256. *)

Inductive ALGO_ID : Type := (* % TPM_ALGORITHM_ID				(4.8)*)
| RSA : ALGO_ID
| SHA : ALGO_ID
| HMAC : ALGO_ID
| AESxxx : ALGO_ID
| MGF1 : ALGO_ID
| ALG_XOR : ALGO_ID.

Lemma algo_id_dec : forall x y:ALGO_ID, {x=y}+{x<>y}.
Proof.
  decide equality.
Defined.


(*  %% TPM_KEY_PARMS							(10.1) *)
Record KEY_PARMS : Type := mkKEY_PARAMS {
                               algoId : ALGO_ID;
		               encScheme : ENC_SCHEME;
		               sigScheme : SIG_SCHEME
(*  		     parms : % TPM_RSA_KEY_PARMS or TPM_SYMMETRIC_KEY_PATMS 
		       	      % or no content, depending on algoId *)
  	      	             }.

Definition keyParmsDef : KEY_PARMS := {| algoId:=RSA;
  	      		                 encScheme:=ENC_NONE;
			                 sigScheme:=SIG_NONE |}.

(* %% Migragion scheme indicator (TPM_MIGRATE_SCHEME)			(4.10)*)
Inductive migrateScheme : Type :=
| migrate : migrateScheme
| rewrap : migrateScheme
| maint : migrateScheme
| restrictMigrate : migrateScheme
| restrictApprove : migrateScheme.

