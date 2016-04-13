(** ----
%%
%% Types Theory
%%
%% Author: Brigid Halling
%% Date: 
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

Require Export Ensembles.

Inductive resource : Type := (*% TPM_RESOURCE_TYPE				(4.1)*)
    | RT_KEY : resource	(* The handle is key handle and is result of a LoadKey 
    	     	     	   type operation *)
    | RT_AUTH : resource (* The handle is an authorization handle. Auth handles 
    	      	       	    come from TPM_OIAP, TPM_OSAP and TPM_DSAP *)
    | RT_HASH : resource (* Reserved for hashes *)
    | RT_TRANS : resource (* The handle is for a transport session. Transport
    	       		     handles come from TPM_EstablishTransport *)
    | RT_CONTEXT : resource  (* Resource wrapped and held outside the TPM
    	       	 	       using the context save/restore commands *)
    | RT_COUNTER : resource  (* Reserved for counters *)
    | RT_DELEGATE : resource (* The handle is for a delegate row. These are the
    		  	        internal rows held in NV storage by the TPM *)
    | RT_DAA_TPM : resource  (* The value is a DAA TPM specific blob *)
    | RT_DAA_V0 : resource   (* The value is a DAA V0 parameter *)
    | RT_DAA_V1 : resource.   (* The value is a DAA V1 parameter *)

Lemma resource_dec : forall x y:resource, {x=y}+{x<>y}.
Proof.
  decide equality.
Defined.

  (** This structure specifies the type of payload in various messages.
      The payload may indicate whether the key is a CMK, and the CMK type. 
      The distinction was put here rather than in TPM_KEY_USAGE:
      - for backward compatibility
      - some commands only see the TPM_STORE_ASYMKEY, not the entire TPM_KEY *)

  Inductive payload : Type :=	(* TPM_PAYLOAD_TYPE				(4.2) *)
  | ASYM : payload	(* The entity is an asymmetric key *)
  | BIND : payload 	(* The entity is bound data *)
  | MIGRATE : payload 	(* The entity is a migration blob *)
  | MAINT : payload 	(* The entity is a maintenance blob *)
  | SEAL : payload 	(* The entity is sealed data *)
  | MIGRATE_RESTRICTED : payload  (* The entity is a restricted-
    		       	             migration asymmetric key *)
  | MIGRATE_EXTERNAL : payload (* The entity is external migratable key *)
  | CMK_MIGRATE : payload.  (* The entity is a CMK migratable blob *)

Lemma payload_dec : forall x y:payload, {x=y}+{x<>y}.
Proof.
  decide equality.
Defined.

  
(**  %% This specifies the types of entity and ADIP encryption schemes that are 
  %%  supported by the TPM. TPM entities are objects with authorization, such as
  %%  the owner, a key, NV defined space, etc. *)

Inductive entity : Type :=	(* TPM_ENTITY_TYPE				(4.3) *)
  | KEYHANDLE : entity	(* The entity is a keyHandle or key *)
  | TPM_OWNER : entity 	(* The entity is the TPM Owner *)
  | DATA : entity       (* The entity is some data *)
  | SRK : entity        (* The entity is the SRK *)
  | KEY : entity        (* The entity is a key or keyHandle *)
  | REVOKE : entity 	(* The entity is the RevokeTrust value *)
  | DEL_OWNER_BLOB : entity  (* The entity is a delegate owner blob *)
  | DEL_ROW : entity	(* The entity is a delegate row *)
  | DEL_KEY_BLOB : entity (* The entity is a delegate key blob *)
  | COUNTER : entity	  (* The entity is a counter *)
  | NV : entity		(* The entity is a NV index *)
  | OPERATOR : entity	(* The entity is the operator *)
  | RESERVED_HANDLE : entity (* This value avoids collisions with the 
    		      		handle MSB setting. *)
(*    %% TPM_ENTITY_TYPE MSB Values *)
  | ET_XOR : entity     (* XOR *)
  | AES128_CTR : entity.	 (* AES 128 bits in CTR mode *)

(** 
  %% Handles (4.4) in keys.pvs
  %% TPM_STARTUP_TYPE (4.5) in startupData.pvs
  %% TPM_STARTUP_EFECTS (4.6) TODO?
 *)

(*  %% This value identifies the protocol in use. *)
Inductive protocol : Type := (* % TPM_PROTOCOL_ID				(4.7) *)
| OIAP : protocol	(* The OIAP protocol. *)
| OSAP : protocol 	(* The OSAP protocol. *)
| ADIP : protocol 	(* The ADIP protocol. *)
| ADCP : protocol 	(* The ADCP protocol. *)
| OWNER : protocol 	(* The protocol for taking ownership of a TPM.  *)
| DSAP : protocol 	(* The DSAP protocol *)
| TRANSPORT : protocol. (* The transport protocol *)

Inductive physPres : Type :=	(* % TPM_PHYSICAL_PRESENCE				(4.9) *)
  | HW_DISABLE : physPres (* Sets the physicalPresenceHWEnable to FALSE *)
  | CMD_DISABLE : physPres (* Sets the physicalPresenceCMDEnable to FALSE *)
  | LIFETIME_LOCK : physPres (* Sets physicalPresenceLifetimeLock to TRUE *)
  | HW_ENABLE : physPres (* Sets the physicalPresenceHWEnable to TRUE *)
  | CMD_ENABLE : physPres (* Sets the physicalPresenceCMDEnable to TRUE *)
  | NOTPRESENT : physPres (* Sets PhysicalPresence = FALSE *)
  | PRESENT : physPres (* Sets PhysicalPresence = TRUE *)
  | LOCK : physPres. (* Sets PhysicalPresenceLock = TRUE *)

Definition PHYSPRES : Type = Ensemble physPres.

(*
  %% TPM_ALGORITHM_ID (4.8) in keyData.pvs
  %% TPM_MIGRATE_SCHEME (4.10) in keyData.pvs
  %% TPM_EK_TYPE (4.11) in data.pvs
  %% TPM_PLATFORM_SPECIFIC (4.12) TODO?
*)
