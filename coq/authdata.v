(** ----
%%
%% Authdata Theory
%%
%% Author: Brigid Halling
%% Date: Tue Jan 8 11:22:39 CST 2013
%%
%% Description: 
%% 
%% Dependencies:
%%  none 	
%%
%% Todo: (key - => pending, + => done)
%% ----
*)


(*
%   %% TPM_AUTHDATA							(5.6)
    %% The AuthData is the info that is saved or passed to provide proof of
    %%  ownership of an entity. 
    %% When sending AuthData to the TPM the TPM does not validate the decryption
    %%  of the data. It is the responsibility of the entity owner to validate
    %%  the AuthData data was properly received by the TPM. This could be done
    %%  by immediatedly attempting to open an authorization session.
    %% The owner of the data can select any value for the data.
%   AUTHDATA : DATATYPE
%   BEGIN
%     tpmSecret(i:nat) : tpmSecret?
%     tpmEncAuth(i:nat) : tpmEncAuth?
%   END AUTHDATA;
*)

(** TPM_AUTH_DATA_USAGE						(5.9)  *)
Inductive AUTH_DATA_USAGE : Type :=
| always : AUTH_DATA_USAGE
| never : AUTH_DATA_USAGE.
