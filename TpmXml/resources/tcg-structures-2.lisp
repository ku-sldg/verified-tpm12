(in-package "ACL2")

(include-book "cutil/deflist" :dir :system)
(include-book "cutil/defaggregate" :dir :system)
(include-book "cutil/defenum" :dir :system)

; ===============================================================
; primitive structures (integers and byte arrays)
; ===============================================================

(defn byte-p (x)
  (and (integerp x)
       (<= 0 x)
       (<= x 255)))

(defn uint16-p (x)
  (and (integerp x)
       (<= 0 x)
       (<= x (- (expt 2 16) 1))))

(defn uint32-p (x)
  (and (integerp x)
       (<= 0 x)
       (<= x (- (expt 2 32) 1))))

(cutil::deflist byte-list-p (x)
  (byte-p x)
  :elementp-of-nil nil
  :true-listp t)

(defn 4-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 4)))

(defn 16-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 16)))

(defn 20-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 20)))

(defn 26-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 26)))

(defn 128-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 128)))

(defn 256-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 256)))

; ===============================================================
; Level 0 Wrappers
; ===============================================================

;; 2.2 TPM_ACTUAL_COUNT
;; The actual number of a counter.
(defn tpm-actual-count-p (x)
  (uint32-p x))

;; 2.2 TPM_AUTHHANDLE
;; Handle to an authorization session
(defn tpm-authhandle-p (x)
  (uint32-p x))

;; 2.2 TPM_CAPABILITY_AREA
;; Identifies a TPM capability area.
(defn tpm-capability-area-p (x)
  (uint32-p x))

;; 2.2 TPM_COUNT_ID
;; The ID value of a monotonic counter
(defn tpm-count-id-p (x)
  (uint32-p x))

;; 2.2 TPM_DELEGATE_INDEX
;; The index value for the delegate NV table
(defn tpm-delegate-index-p (x)
  (uint32-p x))

;; 2.2 TPM_DIRINDEX
;; Index to a DIR register
(defn tpm-dirindex-p (x)
  (uint32-p x))

;; 2.2 TPM_FAMILY_ID
;; The family ID. Families ID’s are automatically assigned a sequence number by the TPM. A trusted proc ...
(defn tpm-family-id-p (x)
  (uint32-p x))

;; 2.2 TPM_FAMILY_VERIFICATION
;; A value used as a label for the most recent verification of this family. Set to zero when not in use ...
(defn tpm-family-verification-p (x)
  (uint32-p x))

;; 2.2 TPM_MODIFIER_INDICATOR
;; The locality modifier
(defn tpm-modifier-indicator-p (x)
  (uint32-p x))

;; 2.2 TPM_PCRINDEX
;; Index to a PCR register
(defn tpm-pcrindex-p (x)
  (uint32-p x))

;; 2.2 TPM_REDIT_COMMAND
;; A command to execute
(defn tpm-redit-command-p (x)
  (uint32-p x))

;; 2.2 TPM_STRUCTURE_TAG
;; The tag for the structure
(defn tpm-structure-tag-p (x)
  (uint16-p x))

;; 2.2 TPM_SYM_MODE
;; The mode of a symmetric encryption
(defn tpm-sym-mode-p (x)
  (uint32-p x))

;; 2.2 TPM_TRANSHANDLE
;; A transport session handle
(defn tpm-transhandle-p (x)
  (uint32-p x))

;; 2.2 TPM_TRANSPORT_ATTRIBUTES
;; Attributes that define what options are in use for a transport session
(defn tpm-transport-attributes-p (x)
  (uint32-p x))

;; 4.3 TPM_ENTITY_TYPE
;; Indicates the types of entity that are supported by the TPM.
(defn tpm-entity-type-p (x)
  (uint16-p x))

;; 4.4 TPM_HANDLE
;; A generic handle could be key, transport etc.
(defn tpm-handle-p (x)
  (uint32-p x))

;; 5.2 TPM_VERSION_BYTE
;; The version info breakdown
(defn tpm-version-byte-p (x)
  (byte-p x))

;; 5.6 TPM_AUTHDATA()
(defn tpm-authdata-p (x)
  (20-byte-list-p x))

;; 16.0 TPM_RESULT
;; The return code from a function
(defn tpm-result-p (x)
  (uint32-p x))

;; 17.0 TPM_COMMAND_CODE
;; The command ordinal.
(defn tpm-command-code-p (x)
  (uint32-p x))

;; 21.4 TPM_CAPABILITY_AREA_set()
(defn tpm-capability-area-set-p (x)
  (uint32-p x))

; ===============================================================
; Level 0 Flags
; ===============================================================

;; 4.6 TPM_STARTUP_EFFECTS
;; How the TPM handles var
(cutil::defaggregate tpm-startup-effects
  ((bit8 booleanp) ;; TPM_RT_DAA_TPM resources are initialized by TPM_Startup(ST_STATE) ...
   (bit7 booleanp) ;; TPM_Startup has no effect on auditDigest
   (bit6 booleanp) ;; auditDigest is set to all zeros on TPM_Startup(ST_CLEAR) but not on other types of TPM_Startup ...
   (bit5 booleanp) ;; auditDigest is set to all zeros on TPM_Startup(any)
   (bit4 booleanp) ;; Deprecated, as the meaning was subject to interpretation. (Was:TPM_RT_KEY resources are initialized  ...
   (bit3 booleanp) ;; TPM_RT_AUTH resources are initialized by TPM_Startup(ST_STATE)
   (bit2 booleanp) ;; TPM_RT_HASH resources are initialized by TPM_Startup(ST_STATE)
   (bit1 booleanp) ;; TPM_RT_TRANS resources are initialized by TPM_Startup(ST_STATE) ...
   (bit0 booleanp) ;; TPM_RT_CONTEXT session (but not key) resources are initialized by TPM_Startup(ST_STATE) ...
  ))

;; 5.17 TPM_CMK_DELEGATE
;; The restrictions placed on delegation of CMK commands
(cutil::defaggregate tpm-cmk-delegate
  ((tpm-cmk-delegate-signing booleanp) ;; When set to 1, this bit SHALL indicate that a delegated command may manipulate a CMK of TPM_KEY_USAG ...
   (tpm-cmk-delegate-storage booleanp) ;; When set to 1, this bit SHALL indicate that a delegated command may manipulate a CMK of TPM_KEY_USAG ...
   (tpm-cmk-delegate-bind booleanp)    ;; When set to 1, this bit SHALL indicate that a delegated command may manipulate a CMK of TPM_KEY_USAG ...
   (tpm-cmk-delegate-legacy booleanp)  ;; When set to 1, this bit SHALL indicate that a delegated command may manipulate a CMK of TPM_KEY_USAG ...
   (tpm-cmk-delegate-migrate booleanp) ;; When set to 1, this bit SHALL indicate that a delegated command may manipulate a CMK of TPM_KEY_USAG ...
  ))

;; 8.6 TPM_LOCALITY_SELECTION()
(cutil::defaggregate tpm-locality-selection
  ((tpm-loc-four booleanp)  ;; Locality 4
   (tpm-loc-three booleanp) ;; Locality 3
   (tpm-loc-two booleanp)   ;; Locality 2
   (tpm-loc-one booleanp)   ;; Locality 1
   (tpm-loc-zero booleanp)  ;; Locality 0. This is the same as the legacy interface.
  ))

;; 10.9 TPM_KEY_CONTROL
;; Allows for controlling of the key when loaded and how to handle TPM_Startup issues ...
(cutil::defaggregate tpm-key-control
  ((tpm-key-control-owner-evict booleanp) ;; Owner controls when the key is evicted from the TPM. When set the TPM MUST preserve key the key acro ...
  ))

;; 20.3 TPM_FAMILY_FLAGS
;; The family flags
(cutil::defaggregate tpm-family-flags
  ((tpm-delegate-admin-lock booleanp) ;; TRUE: Some TPM_Delegate_XXX commands are locked and return TPM_DELEGATE_LOCK; FALSE: TPM_Delegate_XX ...
   (tpm-famflag-enabled booleanp)     ;; When TRUE the table is enabled. The default value is FALSE.
  ))

; ===============================================================
; Level 0 Enumerations
; ===============================================================

;; 4.1 TPM_RESOURCE_TYPE
;; The types of resources that a TPM may have using internal resources
(cutil::defenum tpm-resource-type-p
  (:tpm-rt-key      ;; The handle is a key handle and is the result of a LoadKey type operation ...
   :tpm-rt-auth     ;; The handle is an authorization handle. Auth handles come from TPM_OIAP, TPM_OSAP and TPM_DSAP ...
   :tpm-rt-hash     ;; Reserved for hashes
   :tpm-rt-trans    ;; The handle is for a transport session. Transport handles come from TPM_EstablishTransport ...
   :tpm-rt-context  ;; Resource wrapped and held outside the TPM using the context save/restore commands ...
   :tpm-rt-counter  ;; Reserved for counters
   :tpm-rt-delegate ;; The handle is for a delegate row. These are the internal rows held in NV storage by the TPM ...
   :tpm-rt-daa-tpm  ;; The value is a DAA TPM specific blob
   :tpm-rt-daa-v0   ;; The value is a DAA V0 parameter
   :tpm-rt-daa-v1   ;; The value is a DAA V1 parameter
  ))

;; 4.2 TPM_PAYLOAD_TYPE
;; The information as to what the payload is in an encrypted structure
(cutil::defenum tpm-payload-type-p
  (:tpm-pt-asym               ;; The entity is an asymmetric key
   :tpm-pt-bind               ;; The entity is bound data
   :tpm-pt-migrate            ;; The entity is a migration blob
   :tpm-pt-maint              ;; The entity is a maintenance blob
   :tpm-pt-seal               ;; The entity is sealed data
   :tpm-pt-migrate-restricted ;; The entity is a restricted-migration asymmetric key
   :tpm-pt-migrate-external   ;; The entity is a external migratable key
   :tpm-pt-cmk-migrate        ;; The entity is a CMK migratable blob
  ))

;; 4.4 TPM_KEY_HANDLE
;; The area where a key is held assigned by the TPM.
(cutil::defenum tpm-key-handle-p
  (:tpm-kh-srk       ;; The handle points to the SRK
   :tpm-kh-owner     ;; The handle points to the TPM Owner
   :tpm-kh-revoke    ;; The handle points to the RevokeTrust value
   :tpm-kh-transport ;; The handle points to the TPM_EstablishTransport static authorization ...
   :tpm-kh-operator  ;; The handle points to the Operator auth
   :tpm-kh-admin     ;; The handle points to the delegation administration auth
   :tpm-kh-ek        ;; The handle points to the PUBEK, only usable with TPM_OwnerReadInternalPub ...
  ))

;; 4.5 TPM_STARTUP_TYPE
;; Indicates the start state.
(cutil::defenum tpm-startup-type-p
  (:tpm-st-clear       ;; The TPM is starting up from a clean state
   :tpm-st-state       ;; The TPM is starting up from a saved state
   :tpm-st-deactivated ;; The TPM is to startup and set the deactivated flag to TRUE
  ))

;; 4.7 TPM_PROTOCOL_ID
;; The protocol in use.
(cutil::defenum tpm-protocol-id-p
  (:tpm-pid-oiap      ;; The OIAP protocol.
   :tpm-pid-osap      ;; The OSAP protocol.
   :tpm-pid-adip      ;; The ADIP protocol.
   :tpm-pid-adcp      ;; The ADCP protocol.
   :tpm-pid-owner     ;; The protocol for taking ownership of a TPM.
   :tpm-pid-dsap      ;; The DSAP protocol
   :tpm-pid-transport ;; The transport protocol
  ))

;; 4.8 TPM_ALGORITHM_ID
;; Indicates the type of algorithm.
(cutil::defenum tpm-algorithm-id-p
  (:tpm-alg-rsa    ;; The RSA algorithm.
   ;; reserved     ;; (was the DES algorithm)
   ;; reserved     ;; (was the 3DES algorithm in EDE mode)
   :tpm-alg-sha    ;; The SHA1 algorithm
   :tpm-alg-hmac   ;; The RFC 2104 HMAC algorithm
   :tpm-alg-aes128 ;; The AES algorithm, key size 128
   :tpm-alg-mgf1   ;; The XOR algorithm using MGF1 to create a string the size of the encrypted block ...
   :tpm-alg-aes192 ;; AES, key size 192
   :tpm-alg-aes256 ;; AES, key size 256
   :tpm-alg-xor    ;; XOR using the rolling nonces
  ))

;; 4.9 TPM_PHYSICAL_PRESENCE
;; Sets the state of the physical presence mechanism.
(cutil::defenum tpm-physical-presence-p
  (:tpm-physical-presence-hw-disable    ;; Sets the physicalPresenceHWEnable to FALSE
   :tpm-physical-presence-cmd-disable   ;; Sets the physicalPresenceCMDEnable to FALSE
   :tpm-physical-presence-lifetime-lock ;; Sets the physicalPresenceLifetimeLock to TRUE
   :tpm-physical-presence-hw-enable     ;; Sets the physicalPresenceHWEnable to TRUE
   :tpm-physical-presence-cmd-enable    ;; Sets the physicalPresenceCMDEnable to TRUE
   :tpm-physical-presence-notpresent    ;; Sets PhysicalPresence = FALSE
   :tpm-physical-presence-present       ;; Sets PhysicalPresence = TRUE
   :tpm-physical-presence-lock          ;; Sets PhysicalPresenceLock = TRUE
  ))

;; 4.10 TPM_MIGRATE_SCHEME
;; The definition of the migration scheme
(cutil::defenum tpm-migrate-scheme-p
  (:tpm-ms-migrate          ;; A public key that can be used with all TPM migration commands other than ‘ReWrap’ mode. ...
   :tpm-ms-rewrap           ;; A public key that can be used for the ReWrap mode of TPM_CreateMigrationBlob. ...
   :tpm-ms-maint            ;; A public key that can be used for the Maintenance commands
   :tpm-ms-restrict-migrate ;; The key is to be migrated to a Migration Authority.
   :tpm-ms-restrict-approve ;; The key is to be migrated to an entity approved by a Migration Authority using double wrapping ...
  ))

;; 4.11 TPM_EK_TYPE
;; The type of asymmetric encrypted structure in use by the endorsement key
(cutil::defenum tpm-ek-type-p
  (:tpm-ek-type-activate ;; The blob MUST be TPM_EK_BLOB_ACTIVATE
   :tpm-ek-type-auth     ;; The blob MUST be TPM_EK_BLOB_AUTH
  ))

;; 4.12 TPM_PLATFORM_SPECIFIC
;; The platform specific spec to which the information relates to
(cutil::defenum tpm-platform-specific-p
  (:tpm-ps-pc-11     ;; PC Specific version 1.1
   :tpm-ps-pc-12     ;; PC Specific version 1.2
   :tpm-ps-pda-12    ;; PDA Specific version 1.2
   :tpm-ps-server-12 ;; Server Specific version 1.2
   :tpm-ps-mobile-12 ;; Mobil Specific version 1.2
  ))

;; 5.8 TPM_ENC_SCHEME
;; The definition of the encryption scheme.
(cutil::defenum tpm-enc-scheme-p
  (:tpm-es-none                ;; See section 5.8
   :tpm-es-rsaespkcsv15        ;; See section 5.8
   :tpm-es-rsaesoaep-sha1-mgf1 ;; See section 5.8
   :tpm-es-sym-ctr             ;; See section 5.8
   :tpm-es-sym-ofb             ;; See section 5.8
  ))

;; 5.8 TPM_KEY_USAGE
;; Indicates the permitted usage of the key.
(cutil::defenum tpm-key-usage-p
  (:tpm-key-signing    ;; This SHALL indicate a signing key. The [private] key SHALL be used for signing operations, only. Thi ...
   :tpm-key-storage    ;; This SHALL indicate a storage key. The key SHALL be used to wrap and unwrap other keys in the Protec ...
   :tpm-key-identity   ;; This SHALL indicate an identity key. The key SHALL be used for operations that require a TPM identit ...
   :tpm-key-authchange ;; This SHALL indicate an ephemeral key that is in use during the ChangeAuthAsym process, only. ...
   :tpm-key-bind       ;; This SHALL indicate a key that can be used for TPM_Bind and TPM_UnBind operations only. ...
   :tpm-key-legacy     ;; This SHALL indicate a key that can perform signing and binding operations. The key MAY be used for b ...
   :tpm-key-migrate    ;; This SHALL indicate a key in use for TPM_MigrateKey
  ))

;; 5.8 TPM_SIG_SCHEME
;; The definition of the signature scheme.
(cutil::defenum tpm-sig-scheme-p
  (:tpm-ss-none                ;; See section 5.8
   :tpm-ss-rsassapkcs1v15-sha1 ;; See section 5.8
   :tpm-ss-rsassapkcs1v15-der  ;; See section 5.8
   :tpm-ss-rsassapkcs1v15-info ;; See section 5.8
  ))

;; 5.9 TPM_AUTH_DATA_USAGE
;; Indicates the conditions where it is required that authorization be presented.
(cutil::defenum tpm-auth-data-usage-p
  (:tpm-auth-never          ;; This SHALL indicate that usage of the key without authorization is permitted. ...
   :tpm-auth-always         ;; This SHALL indicate that on each usage of the key the authorization MUST be performed. ...
   :tpm-no-read-pubkey-auth ;; This SHALL indicate that on commands that require the TPM to use the the key, the authorization MUST ...
  ))

;; 5.10 TPM_KEY_FLAGS
;; Indicates information regarding a key.
(cutil::defenum tpm-key-flags-p
  (:redirection      ;; This mask value SHALL indicate the use of redirected output.
   :migratable       ;; This mask value SHALL indicate that the key is migratable.
   :isvolatile       ;; This mask value SHALL indicate that the key MUST be unloaded upon execution of the TPM_Startup(ST_Cl ...
   :pcrignoredonread ;; When TRUE the TPM MUST NOT check digestAtRelease or localityAtRelease for commands that read the pub ...
   :migrateauthority ;; When set indicates that the key is under control of a migration authority. The TPM MUST only allow t ...
  ))

;; 6.0 TPM_TAG
;; The request or response authorization type.
(cutil::defenum tpm-tag-p
  (:tpm-tag-rqu-command       ;; A command with no authentication.
   :tpm-tag-rqu-auth1-command ;; An authenticated command with one authentication handle
   :tpm-tag-rqu-auth2-command ;; An authenticated command with two authentication handles
   :tpm-tag-rsp-command       ;; A response from a command with no authentication
   :tpm-tag-rsp-auth1-command ;; An authenticated response with one authentication handle
   :tpm-tag-rsp-auth2-command ;; An authenticated response with two authentication handles
  ))

;; 19.1 TPM_NV_INDEX
;; The index into the NV storage area
(cutil::defenum tpm-nv-index-p
  (:tpm-nv-index-lock         ;; (required) This value turns on the NV authorization protections. Once executed all NV areas us the p ...
   :tpm-nv-index0             ;; (required) This value allows for the setting of the bGlobalLock flag, which is only reset on TPM_Sta ...
   :tpm-nv-index-dir          ;; (required) Size MUST be 20. This index points to the deprecated DIR command area from 1.1. The TPM M ...
   :tpm-nv-index-tpm          ;; Reserved for TPM use
   :tpm-nv-index-ekcert       ;; The Endorsement credential
   :tpm-nv-index-tpm-cc       ;; The TPM Conformance credential
   :tpm-nv-index-platformcert ;; The platform credential
   :tpm-nv-index-platform-cc  ;; The Platform conformance credential
   :tpm-nv-index-trial        ;; To try TPM_NV_DefineSpace without actually allocating NV space
   :tpm-nv-index-pc           ;; Reserved for PC Client use
   :tpm-nv-index-gpio-xx      ;; Reserved for GPIO pins
   :tpm-nv-index-pda          ;; Reserved for PDA use
   :tpm-nv-index-mobile       ;; Reserved for mobile use
   :tpm-nv-index-server       ;; Reserved for Server use
   :tpm-nv-index-peripheral   ;; Reserved for peripheral use
   :tpm-nv-index-tss          ;; Reserved for TSS use
   :tpm-nv-index-group-resv   ;; Reserved for TCG WG’s
  ))

;; 20.14 TPM_FAMILY_OPERATION
;; What operation is happening
(cutil::defenum tpm-family-operation-p
  (:tpm-family-create     ;; Create a new family
   :tpm-family-enable     ;; Set or reset the enable flag for this family.
   :tpm-family-admin      ;; Prevent administration of this family.
   :tpm-family-invalidate ;; Invalidate a specific family row.
  ))

;; 21.1 TPM_CAPABILITY_AREA_get()
(cutil::defenum tpm-capability-area-get-p
  (:tpm-cap-ord          ;; Boolean value. TRUE indicates that the TPM supports the ordinal. FALSE indicates that the TPM does n ...
   :tpm-cap-alg          ;; Boolean value. TRUE means that the TPM supports the asymmetric algorithm for TPM_Sign, TPM_Seal, TPM ...
   :tpm-cap-pid          ;; Boolean value. TRUE indicates that the TPM supports the protocol, FALSE indicates that the TPM does  ...
   :tpm-cap-flag         ;; See TPM_CAP_FLAG_SUBCAPS
   :tpm-cap-property     ;; See TPM_CAP_PROPERTY_SUBCAPS
   :tpm-cap-version      ;; TPM_STRUCT_VER structure. The major and minor version MUST indicate 1.1. The firmware revision MUST  ...
   :tpm-cap-key-handle   ;; A TPM_KEY_HANDLE_LIST structure that enumerates all key handles loaded on the TPM. The list only con ...
   :tpm-cap-check-loaded ;; A Boolean value. TRUE indicates that the TPM supports and has enough memory available to load a key  ...
   :tpm-cap-sym-mode     ;; A Boolean value. TRUE indicates that the TPM supports the TPM_SYM_MODE, FALSE indicates the TPM does ...
   ;; Unused             ;; --
   ;; Unused             ;; --
   :tpm-cap-key-status   ;; Boolean value of ownerEvict. The handle MUST point to a valid key handle. Return TPM_INVALID_KEYHAND ...
   :tpm-cap-nv-list      ;; A list of TPM_NV_INDEX values that are currently allocated NV storage through TPM_NV_DefineSpace. ...
   ;; Unused             ;; --
   ;; Unused             ;; --
   :tpm-cap-mfr          ;; Manufacturer specific. The manufacturer may provide any additional information regarding the TPM and ...
   :tpm-cap-nv-index     ;; A TPM_NV_DATA_PUBLIC structure that indicates the values for the TPM_NV_INDEX. Returns TPM_BADINDEX  ...
   :tpm-cap-trans-alg    ;; Boolean value. TRUE means that the TPM supports the algorithm for TPM_EstablishTransport, TPM_Execut ...
   ;; Unused             ;; --
   :tpm-cap-handle       ;; A TPM_KEY_HANDLE_LIST structure that enumerates all handles currently loaded in the TPM for the give ...
   :tpm-cap-trans-es     ;; Boolean value. TRUE means the TPM supports the encryption scheme in a transport session for at least ...
   ;; Unused             ;; --
   :tpm-cap-auth-encrypt ;; Boolean value. TRUE indicates that the TPM supports the encryption algorithm in OSAP encryption of A ...
   :tpm-cap-select-size  ;; Boolean value. TRUE indicates that the TPM supports reqSize in TPM_PCR_SELECTION -> sizeOfSelect for ...
   :tpm-cap-da-logic     ;; (OPTIONAL) A TPM_DA_INFO or TPM_DA_INFO_LIMITED structure that returns data according to the selecte ...
   :tpm-cap-version-val  ;; TPM_CAP_VERSION_INFO structure. The TPM fills in the structure and returns the information indicatin ...
  ))

;; 21.1 TPM_CAP_FLAG_SUBCAPS()
(cutil::defenum tpm-cap-flag-subcaps-p
  (:tpm-cap-flag-permanent ;; Return the TPM_PERMANENT_FLAGS structure. Each flag in the structure returns as a byte. ...
   :tpm-cap-flag-volatile  ;; Return the TPM_STCLEAR_FLAGS structure. Each flag in the structure returns as a byte. ...
  ))

;; 21.2 TPM_CAP_PROPERTY_SUBCAPS()
(cutil::defenum tpm-cap-property-subcaps-p
  (:tpm-cap-prop-pcr              ;; UINT32 value. Returns the number of PCR registers supported by the TPM ...
   :tpm-cap-prop-dir              ;; UNIT32. Deprecated. Returns the number of DIR, which is now fixed at 1 ...
   :tpm-cap-prop-manufacturer     ;; UINT32 value. Returns the vendor ID unique to each TPM manufacturer. ...
   :tpm-cap-prop-keys             ;; UINT32 value. Returns the number of 2048-bit RSA keys that can be loaded. This may vary with time an ...
   :tpm-cap-prop-min-counter      ;; UINT32. The minimum amount of time in 10ths of a second that must pass between invocations of increm ...
   :tpm-cap-prop-authsess         ;; UINT32. The number of available authorization sessions. This may vary with time and circumstances. ...
   :tpm-cap-prop-transess         ;; UINT32. The number of available transport sessions. This may vary with time and circumstances ...
   :tpm-cap-prop-counters         ;; UINT32. The number of available monotonic counters. This may vary with time and circumstances. ...
   :tpm-cap-prop-max-authsess     ;; UINT32. The maximum number of loaded authorization sessions the TPM supports. ...
   :tpm-cap-prop-max-transess     ;; UINT32. The maximum number of loaded transport sessions the TPM supports. ...
   :tpm-cap-prop-max-counters     ;; UINT32. The maximum number of monotonic counters under control of TPM_CreateCounter ...
   :tpm-cap-prop-max-keys         ;; UINT32. The maximum number of 2048 RSA keys that the TPM can support. The number does not include th ...
   :tpm-cap-prop-owner            ;; BOOL. A value of TRUE indicates that the TPM has successfully installed an owner. ...
   :tpm-cap-prop-context          ;; UINT32. The number of available saved session slots. This may vary with time and circumstances. ...
   :tpm-cap-prop-max-context      ;; UINT32. The maximum number of saved session slots.
   :tpm-cap-prop-familyrows       ;; UINT32. The maximum number of rows in the family table
   :tpm-cap-prop-tis-timeout      ;; A 4 element array of UINT32 values each denoting the timeout value in microseconds for the following ...
   :tpm-cap-prop-startup-effect   ;; The TPM_STARTUP_EFFECTS structure
   :tpm-cap-prop-delegate-row     ;; UINT32. The maximum size of the delegate table in rows.
   ;; open                        ;; --
   :tpm-cap-prop-max-daasess      ;; UINT32. The maximum number of loaded DAA sessions (join or sign) that the TPM supports. ...
   :tpm-cap-prop-daasess          ;; UINT32. The number of available DAA sessions. This may vary with time and circumstances ...
   :tpm-cap-prop-context-dist     ;; UINT32. The maximum distance between context count values. This MUST be at least 2^16-1 ...
   :tpm-cap-prop-daa-interrupt    ;; BOOL. A value of TRUE indicates that the TPM will accept ANY command while executing a DAA Join or S ...
   :tpm-cap-prop-sessions         ;; UNIT32. The number of available authorization and transport sessions from the pool. This may vary wi ...
   :tpm-cap-prop-max-sessions     ;; UINT32. The maximum number of sessions the TPM supports.
   :tpm-cap-prop-cmk-restriction  ;; UINT32 TPM_Permanent_Data -> restrictDelegate
   :tpm-cap-prop-duration         ;; A 3 element array of UINT32 values each denoting the duration value in microseconds of the duration  ...
   ;; open                        ;; --
   :tpm-cap-prop-active-counter   ;; TPM_COUNT_ID. The id of the current counter. 0xff..ff if no counter is active, either because no cou ...
   :tpm-cap-prop-max-nv-available ;; UINT32. Deprecated. The maximum number of NV space that can be allocated, MAY vary with time and cir ...
   :tpm-cap-prop-input-buffer     ;; UINT32. The maximum size of the TPM input buffer or output buffers in bytes. ...
   ;; XX                          ;; Next number
  ))

;; 21.9 TPM_DA_STATE
;; The state of the dictionary attack mitigation logic
(cutil::defenum tpm-da-state-p
  (:tpm-da-state-inactive ;; The dictionary attack mitigation logic is currently inactive
   :tpm-da-state-active   ;; The dictionary attack mitigation logic is active. TPM_DA_ACTION_TYPE (21.10) is in progress. ...
  ))

; ===============================================================
; Level 0 Records
; ===============================================================

;; 5.1 TPM_STRUCT_VER()
(cutil::defaggregate tpm-struct-ver
  ((major byte-p)     ;; This SHALL indicate the major version of the structure. MUST be 0x01 ...
   (minor byte-p)     ;; This SHALL indicate the minor version of the structure. MUST be 0x01 ...
   (rev-major byte-p) ;; This MUST be 0x00 on output, ignored on input
   (rev-minor byte-p) ;; This MUST be 0x00 on output, ignored on input
  ))

;; 5.4 TPM_DIGEST()
(cutil::defaggregate tpm-digest
  ((digest byte-list-p) ;; This SHALL be the actual digest information
  ))

;; 5.5 TPM_NONCE()
(cutil::defaggregate tpm-nonce
  ((nonce 20-byte-list-p) ;; This SHALL be the 20 bytes of random data. When created by the TPM the value MUST be the next 20 byt ...
  ))

;; 5.7 TPM_KEY_HANDLE_LIST()
(cutil::defaggregate tpm-key-handle-list
  ((loaded uint16-p) ;; The number of keys currently loaded in the TPM.
   (handle uint32-p) ;; An array of handles, one for each key currently loaded in the TPM ...
  ))

;; 5.18 TPM_SELECT_SIZE()
(cutil::defaggregate tpm-select-size
  ((major byte-p)      ;; This SHALL indicate the major version of the TPM. This MUST be 0x01 ...
   (minor byte-p)      ;; This SHALL indicate the minor version of the TPM. This MAY be 0x01 or 0x02 ...
   (req-size uint16-p) ;; This SHALL indicate the value for a sizeOfSelect field in the TPM_SELECTION structure ...
  ))

;; 7.6 TPM_SESSION_DATA()
(cutil::defaggregate tpm-session-data
  ((place-holder booleanp) ;; Vendor specific
  ))

;; 8.1 TPM_PCR_SELECTION()
(cutil::defaggregate tpm-pcr-selection
  ((size-of-select uint16-p) ;; The size in bytes of the pcrSelect structure
   (pcr-select byte-list-p)  ;; This SHALL be a bit map that indicates if a PCR is active or not ...
  ))

;; 10.1 TPM_RSA_KEY_PARMS()
(cutil::defaggregate tpm-rsa-key-parms
  ((key-length uint32-p)    ;; This specifies the size of the RSA key in bits
   (num-primes uint32-p)    ;; This specifies the number of prime factors used by this RSA key. ...
   (exponent-size uint32-p) ;; This SHALL be the size of the exponent. If the key is using the default exponent then the exponentSi ...
   (exponent byte-list-p)   ;; The public exponent of this key
  ))

;; 10.1 TPM_SYMMETRIC_KEY_PARMS()
(cutil::defaggregate tpm-symmetric-key-parms
  ((key-length uint32-p) ;; This SHALL indicate the length of the key in bits
   (block-size uint32-p) ;; This SHALL indicate the block size of the algorithm
   (iv-size uint32-p)    ;; This SHALL indicate the size of the IV
   (iv byte-list-p)      ;; The initialization vector
  ))

;; 10.4 TPM_STORE_PUBKEY()
(cutil::defaggregate tpm-store-pubkey
  ((key-length uint32-p) ;; This SHALL be the length of the key field.
   (key byte-list-p)     ;; This SHALL be a structure interpreted according to the algorithm Id in the corresponding TPM_KEY_PAR ...
  ))

;; 10.7 TPM_STORE_PRIVKEY()
(cutil::defaggregate tpm-store-privkey
  ((key-length uint32-p) ;; This SHALL be the length of the key field.
   (key byte-list-p)     ;; This SHALL be a structure interpreted according to the algorithm Id in the corresponding TPM_KEY str ...
  ))

;; 20.4 TPM_FAMILY_LABEL()
(cutil::defaggregate tpm-family-label
  ((label byte-p) ;; A sequence number that software can map to a string of bytes that can be displayed or used by the ap ...
  ))

;; 20.7 TPM_DELEGATE_LABEL()
(cutil::defaggregate tpm-delegate-label
  ((label byte-p) ;; A byte that can be displayed or used by the applications. This MUST not contain sensitive informatio ...
  ))

; ===============================================================
; TPM_PCRVALUE[] and TPM_DIGEST[]
; ===============================================================

(cutil::deflist tpm-pcrvalue-list-p (x)
  (tpm-pcrvalue-p x)
  :elementp-of-nil nil
  :true-listp t)

(cutil::deflist tpm-digest-list-p (x)
  (tpm-digest-p x)
  :elementp-of-nil nil
  :true-listp t)

; ===============================================================
; Level 1 Wrappers
; ===============================================================

;; 5.4 TPM_CHOSENID_HASH
;; This SHALL be the digest of the chosen identityLabel and privacyCA for a new TPM identity. ...
(defn tpm-chosenid-hash-p (x)
  (tpm-digest-p x))

;; 5.4 TPM_COMPOSITE_HASH
;; This SHALL be the hash of a list of PCR indexes and PCR values that a key or data is bound to. ...
(defn tpm-composite-hash-p (x)
  (tpm-digest-p x))

;; 5.4 TPM_DIRVALUE
;; This SHALL be the value of a DIR register
(defn tpm-dirvalue-p (x)
  (tpm-digest-p x))

;; 5.4 TPM_PCRVALUE
;; The value inside of the PCR
(defn tpm-pcrvalue-p (x)
  (tpm-digest-p x))

;; 5.5 TPM_DAA_CONTEXT_SEED
;; This SHALL be a random value
(defn tpm-daa-context-seed-p (x)
  (tpm-nonce-p x))

;; 5.5 TPM_DAA_TPM_SEED
;; This SHALL be a random value generated by a TPM immediately after the EK is installed in that TPM, w ...
(defn tpm-daa-tpm-seed-p (x)
  (tpm-nonce-p x))

;; 5.6 TPM_SECRET
;; A secret plaintext value used in the authorization process.
(defn tpm-secret-p (x)
  (tpm-authdata-p x))

; ===============================================================
; Level 1 Records
; ===============================================================

;; 5.3 TPM_VERSION()
(cutil::defaggregate tpm-version
  ((major tpm-version-byte-p) ;; This SHALL indicate the major version of the TPM, mostSigVer MUST be 0x01, leastSigVer MUST be 0x00 ...
   (minor tpm-version-byte-p) ;; This SHALL indicate the minor version of the TPM, mostSigVer MUST be 0x01 or 0x02, leastSigVer MUST  ...
   (rev-major byte-p)         ;; This SHALL be the value of the TPM_PERMANENT_DATA -> revMajor
   (rev-minor byte-p)         ;; This SHALL be the value of the TPM_PERMANENT_DATA -> revMinor
  ))

;; 5.13 TPM_COUNTER_VALUE()
(cutil::defaggregate tpm-counter-value
  ((tag tpm-structure-tag-p)    ;; TPM_TAG_COUNTER_VALUE
   (label 4-byte-list-p)        ;; The label for the counter
   (counter tpm-actual-count-p) ;; The 32-bit counter value.
  ))

;; 8.8 TPM_PCR_ATTRIBUTES()
(cutil::defaggregate tpm-pcr-attributes
  ((pcr-reset booleanp)                        ;; A value of TRUE SHALL indicate that the PCR register can be reset using the TPM_PCR_Reset command. I ...
   (pcr-reset-local tpm-locality-selection-p)  ;; An indication of which localities can reset the PCR
   (pcr-extend-local tpm-locality-selection-p) ;; An indication of which localities can perform extends on the PCR. ...
  ))

;; 9.4 TPM_SYMMETRIC_KEY()
(cutil::defaggregate tpm-symmetric-key
  ((alg-id tpm-algorithm-id-p)   ;; This SHALL be the algorithm identifier of the symmetric key.
   (enc-scheme tpm-enc-scheme-p) ;; This SHALL fully identify the manner in which the key will be used for encryption operations. ...
   (size uint16-p)               ;; This SHALL be the size of the data parameter in bytes
   (data byte-list-p)            ;; This SHALL be the symmetric key data
  ))

;; 10.1 TPM_KEY_PARMS()
(cutil::defaggregate tpm-key-parms
  ((algorithm-id tpm-algorithm-id-p) ;; This SHALL be the key algorithm in use
   (enc-scheme tpm-enc-scheme-p)     ;; This SHALL be the encryption scheme that the key uses to encrypt information ...
   (sig-scheme tpm-sig-scheme-p)     ;; This SHALL be the signature scheme that the key uses to perform digital signatures ...
   (parm-size uint32-p)              ;; This SHALL be the size of the parms field in bytes
   (parms byte-list-p)               ;; This SHALL be the parameter information dependant upon the key algorithm. ...
  ))

;; 13.1 TPM_TRANSPORT_PUBLIC()
(cutil::defaggregate tpm-transport-public
  ((tag tpm-structure-tag-p)                     ;; TPM_TAG_TRANSPORT_PUBLIC
   (trans-attributes tpm-transport-attributes-p) ;; The attributes of this session
   (alg-id tpm-algorithm-id-p)                   ;; This SHALL be the algorithm identifier of the symmetric key.
   (enc-scheme tpm-enc-scheme-p)                 ;; This SHALL fully identify the manner in which the key will be used for encryption operations. ...
  ))

;; 15.1 TPM_CURRENT_TICKS()
(cutil::defaggregate tpm-current-ticks
  ((tag tpm-structure-tag-p) ;; TPM_TAG_CURRENT_TICKS
   (current-ticks uint64-p)  ;; The number of ticks since the start of this tick session
   (tick-rate uint16-p)      ;; The number of microseconds per tick. The maximum resolution of the TPM tick counter is thus 1 micros ...
   (tick-nonce tpm-nonce-p)  ;; The nonce created by the TPM when resetting the currentTicks to 0. This indicates the beginning of a ...
  ))

;; 19.3 TPM_NV_DATA_PUBLIC()
(cutil::defaggregate tpm-nv-data-public
  ((tag tpm-structure-tag-p) ;; TPM_TAG_NV_ATTRIBUTES
   (attributes uint32-p)     ;; The attribute area
  ))

;; 20.2 TPM_DELEGATIONS()
(cutil::defaggregate tpm-delegations
  ((tag tpm-structure-tag-p) ;; This SHALL be TPM_TAG_DELEGATIONS
   (delegate-type uint32-p)  ;; Owner or key
   (per1 uint32-p)           ;; The first block of permissions
   (per2 uint32-p)           ;; The second block of permissions
  ))

;; 20.5 TPM_FAMILY_TABLE_ENTRY()
(cutil::defaggregate tpm-family-table-entry
  ((tag tpm-structure-tag-p)                      ;; This SHALL be TPM_TAG_FAMILY_TABLE_ENTRY
   (family-label tpm-family-label-p)              ;; A sequence number that software can map to a string of bytes that can be displayed or used by the ap ...
   (family-id tpm-family-id-p)                    ;; The family ID in use to tie values together. This is not a sensitive value. ...
   (verification-count tpm-family-verification-p) ;; The value inserted into delegation rows to indicate that they are the current generation of rows. Us ...
   (flags tpm-family-flags-p)                     ;; See section on TPM_FAMILY_FLAGS.
  ))

;; 21.10 TPM_DA_ACTION_TYPE()
(cutil::defaggregate tpm-da-action-type
  ((tag tpm-structure-tag-p) ;; MUST be TPM_TAG_DA_ACTION_TYPE
   (actions uint32-p)        ;; The action taken when TPM_DA_STATE is TPM_DA_STATE_ACTIVE.
  ))

;; 22.3 TPM_DAA_ISSUER()
(cutil::defaggregate tpm-daa-issuer
  ((tag tpm-structure-tag-p)       ;; MUST be TPM_TAG_DAA_ISSUER
   (daa-digest-r0 tpm-digest-p)    ;; A digest of the parameter “R0”, which is not secret and may be common to many TPMs. ...
   (daa-digest-r1 tpm-digest-p)    ;; A digest of the parameter “R1”, which is not secret and may be common to many TPMs. ...
   (daa-digest-s0 tpm-digest-p)    ;; A digest of the parameter “S0”, which is not secret and may be common to many TPMs. ...
   (daa-digest-s1 tpm-digest-p)    ;; A digest of the parameter “S1”, which is not secret and may be common to many TPMs. ...
   (daa-digest-n tpm-digest-p)     ;; A digest of the parameter “n”, which is not secret and may be common to many TPMs. ...
   (daa-digest-gamma tpm-digest-p) ;; A digest of the parameter “gamma”, which is not secret and may be common to many TPMs. ...
   (daa-generic-q 26-byte-list-p)  ;; The parameter q, which is not secret and may be common to many TPMs. Note that q is slightly larger  ...
  ))

;; 22.4 TPM_DAA_TPM()
(cutil::defaggregate tpm-daa-tpm
  ((tag tpm-structure-tag-p)       ;; MUST be TPM_TAG_DAA_TPM
   (daa-digestissuer tpm-digest-p) ;; A digest of a TPM_DAA_ISSUER structure that contains the parameters used to generate this TPM_DAA_TP ...
   (daa-digest-v0 tpm-digest-p)    ;; A digest of the parameter “v0”, which is secret and specific to this TPM. “v0” is generated during a ...
   (daa-digest-v1 tpm-digest-p)    ;; A digest of the parameter “v1”, which is secret and specific to this TPM. “v1” is generated during a ...
   (daa-rekey tpm-digest-p)        ;; A digest related to the rekeying process, which is not secret but is specific to this TPM, and must  ...
   (daa-count uint32-p)            ;; The parameter “count”, which is not secret but must be consistent across JOIN/SIGN sessions. “count” ...
  ))

;; 22.6 TPM_DAA_JOINDATA()
(cutil::defaggregate tpm-daa-joindata
  ((daa-join-u0 128-byte-list-p) ;; A TPM-specific secret “u0”, used during the JOIN phase, and discarded afterwards. ...
   (daa-join-u1 128-byte-list-p) ;; A TPM-specific secret “u1”, used during the JOIN phase, and discarded afterwards. ...
   (daa-digest-n0 tpm-digest-p)  ;; A digest of the parameter “n0”, which is an RSA public key with exponent 2^16 +1 ...
  ))

; ===============================================================
; Level 2 Records
; ===============================================================

;; 8.5 TPM_PCR_INFO_SHORT()
(cutil::defaggregate tpm-pcr-info-short
  ((pcr-selection tpm-pcr-selection-p)            ;; This SHALL be the selection of PCRs that specifies the digestAtRelease ...
   (locality-at-release tpm-locality-selection-p) ;; This SHALL be the locality modifier required to release the information. This value must not be zero ...
   (digest-at-release tpm-composite-hash-p)       ;; This SHALL be the digest of the PCR indices and PCR values to verify when revealing auth data ...
  ))

;; 10.2 TPM_KEY()
(cutil::defaggregate tpm-key
  ((ver tpm-struct-ver-p)                  ;; This MUST be 1.1.0.0
   (key-usage tpm-key-usage-p)             ;; This SHALL be the TPM key usage that determines the operations permitted with this key ...
   (key-flags tpm-key-flags-p)             ;; This SHALL be the indication of migration, redirection etc.
   (auth-data-usage tpm-auth-data-usage-p) ;; This SHALL Indicate the conditions where it is required that authorization be presented. ...
   (algorithm-parms tpm-key-parms-p)       ;; This SHALL be the information regarding the algorithm for this key ...
   (pcr-info-size uint32-p)                ;; This SHALL be the length of the pcrInfo parameter. If the key is not bound to a PCR this value SHOUL ...
   (pcr-info byte-list-p)                  ;; This SHALL be a structure of type TPM_PCR_INFO, or an empty array if the key is not bound to PCRs. ...
   (pub-key tpm-store-pubkey-p)            ;; This SHALL be the public portion of the key
   (enc-data-size uint32-p)                ;; This SHALL be the size of the encData parameter.
   (enc-data byte-list-p)                  ;; This SHALL be an encrypted TPM_STORE_ASYMKEY structure or TPM_MIGRATE_ASYMKEY structure ...
  ))

;; 10.5 TPM_PUBKEY()
(cutil::defaggregate tpm-pubkey
  ((algorithm-parms tpm-key-parms-p) ;; This SHALL be the information regarding this key
   (pub-key tpm-store-pubkey-p)      ;; This SHALL be the public key information
  ))

;; 20.6 TPM_FAMILY_TABLE()
(cutil::defaggregate tpm-family-table
  ((fam-table-row tpm-family-table-entry-p) ;; The array of family table entries
  ))

;; 22.5 TPM_DAA_CONTEXT()
(cutil::defaggregate tpm-daa-context
  ((tag tpm-structure-tag-p)                ;; MUST be TPM_TAG_DAA_CONTEXT
   (daa-digestcontext tpm-digest-p)         ;; A digest of parameters used to generate this structure. The parameters vary, depending on whether th ...
   (daa-digest tpm-digest-p)                ;; A running digest of certain parameters generated during DAA computation; operationally the same as a ...
   (daa-contextseed tpm-daa-context-seed-p) ;; The seed used to generate other DAA session parameters
   (daa-scratch 256-byte-list-p)            ;; Memory used to hold different parameters at different times of DAA computation, but only one paramet ...
   (daa-stage byte-p)                       ;; A counter, indicating the stage of DAA computation that was most recently completed. The value of th ...
  ))

; ===============================================================
; Level 3 Records
; ===============================================================

;; 20.8 TPM_DELEGATE_PUBLIC()
(cutil::defaggregate tpm-delegate-public
  ((tag tpm-structure-tag-p)                      ;; This SHALL be TPM_TAG_DELEGATE_PUBLIC
   (rowlabel tpm-delegate-label-p)                ;; This SHALL be the label for the row. It MUST not contain any sensitive information. ...
   (pcr-info tpm-pcr-info-short-p)                ;; This SHALL be the designation of the process that can use the permission. This is a not sensitive va ...
   (permissions tpm-delegations-p)                ;; This SHALL be the permissions that are allowed to the indicated process. This is not a sensitive val ...
   (family-id tpm-family-id-p)                    ;; This SHALL be the family ID that identifies which family the row belongs to. This is not a sensitive ...
   (verification-count tpm-family-verification-p) ;; A copy of verificationCount from the associated family table. This is not a sensitive value. ...
  ))

; ===============================================================
; Level 4 Records
; ===============================================================

;; 20.9 TPM_DELEGATE_TABLE_ROW()
(cutil::defaggregate tpm-delegate-table-row
  ((tag tpm-structure-tag-p)   ;; This SHALL be TPM_TAG_DELEGATE_TABLE_ROW
   (pub tpm-delegate-public-p) ;; This SHALL be the public information for a table row.
   (auth-value tpm-secret-p)   ;; This SHALL be the AuthData value that can use the permissions. This is a sensitive value. ...
  ))

; ===============================================================
; Level 5 Records
; ===============================================================

;; 20.10 TPM_DELEGATE_TABLE()
(cutil::defaggregate tpm-delegate-table
  ((del-row tpm-delegate-table-row-p) ;; The array of delegations
  ))
