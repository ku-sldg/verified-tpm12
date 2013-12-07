(in-package "ACL2")

(include-book "cutil/defaggregate" :dir :system)
(include-book "cutil/deflist" :dir :system)

(program)

(cutil::defaggregate tpm-struct-ver
  ( major
    minor
    rev-major
    rev-minor)
:require
  ( (byte-p-of-tpm-struct-ver->major
      (byte major))
    (byte-p-of-tpm-struct-ver->minor
      (byte minor))
    (byte-p-of-tpm-struct-ver->rev-major
      (byte rev-major))
    (byte-p-of-tpm-struct-ver->rev-minor
      (byte rev-minor)))

(cutil::defaggregate tpm-version-byte
  ( least-sig-ver
    most-sig-ver)
:require
  ( (nibble-p-of-tpm-version-byte->least-sig-ver
      (nibble least-sig-ver))
    (nibble-p-of-tpm-version-byte->most-sig-ver
      (nibble most-sig-ver)))

(cutil::defaggregate tpm-version
  ( major
    minor
    rev-major
    rev-minor)
:require
  ( (tpm-version-byte-p-of-tpm-version->major
      (tpm-version-byte major))
    (tpm-version-byte-p-of-tpm-version->minor
      (tpm-version-byte minor))
    (byte-p-of-tpm-version->rev-major
      (byte rev-major))
    (byte-p-of-tpm-version->rev-minor
      (byte rev-minor)))

(cutil::defaggregate tpm-digest
  ( digest)
:require
  ( (byte[]-p-of-tpm-digest->digest
      (byte[] digest)))

(cutil::defaggregate tpm-key-handle-list
  ( loaded
    handle)
:require
  ( (uint16-p-of-tpm-key-handle-list->loaded
      (uint16 loaded))
    (uint32-p-of-tpm-key-handle-list->handle
      (uint32 handle)))

(cutil::defaggregate tpm-changeauth-validate
  ( new-auth-secret
    n1)
:require
  ( (tpm-secret-p-of-tpm-changeauth-validate->new-auth-secret
      (tpm-secret new-auth-secret))
    (tpm-nonce-p-of-tpm-changeauth-validate->n1
      (tpm-nonce n1)))

(cutil::defaggregate tpm-migrationkeyauth
  ( migration-key
    migration-scheme
    digest)
:require
  ( (tpm-pubkey-p-of-tpm-migrationkeyauth->migration-key
      (tpm-pubkey migration-key))
    (tpm-migrate-scheme-p-of-tpm-migrationkeyauth->migration-scheme
      (tpm-migrate-scheme migration-scheme))
    (tpm-digest-p-of-tpm-migrationkeyauth->digest
      (tpm-digest digest)))

(cutil::defaggregate tpm-counter-value
  ( tag
    label
    counter)
:require
  ( (tpm-structure-tag-p-of-tpm-counter-value->tag
      (tpm-structure-tag tag))
    (byte[4]-p-of-tpm-counter-value->label
      (byte[4] label))
    (tpm-actual-count-p-of-tpm-counter-value->counter
      (tpm-actual-count counter)))

(cutil::defaggregate tpm-sign-info
  ( tag
    fixed
    replay
    data-len
    data)
:require
  ( (tpm-structure-tag-p-of-tpm-sign-info->tag
      (tpm-structure-tag tag))
    (byte[4]-p-of-tpm-sign-info->fixed
      (byte[4] fixed))
    (tpm-nonce-p-of-tpm-sign-info->replay
      (tpm-nonce replay))
    (uint32-p-of-tpm-sign-info->data-len
      (uint32 data-len))
    (byte*-p-of-tpm-sign-info->data
      (byte* data)))

(cutil::defaggregate tpm-msa-composite
  ( ms-alist
    mig-auth-digest)
:require
  ( (uint32-p-of-tpm-msa-composite->ms-alist
      (uint32 ms-alist))
    (tpm-digest[]-p-of-tpm-msa-composite->mig-auth-digest
      (tpm-digest[] mig-auth-digest)))

(cutil::defaggregate tpm-cmk-auth
  ( migration-authority-digest
    destination-key-digest
    source-key-digest)
:require
  ( (tpm-digest-p-of-tpm-cmk-auth->migration-authority-digest
      (tpm-digest migration-authority-digest))
    (tpm-digest-p-of-tpm-cmk-auth->destination-key-digest
      (tpm-digest destination-key-digest))
    (tpm-digest-p-of-tpm-cmk-auth->source-key-digest
      (tpm-digest source-key-digest)))

(cutil::defaggregate tpm-select-size
  ( major
    minor
    req-size)
:require
  ( (byte-p-of-tpm-select-size->major
      (byte major))
    (byte-p-of-tpm-select-size->minor
      (byte minor))
    (uint16-p-of-tpm-select-size->req-size
      (uint16 req-size)))

(cutil::defaggregate tpm-cmk-migauth
  ( tag
    msa-digest
    pub-key-digest)
:require
  ( (tpm-structure-tag-p-of-tpm-cmk-migauth->tag
      (tpm-structure-tag tag))
    (tpm-digest-p-of-tpm-cmk-migauth->msa-digest
      (tpm-digest msa-digest))
    (tpm-digest-p-of-tpm-cmk-migauth->pub-key-digest
      (tpm-digest pub-key-digest)))

(cutil::defaggregate tpm-cmk-sigticket
  ( tag
    ver-key-digest
    signed-data)
:require
  ( (tpm-structure-tag-p-of-tpm-cmk-sigticket->tag
      (tpm-structure-tag tag))
    (tpm-digest-p-of-tpm-cmk-sigticket->ver-key-digest
      (tpm-digest ver-key-digest))
    (tpm-digest-p-of-tpm-cmk-sigticket->signed-data
      (tpm-digest signed-data)))

(cutil::defaggregate tpm-cmk-ma-approval
  ( tag
    migration-authority-digest)
:require
  ( (tpm-structure-tag-p-of-tpm-cmk-ma-approval->tag
      (tpm-structure-tag tag))
    (tpm-digest-p-of-tpm-cmk-ma-approval->migration-authority-digest
      (tpm-digest migration-authority-digest)))

(cutil::defaggregate tpm-permanent-flags
  ( tag
    disable
    ownership
    deactivated
    read-pubek
    disable-owner-clear
    allow-maintenance
    physical-presence-lifetime-lock
    physical-presence-hw-enable
    physical-presence-cmd-enable
    cekp-used
    tp-mpost
    tp-mpost-lock
    fips
    operator
    enable-revoke-ek
    nv-locked
    read-srk-pub
    tpm-established
    maintenance-done
    disable-full-da-logic-info)
:require
  ( (tpm-structure-tag-p-of-tpm-permanent-flags->tag
      (tpm-structure-tag tag))
    (bool-p-of-tpm-permanent-flags->disable
      (bool disable))
    (bool-p-of-tpm-permanent-flags->ownership
      (bool ownership))
    (bool-p-of-tpm-permanent-flags->deactivated
      (bool deactivated))
    (bool-p-of-tpm-permanent-flags->read-pubek
      (bool read-pubek))
    (bool-p-of-tpm-permanent-flags->disable-owner-clear
      (bool disable-owner-clear))
    (bool-p-of-tpm-permanent-flags->allow-maintenance
      (bool allow-maintenance))
    (bool-p-of-tpm-permanent-flags->physical-presence-lifetime-lock
      (bool physical-presence-lifetime-lock))
    (bool-p-of-tpm-permanent-flags->physical-presence-hw-enable
      (bool physical-presence-hw-enable))
    (bool-p-of-tpm-permanent-flags->physical-presence-cmd-enable
      (bool physical-presence-cmd-enable))
    (bool-p-of-tpm-permanent-flags->cekp-used
      (bool cekp-used))
    (bool-p-of-tpm-permanent-flags->tp-mpost
      (bool tp-mpost))
    (bool-p-of-tpm-permanent-flags->tp-mpost-lock
      (bool tp-mpost-lock))
    (bool-p-of-tpm-permanent-flags->fips
      (bool fips))
    (bool-p-of-tpm-permanent-flags->operator
      (bool operator))
    (bool-p-of-tpm-permanent-flags->enable-revoke-ek
      (bool enable-revoke-ek))
    (bool-p-of-tpm-permanent-flags->nv-locked
      (bool nv-locked))
    (bool-p-of-tpm-permanent-flags->read-srk-pub
      (bool read-srk-pub))
    (bool-p-of-tpm-permanent-flags->tpm-established
      (bool tpm-established))
    (bool-p-of-tpm-permanent-flags->maintenance-done
      (bool maintenance-done))
    (bool-p-of-tpm-permanent-flags->disable-full-da-logic-info
      (bool disable-full-da-logic-info)))

(cutil::defaggregate tpm-stclear-flags
  ( tag
    deactivated
    disable-force-clear
    physical-presence
    physical-presence-lock
    b-global-lock)
:require
  ( (tpm-structure-tag-p-of-tpm-stclear-flags->tag
      (tpm-structure-tag tag))
    (bool-p-of-tpm-stclear-flags->deactivated
      (bool deactivated))
    (bool-p-of-tpm-stclear-flags->disable-force-clear
      (bool disable-force-clear))
    (bool-p-of-tpm-stclear-flags->physical-presence
      (bool physical-presence))
    (bool-p-of-tpm-stclear-flags->physical-presence-lock
      (bool physical-presence-lock))
    (bool-p-of-tpm-stclear-flags->b-global-lock
      (bool b-global-lock)))

(cutil::defaggregate tpm-stany-flags
  ( tag
    post-initialise
    locality-modifier
    transport-exclusive
    tos-present)
:require
  ( (tpm-structure-tag-p-of-tpm-stany-flags->tag
      (tpm-structure-tag tag))
    (bool-p-of-tpm-stany-flags->post-initialise
      (bool post-initialise))
    (tpm-modifier-indicator-p-of-tpm-stany-flags->locality-modifier
      (tpm-modifier-indicator locality-modifier))
    (bool-p-of-tpm-stany-flags->transport-exclusive
      (bool transport-exclusive))
    (bool-p-of-tpm-stany-flags->tos-present
      (bool tos-present)))

(cutil::defaggregate tpm-permanent-data
  ( tag
    rev-major
    rev-minor
    tpm-proof
    owner-auth
    operator-auth
    manu-maint-pub
    endorsement-key
    srk
    delegate-key
    context-key
    audit-monotonic-counter
    monotonic-counter
    pcr-attrib
    ordinal-audit-status
    auth-dir
    rng-state
    family-table
    delegate-table
    ek-reset
    last-family-id
    no-owner-nv-write
    restrict-delegate
    tpm-daa-seed
    daa-proof
    daa-blob-key)
:require
  ( (tpm-structure-tag-p-of-tpm-permanent-data->tag
      (tpm-structure-tag tag))
    (byte-p-of-tpm-permanent-data->rev-major
      (byte rev-major))
    (byte-p-of-tpm-permanent-data->rev-minor
      (byte rev-minor))
    (tpm-secret-p-of-tpm-permanent-data->tpm-proof
      (tpm-secret tpm-proof))
    (tpm-secret-p-of-tpm-permanent-data->owner-auth
      (tpm-secret owner-auth))
    (tpm-secret-p-of-tpm-permanent-data->operator-auth
      (tpm-secret operator-auth))
    (tpm-pubkey-p-of-tpm-permanent-data->manu-maint-pub
      (tpm-pubkey manu-maint-pub))
    (tpm-key-p-of-tpm-permanent-data->endorsement-key
      (tpm-key endorsement-key))
    (tpm-key-p-of-tpm-permanent-data->srk
      (tpm-key srk))
    (tpm-key-p-of-tpm-permanent-data->delegate-key
      (tpm-key delegate-key))
    (tpm-key-p-of-tpm-permanent-data->context-key
      (tpm-key context-key))
    (tpm-counter-value-p-of-tpm-permanent-data->audit-monotonic-counter
      (tpm-counter-value audit-monotonic-counter))
    (tpm-counter-value-p-of-tpm-permanent-data->monotonic-counter
      (tpm-counter-value monotonic-counter))
    (tpm-pcr-attributes-p-of-tpm-permanent-data->pcr-attrib
      (tpm-pcr-attributes pcr-attrib))
    (byte[]-p-of-tpm-permanent-data->ordinal-audit-status
      (byte[] ordinal-audit-status))
    (tpm-dirvalue-p-of-tpm-permanent-data->auth-dir
      (tpm-dirvalue auth-dir))
    (byte[]-p-of-tpm-permanent-data->rng-state
      (byte[] rng-state))
    (tpm-family-table-p-of-tpm-permanent-data->family-table
      (tpm-family-table family-table))
    (tpm-delegate-table-p-of-tpm-permanent-data->delegate-table
      (tpm-delegate-table delegate-table))
    (tpm-nonce-p-of-tpm-permanent-data->ek-reset
      (tpm-nonce ek-reset))
    (uint32-p-of-tpm-permanent-data->last-family-id
      (uint32 last-family-id))
    (uint32-p-of-tpm-permanent-data->no-owner-nv-write
      (uint32 no-owner-nv-write))
    (tpm-cmk-delegate-p-of-tpm-permanent-data->restrict-delegate
      (tpm-cmk-delegate restrict-delegate))
    (tpm-daa-tpm-seed-p-of-tpm-permanent-data->tpm-daa-seed
      (tpm-daa-tpm-seed tpm-daa-seed))
    (tpm-nonce-p-of-tpm-permanent-data->daa-proof
      (tpm-nonce daa-proof))
    (tpm-key-p-of-tpm-permanent-data->daa-blob-key
      (tpm-key daa-blob-key)))

(cutil::defaggregate tpm-stclear-data
  ( tag
    context-nonce-key
    count-id
    owner-reference
    disable-reset-lock
    pcr
    deferred-physical-presence)
:require
  ( (tpm-structure-tag-p-of-tpm-stclear-data->tag
      (tpm-structure-tag tag))
    (tpm-nonce-p-of-tpm-stclear-data->context-nonce-key
      (tpm-nonce context-nonce-key))
    (tpm-count-id-p-of-tpm-stclear-data->count-id
      (tpm-count-id count-id))
    (uint32-p-of-tpm-stclear-data->owner-reference
      (uint32 owner-reference))
    (bool-p-of-tpm-stclear-data->disable-reset-lock
      (bool disable-reset-lock))
    (tpm-pcrvalue-p-of-tpm-stclear-data->pcr
      (tpm-pcrvalue pcr))
    (uint32-p-of-tpm-stclear-data->deferred-physical-presence
      (uint32 deferred-physical-presence)))

(cutil::defaggregate tpm-stany-data
  ( tag
    context-nonce-session
    audit-digest
    current-ticks
    context-count
    context-list
    sessions)
:require
  ( (tpm-structure-tag-p-of-tpm-stany-data->tag
      (tpm-structure-tag tag))
    (tpm-nonce-p-of-tpm-stany-data->context-nonce-session
      (tpm-nonce context-nonce-session))
    (tpm-digest-p-of-tpm-stany-data->audit-digest
      (tpm-digest audit-digest))
    (tpm-current-ticks-p-of-tpm-stany-data->current-ticks
      (tpm-current-ticks current-ticks))
    (uint32-p-of-tpm-stany-data->context-count
      (uint32 context-count))
    (uint32-p-of-tpm-stany-data->context-list
      (uint32 context-list))
    (tpm-session-data-p-of-tpm-stany-data->sessions
      (tpm-session-data sessions)))

(cutil::defaggregate tpm-pcr-selection
  ( size-of-select
    pcr-select)
:require
  ( (uint16-p-of-tpm-pcr-selection->size-of-select
      (uint16 size-of-select))
    (byte*-p-of-tpm-pcr-selection->pcr-select
      (byte* pcr-select)))

(cutil::defaggregate tpm-pcr-composite
  ( select
    value-size
    pcr-value[])
:require
  ( (tpm-pcr-selection-p-of-tpm-pcr-composite->select
      (tpm-pcr-selection select))
    (uint32-p-of-tpm-pcr-composite->value-size
      (uint32 value-size))
    (tpm-pcrvalue-p-of-tpm-pcr-composite->pcr-value[]
      (tpm-pcrvalue pcr-value[])))

(cutil::defaggregate tpm-pcr-info
  ( pcr-selection
    digest-at-release
    digest-at-creation)
:require
  ( (tpm-pcr-selection-p-of-tpm-pcr-info->pcr-selection
      (tpm-pcr-selection pcr-selection))
    (tpm-composite-hash-p-of-tpm-pcr-info->digest-at-release
      (tpm-composite-hash digest-at-release))
    (tpm-composite-hash-p-of-tpm-pcr-info->digest-at-creation
      (tpm-composite-hash digest-at-creation)))

(cutil::defaggregate tpm-pcr-info-long
  ( tag
    locality-at-creation
    locality-at-release
    creation-pcr-selection
    release-pcr-selection
    digest-at-creation
    digest-at-release)
:require
  ( (tpm-structure-tag-p-of-tpm-pcr-info-long->tag
      (tpm-structure-tag tag))
    (tpm-locality-selection-p-of-tpm-pcr-info-long->locality-at-creation
      (tpm-locality-selection locality-at-creation))
    (tpm-locality-selection-p-of-tpm-pcr-info-long->locality-at-release
      (tpm-locality-selection locality-at-release))
    (tpm-pcr-selection-p-of-tpm-pcr-info-long->creation-pcr-selection
      (tpm-pcr-selection creation-pcr-selection))
    (tpm-pcr-selection-p-of-tpm-pcr-info-long->release-pcr-selection
      (tpm-pcr-selection release-pcr-selection))
    (tpm-composite-hash-p-of-tpm-pcr-info-long->digest-at-creation
      (tpm-composite-hash digest-at-creation))
    (tpm-composite-hash-p-of-tpm-pcr-info-long->digest-at-release
      (tpm-composite-hash digest-at-release)))

(cutil::defaggregate tpm-pcr-info-short
  ( pcr-selection
    locality-at-release
    digest-at-release)
:require
  ( (tpm-pcr-selection-p-of-tpm-pcr-info-short->pcr-selection
      (tpm-pcr-selection pcr-selection))
    (tpm-locality-selection-p-of-tpm-pcr-info-short->locality-at-release
      (tpm-locality-selection locality-at-release))
    (tpm-composite-hash-p-of-tpm-pcr-info-short->digest-at-release
      (tpm-composite-hash digest-at-release)))

(cutil::defaggregate tpm-pcr-attributes
  ( pcr-reset
    pcr-reset-local
    pcr-extend-local)
:require
  ( (bool-p-of-tpm-pcr-attributes->pcr-reset
      (bool pcr-reset))
    (tpm-locality-selection-p-of-tpm-pcr-attributes->pcr-reset-local
      (tpm-locality-selection pcr-reset-local))
    (tpm-locality-selection-p-of-tpm-pcr-attributes->pcr-extend-local
      (tpm-locality-selection pcr-extend-local)))

(cutil::defaggregate tpm-stored-data
  ( ver
    seal-info-size
    seal-info
    enc-data-size
    enc-data)
:require
  ( (tpm-struct-ver-p-of-tpm-stored-data->ver
      (tpm-struct-ver ver))
    (uint32-p-of-tpm-stored-data->seal-info-size
      (uint32 seal-info-size))
    (byte*-p-of-tpm-stored-data->seal-info
      (byte* seal-info))
    (uint32-p-of-tpm-stored-data->enc-data-size
      (uint32 enc-data-size))
    (byte*-p-of-tpm-stored-data->enc-data
      (byte* enc-data)))

(cutil::defaggregate tpm-stored-data12
  ( tag
    et
    seal-info-size
    seal-info
    enc-data-size
    enc-data)
:require
  ( (tpm-structure-tag-p-of-tpm-stored-data12->tag
      (tpm-structure-tag tag))
    (tpm-entity-type-p-of-tpm-stored-data12->et
      (tpm-entity-type et))
    (uint32-p-of-tpm-stored-data12->seal-info-size
      (uint32 seal-info-size))
    (byte*-p-of-tpm-stored-data12->seal-info
      (byte* seal-info))
    (uint32-p-of-tpm-stored-data12->enc-data-size
      (uint32 enc-data-size))
    (byte*-p-of-tpm-stored-data12->enc-data
      (byte* enc-data)))

(cutil::defaggregate tpm-sealed-data
  ( payload
    auth-data
    tpm-proof
    stored-digest
    data-size
    data)
:require
  ( (tpm-payload-type-p-of-tpm-sealed-data->payload
      (tpm-payload-type payload))
    (tpm-secret-p-of-tpm-sealed-data->auth-data
      (tpm-secret auth-data))
    (tpm-secret-p-of-tpm-sealed-data->tpm-proof
      (tpm-secret tpm-proof))
    (tpm-digest-p-of-tpm-sealed-data->stored-digest
      (tpm-digest stored-digest))
    (uint32-p-of-tpm-sealed-data->data-size
      (uint32 data-size))
    (byte*-p-of-tpm-sealed-data->data
      (byte* data)))

(cutil::defaggregate tpm-symmetric-key
  ( alg-id
    enc-scheme
    size
    data)
:require
  ( (tpm-algorithm-id-p-of-tpm-symmetric-key->alg-id
      (tpm-algorithm-id alg-id))
    (tpm-enc-scheme-p-of-tpm-symmetric-key->enc-scheme
      (tpm-enc-scheme enc-scheme))
    (uint16-p-of-tpm-symmetric-key->size
      (uint16 size))
    (byte*-p-of-tpm-symmetric-key->data
      (byte* data)))

(cutil::defaggregate tpm-bound-data
  ( ver
    payload
    payload-data)
:require
  ( (tpm-struct-ver-p-of-tpm-bound-data->ver
      (tpm-struct-ver ver))
    (tpm-payload-type-p-of-tpm-bound-data->payload
      (tpm-payload-type payload))
    (byte[]-p-of-tpm-bound-data->payload-data
      (byte[] payload-data)))

(cutil::defaggregate tpm-key-parms
  ( algorithm-id
    enc-scheme
    sig-scheme
    parm-size
    parms)
:require
  ( (tpm-algorithm-id-p-of-tpm-key-parms->algorithm-id
      (tpm-algorithm-id algorithm-id))
    (tpm-enc-scheme-p-of-tpm-key-parms->enc-scheme
      (tpm-enc-scheme enc-scheme))
    (tpm-sig-scheme-p-of-tpm-key-parms->sig-scheme
      (tpm-sig-scheme sig-scheme))
    (uint32-p-of-tpm-key-parms->parm-size
      (uint32 parm-size))
    (byte*-p-of-tpm-key-parms->parms
      (byte* parms)))

(cutil::defaggregate tpm-rsa-key-parms
  ( key-length
    num-primes
    exponent-size
    exponent)
:require
  ( (uint32-p-of-tpm-rsa-key-parms->key-length
      (uint32 key-length))
    (uint32-p-of-tpm-rsa-key-parms->num-primes
      (uint32 num-primes))
    (uint32-p-of-tpm-rsa-key-parms->exponent-size
      (uint32 exponent-size))
    (byte*-p-of-tpm-rsa-key-parms->exponent
      (byte* exponent)))

(cutil::defaggregate tpm-symmetric-key-parms
  ( key-length
    block-size
    iv-size
    iv)
:require
  ( (uint32-p-of-tpm-symmetric-key-parms->key-length
      (uint32 key-length))
    (uint32-p-of-tpm-symmetric-key-parms->block-size
      (uint32 block-size))
    (uint32-p-of-tpm-symmetric-key-parms->iv-size
      (uint32 iv-size))
    (byte*-p-of-tpm-symmetric-key-parms->iv
      (byte* iv)))

(cutil::defaggregate tpm-key
  ( ver
    key-usage
    key-flags
    auth-data-usage
    algorithm-parms
    pcr-info-size
    pcr-info
    pub-key
    enc-data-size
    enc-data)
:require
  ( (tpm-struct-ver-p-of-tpm-key->ver
      (tpm-struct-ver ver))
    (tpm-key-usage-p-of-tpm-key->key-usage
      (tpm-key-usage key-usage))
    (tpm-key-flags-p-of-tpm-key->key-flags
      (tpm-key-flags key-flags))
    (tpm-auth-data-usage-p-of-tpm-key->auth-data-usage
      (tpm-auth-data-usage auth-data-usage))
    (tpm-key-parms-p-of-tpm-key->algorithm-parms
      (tpm-key-parms algorithm-parms))
    (uint32-p-of-tpm-key->pcr-info-size
      (uint32 pcr-info-size))
    (byte*-p-of-tpm-key->pcr-info
      (byte* pcr-info))
    (tpm-store-pubkey-p-of-tpm-key->pub-key
      (tpm-store-pubkey pub-key))
    (uint32-p-of-tpm-key->enc-data-size
      (uint32 enc-data-size))
    (byte*-p-of-tpm-key->enc-data
      (byte* enc-data)))

(cutil::defaggregate tpm-key12
  ( tag
    fill
    key-usage
    key-flags
    auth-data-usage
    algorithm-parms
    pcr-info-size
    pcr-info
    pub-key
    enc-data-size
    enc-data)
:require
  ( (tpm-structure-tag-p-of-tpm-key12->tag
      (tpm-structure-tag tag))
    (uint16-p-of-tpm-key12->fill
      (uint16 fill))
    (tpm-key-usage-p-of-tpm-key12->key-usage
      (tpm-key-usage key-usage))
    (tpm-key-flags-p-of-tpm-key12->key-flags
      (tpm-key-flags key-flags))
    (tpm-auth-data-usage-p-of-tpm-key12->auth-data-usage
      (tpm-auth-data-usage auth-data-usage))
    (tpm-key-parms-p-of-tpm-key12->algorithm-parms
      (tpm-key-parms algorithm-parms))
    (uint32-p-of-tpm-key12->pcr-info-size
      (uint32 pcr-info-size))
    (byte*-p-of-tpm-key12->pcr-info
      (byte* pcr-info))
    (tpm-store-pubkey-p-of-tpm-key12->pub-key
      (tpm-store-pubkey pub-key))
    (uint32-p-of-tpm-key12->enc-data-size
      (uint32 enc-data-size))
    (byte*-p-of-tpm-key12->enc-data
      (byte* enc-data)))

(cutil::defaggregate tpm-store-pubkey
  ( key-length
    key)
:require
  ( (uint32-p-of-tpm-store-pubkey->key-length
      (uint32 key-length))
    (byte*-p-of-tpm-store-pubkey->key
      (byte* key)))

(cutil::defaggregate tpm-pubkey
  ( algorithm-parms
    pub-key)
:require
  ( (tpm-key-parms-p-of-tpm-pubkey->algorithm-parms
      (tpm-key-parms algorithm-parms))
    (tpm-store-pubkey-p-of-tpm-pubkey->pub-key
      (tpm-store-pubkey pub-key)))

(cutil::defaggregate tpm-store-asymkey
  ( payload
    usage-auth
    migration-auth
    pub-data-digest
    priv-key)
:require
  ( (tpm-payload-type-p-of-tpm-store-asymkey->payload
      (tpm-payload-type payload))
    (tpm-secret-p-of-tpm-store-asymkey->usage-auth
      (tpm-secret usage-auth))
    (tpm-secret-p-of-tpm-store-asymkey->migration-auth
      (tpm-secret migration-auth))
    (tpm-digest-p-of-tpm-store-asymkey->pub-data-digest
      (tpm-digest pub-data-digest))
    (tpm-store-privkey-p-of-tpm-store-asymkey->priv-key
      (tpm-store-privkey priv-key)))

(cutil::defaggregate tpm-store-privkey
  ( key-length
    key)
:require
  ( (uint32-p-of-tpm-store-privkey->key-length
      (uint32 key-length))
    (byte*-p-of-tpm-store-privkey->key
      (byte* key)))

(cutil::defaggregate tpm-migrate-asymkey
  ( payload
    usage-auth
    pub-data-digest
    part-priv-key-len
    part-priv-key)
:require
  ( (tpm-payload-type-p-of-tpm-migrate-asymkey->payload
      (tpm-payload-type payload))
    (tpm-secret-p-of-tpm-migrate-asymkey->usage-auth
      (tpm-secret usage-auth))
    (tpm-digest-p-of-tpm-migrate-asymkey->pub-data-digest
      (tpm-digest pub-data-digest))
    (uint32-p-of-tpm-migrate-asymkey->part-priv-key-len
      (uint32 part-priv-key-len))
    (byte*-p-of-tpm-migrate-asymkey->part-priv-key
      (byte* part-priv-key)))

(cutil::defaggregate tpm-certify-info
  ( version
    key-usage
    key-flags
    auth-data-usage
    algorithm-parms
    pub-key-digest
    data
    parent-pcr-status
    pcr-info-size
    pcr-info)
:require
  ( (tpm-struct-ver-p-of-tpm-certify-info->version
      (tpm-struct-ver version))
    (tpm-key-usage-p-of-tpm-certify-info->key-usage
      (tpm-key-usage key-usage))
    (tpm-key-flags-p-of-tpm-certify-info->key-flags
      (tpm-key-flags key-flags))
    (tpm-auth-data-usage-p-of-tpm-certify-info->auth-data-usage
      (tpm-auth-data-usage auth-data-usage))
    (tpm-key-parms-p-of-tpm-certify-info->algorithm-parms
      (tpm-key-parms algorithm-parms))
    (tpm-digest-p-of-tpm-certify-info->pub-key-digest
      (tpm-digest pub-key-digest))
    (tpm-nonce-p-of-tpm-certify-info->data
      (tpm-nonce data))
    (bool-p-of-tpm-certify-info->parent-pcr-status
      (bool parent-pcr-status))
    (uint32-p-of-tpm-certify-info->pcr-info-size
      (uint32 pcr-info-size))
    (byte*-p-of-tpm-certify-info->pcr-info
      (byte* pcr-info)))

(cutil::defaggregate tpm-certify-info2
  ( tag
    fill
    payload-type
    key-usage
    key-flags
    auth-data-usage
    algorithm-parms
    pub-key-digest
    data
    parent-pcr-status
    pcr-info-size
    pcr-info
    migration-authority-size
    migration-authority)
:require
  ( (tpm-structure-tag-p-of-tpm-certify-info2->tag
      (tpm-structure-tag tag))
    (byte-p-of-tpm-certify-info2->fill
      (byte fill))
    (tpm-payload-type-p-of-tpm-certify-info2->payload-type
      (tpm-payload-type payload-type))
    (tpm-key-usage-p-of-tpm-certify-info2->key-usage
      (tpm-key-usage key-usage))
    (tpm-key-flags-p-of-tpm-certify-info2->key-flags
      (tpm-key-flags key-flags))
    (tpm-auth-data-usage-p-of-tpm-certify-info2->auth-data-usage
      (tpm-auth-data-usage auth-data-usage))
    (tpm-key-parms-p-of-tpm-certify-info2->algorithm-parms
      (tpm-key-parms algorithm-parms))
    (tpm-digest-p-of-tpm-certify-info2->pub-key-digest
      (tpm-digest pub-key-digest))
    (tpm-nonce-p-of-tpm-certify-info2->data
      (tpm-nonce data))
    (bool-p-of-tpm-certify-info2->parent-pcr-status
      (bool parent-pcr-status))
    (uint32-p-of-tpm-certify-info2->pcr-info-size
      (uint32 pcr-info-size))
    (byte*-p-of-tpm-certify-info2->pcr-info
      (byte* pcr-info))
    (uint32-p-of-tpm-certify-info2->migration-authority-size
      (uint32 migration-authority-size))
    (byte*-p-of-tpm-certify-info2->migration-authority
      (byte* migration-authority)))

(cutil::defaggregate tpm-quote-info
  ( version
    fixed
    digest-value
    external-data)
:require
  ( (tpm-struct-ver-p-of-tpm-quote-info->version
      (tpm-struct-ver version))
    (byte[4]-p-of-tpm-quote-info->fixed
      (byte[4] fixed))
    (tpm-composite-hash-p-of-tpm-quote-info->digest-value
      (tpm-composite-hash digest-value))
    (tpm-nonce-p-of-tpm-quote-info->external-data
      (tpm-nonce external-data)))

(cutil::defaggregate tpm-quote-info2
  ( tag
    fixed
    external-data
    info-short)
:require
  ( (tpm-structure-tag-p-of-tpm-quote-info2->tag
      (tpm-structure-tag tag))
    (byte[4]-p-of-tpm-quote-info2->fixed
      (byte[4] fixed))
    (tpm-nonce-p-of-tpm-quote-info2->external-data
      (tpm-nonce external-data))
    (tpm-pcr-info-short-p-of-tpm-quote-info2->info-short
      (tpm-pcr-info-short info-short)))

(cutil::defaggregate tpm-ek-blob
  ( tag
    ek-type
    blob-size
    blob)
:require
  ( (tpm-structure-tag-p-of-tpm-ek-blob->tag
      (tpm-structure-tag tag))
    (tpm-ek-type-p-of-tpm-ek-blob->ek-type
      (tpm-ek-type ek-type))
    (uint32-p-of-tpm-ek-blob->blob-size
      (uint32 blob-size))
    (byte*-p-of-tpm-ek-blob->blob
      (byte* blob)))

(cutil::defaggregate tpm-ek-blob-activate
  ( tag
    session-key
    id-digest
    pcr-info)
:require
  ( (tpm-structure-tag-p-of-tpm-ek-blob-activate->tag
      (tpm-structure-tag tag))
    (tpm-symmetric-key-p-of-tpm-ek-blob-activate->session-key
      (tpm-symmetric-key session-key))
    (tpm-digest-p-of-tpm-ek-blob-activate->id-digest
      (tpm-digest id-digest))
    (tpm-pcr-info-short-p-of-tpm-ek-blob-activate->pcr-info
      (tpm-pcr-info-short pcr-info)))

(cutil::defaggregate tpm-ek-blob-auth
  ( tag
    auth-value)
:require
  ( (tpm-structure-tag-p-of-tpm-ek-blob-auth->tag
      (tpm-structure-tag tag))
    (tpm-secret-p-of-tpm-ek-blob-auth->auth-value
      (tpm-secret auth-value)))

(cutil::defaggregate tpm-chosenid-hash
  ( identity-label
    privacy-ca)
:require
  ( (byte[]-p-of-tpm-chosenid-hash->identity-label
      (byte[] identity-label))
    (tpm-pubkey-p-of-tpm-chosenid-hash->privacy-ca
      (tpm-pubkey privacy-ca)))

(cutil::defaggregate tpm-identity-contents
  ( ver
    ordinal
    label-priv-ca-digest
    identity-pub-key)
:require
  ( (tpm-struct-ver-p-of-tpm-identity-contents->ver
      (tpm-struct-ver ver))
    (uint32-p-of-tpm-identity-contents->ordinal
      (uint32 ordinal))
    (tpm-chosenid-hash-p-of-tpm-identity-contents->label-priv-ca-digest
      (tpm-chosenid-hash label-priv-ca-digest))
    (tpm-pubkey-p-of-tpm-identity-contents->identity-pub-key
      (tpm-pubkey identity-pub-key)))

(cutil::defaggregate tpm-identity-req
  ( asym-size
    sym-size
    asym-algorithm
    sym-algorithm
    asym-blob
    sym-blob)
:require
  ( (uint32-p-of-tpm-identity-req->asym-size
      (uint32 asym-size))
    (uint32-p-of-tpm-identity-req->sym-size
      (uint32 sym-size))
    (tpm-key-parms-p-of-tpm-identity-req->asym-algorithm
      (tpm-key-parms asym-algorithm))
    (tpm-key-parms-p-of-tpm-identity-req->sym-algorithm
      (tpm-key-parms sym-algorithm))
    (byte*-p-of-tpm-identity-req->asym-blob
      (byte* asym-blob))
    (byte*-p-of-tpm-identity-req->sym-blob
      (byte* sym-blob)))

(cutil::defaggregate tpm-identity-proof
  ( ver
    label-size
    identity-binding-size
    endorsement-size
    platform-size
    conformance-size
    identity-key
    label-area
    identity-binding
    endorsement-credential
    platform-credential
    conformance-credential)
:require
  ( (tpm-struct-ver-p-of-tpm-identity-proof->ver
      (tpm-struct-ver ver))
    (uint32-p-of-tpm-identity-proof->label-size
      (uint32 label-size))
    (uint32-p-of-tpm-identity-proof->identity-binding-size
      (uint32 identity-binding-size))
    (uint32-p-of-tpm-identity-proof->endorsement-size
      (uint32 endorsement-size))
    (uint32-p-of-tpm-identity-proof->platform-size
      (uint32 platform-size))
    (uint32-p-of-tpm-identity-proof->conformance-size
      (uint32 conformance-size))
    (tpm-pubkey-p-of-tpm-identity-proof->identity-key
      (tpm-pubkey identity-key))
    (byte*-p-of-tpm-identity-proof->label-area
      (byte* label-area))
    (byte*-p-of-tpm-identity-proof->identity-binding
      (byte* identity-binding))
    (byte*-p-of-tpm-identity-proof->endorsement-credential
      (byte* endorsement-credential))
    (byte*-p-of-tpm-identity-proof->platform-credential
      (byte* platform-credential))
    (byte*-p-of-tpm-identity-proof->conformance-credential
      (byte* conformance-credential)))

(cutil::defaggregate tpm-asym-ca-contents
  ( session-key
    id-digest)
:require
  ( (tpm-symmetric-key-p-of-tpm-asym-ca-contents->session-key
      (tpm-symmetric-key session-key))
    (tpm-digest-p-of-tpm-asym-ca-contents->id-digest
      (tpm-digest id-digest)))

(cutil::defaggregate tpm-sym-ca-attestation
  ( cred-size
    algorithm
    credential)
:require
  ( (uint32-p-of-tpm-sym-ca-attestation->cred-size
      (uint32 cred-size))
    (tpm-key-parms-p-of-tpm-sym-ca-attestation->algorithm
      (tpm-key-parms algorithm))
    (byte*-p-of-tpm-sym-ca-attestation->credential
      (byte* credential)))

(cutil::defaggregate tpm-transport-public
  ( tag
    trans-attributes
    alg-id
    enc-scheme)
:require
  ( (tpm-structure-tag-p-of-tpm-transport-public->tag
      (tpm-structure-tag tag))
    (tpm-transport-attributes-p-of-tpm-transport-public->trans-attributes
      (tpm-transport-attributes trans-attributes))
    (tpm-algorithm-id-p-of-tpm-transport-public->alg-id
      (tpm-algorithm-id alg-id))
    (tpm-enc-scheme-p-of-tpm-transport-public->enc-scheme
      (tpm-enc-scheme enc-scheme)))

(cutil::defaggregate tpm-transport-internal
  ( tag
    auth-data
    trans-public
    trans-handle
    trans-nonce-even
    trans-digest)
:require
  ( (tpm-structure-tag-p-of-tpm-transport-internal->tag
      (tpm-structure-tag tag))
    (tpm-authdata-p-of-tpm-transport-internal->auth-data
      (tpm-authdata auth-data))
    (tpm-transport-public-p-of-tpm-transport-internal->trans-public
      (tpm-transport-public trans-public))
    (tpm-transhandle-p-of-tpm-transport-internal->trans-handle
      (tpm-transhandle trans-handle))
    (tpm-nonce-p-of-tpm-transport-internal->trans-nonce-even
      (tpm-nonce trans-nonce-even))
    (tpm-digest-p-of-tpm-transport-internal->trans-digest
      (tpm-digest trans-digest)))

(cutil::defaggregate tpm-transport-log
  ( tag
    parameters
    pub-key-hash)
:require
  ( (tpm-structure-tag-p-of-tpm-transport-log->tag
      (tpm-structure-tag tag))
    (tpm-digest-p-of-tpm-transport-log->parameters
      (tpm-digest parameters))
    (tpm-digest-p-of-tpm-transport-log->pub-key-hash
      (tpm-digest pub-key-hash)))

(cutil::defaggregate tpm-transport-log-out
  ( tag
    current-ticks
    parameters
    locality)
:require
  ( (tpm-structure-tag-p-of-tpm-transport-log-out->tag
      (tpm-structure-tag tag))
    (tpm-current-ticks-p-of-tpm-transport-log-out->current-ticks
      (tpm-current-ticks current-ticks))
    (tpm-digest-p-of-tpm-transport-log-out->parameters
      (tpm-digest parameters))
    (tpm-modifier-indicator-p-of-tpm-transport-log-out->locality
      (tpm-modifier-indicator locality)))

(cutil::defaggregate tpm-transport-auth
  ( tag
    auth-data)
:require
  ( (tpm-structure-tag-p-of-tpm-transport-auth->tag
      (tpm-structure-tag tag))
    (tpm-authdata-p-of-tpm-transport-auth->auth-data
      (tpm-authdata auth-data)))

(cutil::defaggregate tpm-audit-event-in
  ( tag
    input-parms
    audit-count)
:require
  ( (tpm-structure-tag-p-of-tpm-audit-event-in->tag
      (tpm-structure-tag tag))
    (tpm-digest-p-of-tpm-audit-event-in->input-parms
      (tpm-digest input-parms))
    (tpm-counter-value-p-of-tpm-audit-event-in->audit-count
      (tpm-counter-value audit-count)))

(cutil::defaggregate tpm-audit-event-out
  ( tag
    output-parms
    audit-count)
:require
  ( (tpm-structure-tag-p-of-tpm-audit-event-out->tag
      (tpm-structure-tag tag))
    (tpm-digest-p-of-tpm-audit-event-out->output-parms
      (tpm-digest output-parms))
    (tpm-counter-value-p-of-tpm-audit-event-out->audit-count
      (tpm-counter-value audit-count)))

(cutil::defaggregate tpm-current-ticks
  ( tag
    current-ticks
    tick-rate
    tick-nonce)
:require
  ( (tpm-structure-tag-p-of-tpm-current-ticks->tag
      (tpm-structure-tag tag))
    (uint64-p-of-tpm-current-ticks->current-ticks
      (uint64 current-ticks))
    (uint16-p-of-tpm-current-ticks->tick-rate
      (uint16 tick-rate))
    (tpm-nonce-p-of-tpm-current-ticks->tick-nonce
      (tpm-nonce tick-nonce)))

(cutil::defaggregate tpm-context-blob
  ( tag
    resource-type
    handle
    label
    context-count
    integrity-digest
    additional-size
    additional-data
    sensitive-size
    sensitive-data)
:require
  ( (tpm-structure-tag-p-of-tpm-context-blob->tag
      (tpm-structure-tag tag))
    (tpm-resource-type-p-of-tpm-context-blob->resource-type
      (tpm-resource-type resource-type))
    (tpm-handle-p-of-tpm-context-blob->handle
      (tpm-handle handle))
    (byte[16]-p-of-tpm-context-blob->label
      (byte[16] label))
    (uint32-p-of-tpm-context-blob->context-count
      (uint32 context-count))
    (tpm-digest-p-of-tpm-context-blob->integrity-digest
      (tpm-digest integrity-digest))
    (uint32-p-of-tpm-context-blob->additional-size
      (uint32 additional-size))
    (byte*-p-of-tpm-context-blob->additional-data
      (byte* additional-data))
    (uint32-p-of-tpm-context-blob->sensitive-size
      (uint32 sensitive-size))
    (byte*-p-of-tpm-context-blob->sensitive-data
      (byte* sensitive-data)))

(cutil::defaggregate tpm-context-sensitive
  ( tag
    context-nonce
    internal-size
    internal-data)
:require
  ( (tpm-structure-tag-p-of-tpm-context-sensitive->tag
      (tpm-structure-tag tag))
    (tpm-nonce-p-of-tpm-context-sensitive->context-nonce
      (tpm-nonce context-nonce))
    (uint32-p-of-tpm-context-sensitive->internal-size
      (uint32 internal-size))
    (byte*-p-of-tpm-context-sensitive->internal-data
      (byte* internal-data)))

(cutil::defaggregate tpm-nv-data-public
  ( tag
    attributes)
:require
  ( (tpm-structure-tag-p-of-tpm-nv-data-public->tag
      (tpm-structure-tag tag))
    (uint32-p-of-tpm-nv-data-public->attributes
      (uint32 attributes)))

(cutil::defaggregate tpm-nv-data-sensitive
  ( tag
    pub-info
    auth-value
    data)
:require
  ( (tpm-structure-tag-p-of-tpm-nv-data-sensitive->tag
      (tpm-structure-tag tag))
    (tpm-nv-data-public-p-of-tpm-nv-data-sensitive->pub-info
      (tpm-nv-data-public pub-info))
    (tpm-authdata-p-of-tpm-nv-data-sensitive->auth-value
      (tpm-authdata auth-value))
    (byte*-p-of-tpm-nv-data-sensitive->data
      (byte* data)))

(cutil::defaggregate tpm-delegations
  ( tag
    delegate-type
    per1
    per2)
:require
  ( (tpm-structure-tag-p-of-tpm-delegations->tag
      (tpm-structure-tag tag))
    (uint32-p-of-tpm-delegations->delegate-type
      (uint32 delegate-type))
    (unit32-p-of-tpm-delegations->per1
      (unit32 per1))
    (uint32-p-of-tpm-delegations->per2
      (uint32 per2)))

(cutil::defaggregate tpm-family-label
  ( label)
:require
  ( (byte-p-of-tpm-family-label->label
      (byte label)))

(cutil::defaggregate tpm-family-table-entry
  ( tag
    family-label
    family-id
    verification-count
    flags)
:require
  ( (tpm-structure-tag-p-of-tpm-family-table-entry->tag
      (tpm-structure-tag tag))
    (tpm-family-label-p-of-tpm-family-table-entry->family-label
      (tpm-family-label family-label))
    (tpm-family-id-p-of-tpm-family-table-entry->family-id
      (tpm-family-id family-id))
    (tpm-family-verification-p-of-tpm-family-table-entry->verification-count
      (tpm-family-verification verification-count))
    (tpm-family-flags-p-of-tpm-family-table-entry->flags
      (tpm-family-flags flags)))

(cutil::defaggregate tpm-family-table
  ( fam-table-row)
:require
  ( (tpm-family-table-entry-p-of-tpm-family-table->fam-table-row
      (tpm-family-table-entry fam-table-row)))

(cutil::defaggregate tpm-delegate-label
  ( label)
:require
  ( (byte-p-of-tpm-delegate-label->label
      (byte label)))

(cutil::defaggregate tpm-delegate-public
  ( tag
    rowlabel
    pcr-info
    permissions
    family-id
    verification-count)
:require
  ( (tpm-structure-tag-p-of-tpm-delegate-public->tag
      (tpm-structure-tag tag))
    (tpm-delegate-label-p-of-tpm-delegate-public->rowlabel
      (tpm-delegate-label rowlabel))
    (tpm-pcr-info-short-p-of-tpm-delegate-public->pcr-info
      (tpm-pcr-info-short pcr-info))
    (tpm-delegations-p-of-tpm-delegate-public->permissions
      (tpm-delegations permissions))
    (tpm-family-id-p-of-tpm-delegate-public->family-id
      (tpm-family-id family-id))
    (tpm-family-verification-p-of-tpm-delegate-public->verification-count
      (tpm-family-verification verification-count)))

(cutil::defaggregate tpm-delegate-table-row
  ( tag
    pub
    auth-value)
:require
  ( (tpm-structure-tag-p-of-tpm-delegate-table-row->tag
      (tpm-structure-tag tag))
    (tpm-delegate-public-p-of-tpm-delegate-table-row->pub
      (tpm-delegate-public pub))
    (tpm-secret-p-of-tpm-delegate-table-row->auth-value
      (tpm-secret auth-value)))

(cutil::defaggregate tpm-delegate-table
  ( del-row)
:require
  ( (tpm-delegate-table-row-p-of-tpm-delegate-table->del-row
      (tpm-delegate-table-row del-row)))

(cutil::defaggregate tpm-delegate-sensitive
  ( tag
    auth-value)
:require
  ( (tpm-structure-tag-p-of-tpm-delegate-sensitive->tag
      (tpm-structure-tag tag))
    (tpm-secret-p-of-tpm-delegate-sensitive->auth-value
      (tpm-secret auth-value)))

(cutil::defaggregate tpm-delegate-owner-blob
  ( tag
    pub
    integrity-digest
    additional-size
    additional-area
    sensitive-size
    sensitive-area)
:require
  ( (tpm-structure-tag-p-of-tpm-delegate-owner-blob->tag
      (tpm-structure-tag tag))
    (tpm-delegate-public-p-of-tpm-delegate-owner-blob->pub
      (tpm-delegate-public pub))
    (tpm-digest-p-of-tpm-delegate-owner-blob->integrity-digest
      (tpm-digest integrity-digest))
    (uint32-p-of-tpm-delegate-owner-blob->additional-size
      (uint32 additional-size))
    (byte*-p-of-tpm-delegate-owner-blob->additional-area
      (byte* additional-area))
    (uint32-p-of-tpm-delegate-owner-blob->sensitive-size
      (uint32 sensitive-size))
    (byte*-p-of-tpm-delegate-owner-blob->sensitive-area
      (byte* sensitive-area)))

(cutil::defaggregate tpm-delegate-key-blob
  ( tag
    pub
    integrity-digest
    pub-key-digest
    additional-size
    additional-area
    sensitive-size
    sensitive-area)
:require
  ( (tpm-structure-tag-p-of-tpm-delegate-key-blob->tag
      (tpm-structure-tag tag))
    (tpm-delegate-public-p-of-tpm-delegate-key-blob->pub
      (tpm-delegate-public pub))
    (tpm-digest-p-of-tpm-delegate-key-blob->integrity-digest
      (tpm-digest integrity-digest))
    (tpm-digest-p-of-tpm-delegate-key-blob->pub-key-digest
      (tpm-digest pub-key-digest))
    (uint32-p-of-tpm-delegate-key-blob->additional-size
      (uint32 additional-size))
    (byte*-p-of-tpm-delegate-key-blob->additional-area
      (byte* additional-area))
    (uint32-p-of-tpm-delegate-key-blob->sensitive-size
      (uint32 sensitive-size))
    (byte*-p-of-tpm-delegate-key-blob->sensitive-area
      (byte* sensitive-area)))

(cutil::defaggregate tpm-cap-version-info
  ( tag
    version
    spec-level
    errata-rev
    tpm-vendor-id
    vendor-specific-size
    vendor-specific)
:require
  ( (tpm-structure-tag-p-of-tpm-cap-version-info->tag
      (tpm-structure-tag tag))
    (tpm-version-p-of-tpm-cap-version-info->version
      (tpm-version version))
    (uint16-p-of-tpm-cap-version-info->spec-level
      (uint16 spec-level))
    (byte-p-of-tpm-cap-version-info->errata-rev
      (byte errata-rev))
    (byte[4]-p-of-tpm-cap-version-info->tpm-vendor-id
      (byte[4] tpm-vendor-id))
    (uint16-p-of-tpm-cap-version-info->vendor-specific-size
      (uint16 vendor-specific-size))
    (byte*-p-of-tpm-cap-version-info->vendor-specific
      (byte* vendor-specific)))

(cutil::defaggregate tpm-da-info
  ( tag
    state
    current-count
    threshold-count
    action-at-threshold
    action-depend-value
    vendor-data-size
    vendor-data)
:require
  ( (tpm-structure-tag-p-of-tpm-da-info->tag
      (tpm-structure-tag tag))
    (tpm-da-state-p-of-tpm-da-info->state
      (tpm-da-state state))
    (uint16-p-of-tpm-da-info->current-count
      (uint16 current-count))
    (uint16-p-of-tpm-da-info->threshold-count
      (uint16 threshold-count))
    (tpm-da-action-type-p-of-tpm-da-info->action-at-threshold
      (tpm-da-action-type action-at-threshold))
    (uint32-p-of-tpm-da-info->action-depend-value
      (uint32 action-depend-value))
    (uint32-p-of-tpm-da-info->vendor-data-size
      (uint32 vendor-data-size))
    (byte*-p-of-tpm-da-info->vendor-data
      (byte* vendor-data)))

(cutil::defaggregate tpm-da-info-limited
  ( tag
    state
    current-count
    threshold-count
    action-at-threshold
    action-depend-value
    vendor-data-size
    vendor-data)
:require
  ( (tpm-structure-tag-p-of-tpm-da-info-limited->tag
      (tpm-structure-tag tag))
    (tpm-da-state-p-of-tpm-da-info-limited->state
      (tpm-da-state state))
    (uint16-p-of-tpm-da-info-limited->current-count
      (uint16 current-count))
    (uint16-p-of-tpm-da-info-limited->threshold-count
      (uint16 threshold-count))
    (tpm-da-action-type-p-of-tpm-da-info-limited->action-at-threshold
      (tpm-da-action-type action-at-threshold))
    (uint32-p-of-tpm-da-info-limited->action-depend-value
      (uint32 action-depend-value))
    (uint32-p-of-tpm-da-info-limited->vendor-data-size
      (uint32 vendor-data-size))
    (byte*-p-of-tpm-da-info-limited->vendor-data
      (byte* vendor-data)))

(cutil::defaggregate tpm-da-action-type
  ( tag
    actions)
:require
  ( (tpm-structure-tag-p-of-tpm-da-action-type->tag
      (tpm-structure-tag tag))
    (uint32-p-of-tpm-da-action-type->actions
      (uint32 actions)))

(cutil::defaggregate tpm-daa-issuer
  ( tag
    daa_digest_-r0
    daa_digest_-r1
    daa_digest_-s0
    daa_digest_-s1
    daa_digest_n
    daa_digest_gamma
    daa_)
:require
  ( (tpm-structure-tag-p-of-tpm-daa-issuer->tag
      (tpm-structure-tag tag))
    (tpm-digest-p-of-tpm-daa-issuer->daa_digest_-r0
      (tpm-digest daa_digest_-r0))
    (tpm-digest-p-of-tpm-daa-issuer->daa_digest_-r1
      (tpm-digest daa_digest_-r1))
    (tpm-digest-p-of-tpm-daa-issuer->daa_digest_-s0
      (tpm-digest daa_digest_-s0))
    (tpm-digest-p-of-tpm-daa-issuer->daa_digest_-s1
      (tpm-digest daa_digest_-s1))
    (tpm-digest-p-of-tpm-daa-issuer->daa_digest_n
      (tpm-digest daa_digest_n))
    (tpm-digest-p-of-tpm-daa-issuer->daa_digest_gamma
      (tpm-digest daa_digest_gamma))
    (byte[26]-p-of-tpm-daa-issuer->daa_
      (byte[26] daa_)))

(cutil::defaggregate tpm-daa-tpm
  ( tag
    daa_digest-issuer
    daa_digest_v0
    daa_digest_v1
    daa_rekey
    daa_count)
:require
  ( (tpm-structure-tag-p-of-tpm-daa-tpm->tag
      (tpm-structure-tag tag))
    (tpm-digest-p-of-tpm-daa-tpm->daa_digest-issuer
      (tpm-digest daa_digest-issuer))
    (tpm-digest-p-of-tpm-daa-tpm->daa_digest_v0
      (tpm-digest daa_digest_v0))
    (tpm-digest-p-of-tpm-daa-tpm->daa_digest_v1
      (tpm-digest daa_digest_v1))
    (tpm-digest-p-of-tpm-daa-tpm->daa_rekey
      (tpm-digest daa_rekey))
    (uint32-p-of-tpm-daa-tpm->daa_count
      (uint32 daa_count)))

(cutil::defaggregate tpm-daa-context
  ( tag
    daa_digest-context
    daa_digest
    daa_context-seed
    daa_scratch
    daa_stage)
:require
  ( (tpm-structure-tag-p-of-tpm-daa-context->tag
      (tpm-structure-tag tag))
    (tpm-digest-p-of-tpm-daa-context->daa_digest-context
      (tpm-digest daa_digest-context))
    (tpm-digest-p-of-tpm-daa-context->daa_digest
      (tpm-digest daa_digest))
    (tpm-daa-context-seed-p-of-tpm-daa-context->daa_context-seed
      (tpm-daa-context-seed daa_context-seed))
    (byte[256]-p-of-tpm-daa-context->daa_scratch
      (byte[256] daa_scratch))
    (byte-p-of-tpm-daa-context->daa_stage
      (byte daa_stage)))

(cutil::defaggregate tpm-daa-joindata
  ( daa_join_u0
    daa_join_u1
    daa_digest_n0)
:require
  ( (byte[128]-p-of-tpm-daa-joindata->daa_join_u0
      (byte[128] daa_join_u0))
    (byte[128]-p-of-tpm-daa-joindata->daa_join_u1
      (byte[128] daa_join_u1))
    (tpm-digest-p-of-tpm-daa-joindata->daa_digest_n0
      (tpm-digest daa_digest_n0)))

(cutil::defaggregate tpm-stany-data
  ( daa_issuer-settings
    daa_tpm-specific
    daa_session
    daa_join-session)
:require
  ( (tpm-daa-issuer-p-of-tpm-stany-data->daa_issuer-settings
      (tpm-daa-issuer daa_issuer-settings))
    (tpm-daa-tpm-p-of-tpm-stany-data->daa_tpm-specific
      (tpm-daa-tpm daa_tpm-specific))
    (tpm-daa-context-p-of-tpm-stany-data->daa_session
      (tpm-daa-context daa_session))
    (tpm-daa-joindata-p-of-tpm-stany-data->daa_join-session
      (tpm-daa-joindata daa_join-session)))

(cutil::defaggregate tpm-daa-blob
  ( tag
    resource-type
    label
    blob-integrity
    additional-size
    additional-data
    sensitive-size
    sensitive-data)
:require
  ( (tpm-structure-tag-p-of-tpm-daa-blob->tag
      (tpm-structure-tag tag))
    (tpm-resource-type-p-of-tpm-daa-blob->resource-type
      (tpm-resource-type resource-type))
    (byte[16]-p-of-tpm-daa-blob->label
      (byte[16] label))
    (tpm-digest-p-of-tpm-daa-blob->blob-integrity
      (tpm-digest blob-integrity))
    (uint32-p-of-tpm-daa-blob->additional-size
      (uint32 additional-size))
    (byte*-p-of-tpm-daa-blob->additional-data
      (byte* additional-data))
    (uint32-p-of-tpm-daa-blob->sensitive-size
      (uint32 sensitive-size))
    (byte*-p-of-tpm-daa-blob->sensitive-data
      (byte* sensitive-data)))

(cutil::defaggregate tpm-daa-sensitive
  ( tag
    internal-size
    internal-data)
:require
  ( (tpm-structure-tag-p-of-tpm-daa-sensitive->tag
      (tpm-structure-tag tag))
    (uint32-p-of-tpm-daa-sensitive->internal-size
      (uint32 internal-size))
    (byte*-p-of-tpm-daa-sensitive->internal-data
      (byte* internal-data)))
