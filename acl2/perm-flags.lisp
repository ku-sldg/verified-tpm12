(in-package "ACL2")

(cutil::defaggregate perm-flags

  (disable
   ownership
   deactivated
   read-pubek
   disable-owner-clear
   allow-maintenance
   physical-presence-lifetime-lock
   physical-presence-hw-enable
   physical-presence-cmd-enable
   cekp-used
   tpm-post
   tpm-post-lock
   fips
   operator
   enable-revoke-ek
   nv-locked
   read-srk-pub
   tpm-established
   maintenance-done
   disable-full-da-logic-info)

  :require
  ((tpm-state->disable-booleanp
    (booleanp disable))
   (tpm-state->ownership-booleanp
    (booleanp ownership))
   (tpm-state->deactivated-booleanp
    (booleanp deactivated))
   (tpm-state->read-pubek-booleanp
    (booleanp read-pubek))
   (tpm-state->disable-owner-clear-booleanp
    (booleanp disable-owner-clear))
   (tpm-state->allow-maintenance-booleanp
    (booleanp allow-maintenance))
   (tpm-state->physical-presence-lifetime-lock-booleanp
    (booleanp physical-presence-lifetime-lock))
   (tpm-state->physical-presence-hw-enable-booleanp
    (booleanp physical-presence-hw-enable))
   (tpm-state->physical-presence-cmd-enable-booleanp
    (booleanp physical-presence-cmd-enable))
   (tpm-state->cekp-used-booleanp
    (booleanp cekp-used))
   (tpm-state->tpm-post-booleanp
    (booleanp tpm-post))
   (tpm-state->tpm-post-lock-booleanp
    (booleanp tpm-post-lock))
   (tpm-state->fips-booleanp
    (booleanp fips))
   (tpm-state->operator-booleanp
    (booleanp operator))
   (tpm-state->enable-revoke-ek-booleanp
    (booleanp enable-revoke-ek))
   (tpm-state->nv-locked-booleanp
    (booleanp nv-locked))
   (tpm-state->read-srk-pub-booleanp
    (booleanp read-srk-pub))
   (tpm-state->tpm-established-booleanp
    (booleanp tpm-established))
   (tpm-state->maintenance-done-booleanp
    (booleanp maintenance-done))
   (tpm-state->disable-full-da-logic-info-booleanp
    (booleanp disable-full-da-logic-info)))
   :tag :perm-flags)

(defconst *perm-flags-init*
  (make-perm-flags
   :disable nil
   :ownership nil
   :deactivated nil
   :read-pubek nil
   :disable-owner-clear nil
   :allow-maintenance nil
   :physical-presence-lifetime-lock nil
   :physical-presence-hw-enable nil
   :physical-presence-cmd-enable nil
   :cekp-used nil
   :tpm-post nil
   :tpm-post-lock nil
   :fips nil
   :operator nil
   :enable-revoke-ek nil
   :nv-locked nil
   :read-srk-pub nil
   :tpm-established nil
   :maintenance-done nil
   :disable-full-da-logic-info nil))