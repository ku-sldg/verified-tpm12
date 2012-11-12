(in-package "ACL2")

(include-book "cutil/defaggregate" :dir :system)

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
  ((booleanp-of-tpm-state->disable
    (booleanp disable))
   (booleanp-of-tpm-state->ownership
    (booleanp ownership))
   (booleanp-of-tpm-state->deactivated
    (booleanp deactivated))
   (booleanp-tpm-state->read-pubek
    (booleanp read-pubek))
   (booleanp-of-tpm-state->disable-owner-clear
    (booleanp disable-owner-clear))
   (booleanp-of-tpm-state->allow-maintenance
    (booleanp allow-maintenance))
   (booleanp-of-tpm-state->physical-presence-lifetime-lock
    (booleanp physical-presence-lifetime-lock))
   (booleanp-of-tpm-state->physical-presence-hw-enable
    (booleanp physical-presence-hw-enable))
   (booleanp-of-tpm-state->physical-presence-cmd-enable
    (booleanp physical-presence-cmd-enable))
   (booleanp-of-tpm-state->cekp-used
    (booleanp cekp-used))
   (booleanp-of-tpm-state->tpm-post
    (booleanp tpm-post))
   (booleanp-of-tpm-state->tpm-post-lock
    (booleanp tpm-post-lock))
   (booleanp-of-tpm-state->fips
    (booleanp fips))
   (booleanp-of-tpm-state->operator
    (booleanp operator))
   (booleanp-of-tpm-state->enable-revoke-ek
    (booleanp enable-revoke-ek))
   (booleanp-of-tpm-state->nv-locked
    (booleanp nv-locked))
   (booleanp-of-tpm-state->read-srk-pub
    (booleanp read-srk-pub))
   (booleanp-of-tpm-state->tpm-established
    (booleanp tpm-established))
   (booleanp-of-tpm-state->maintenance-done
    (booleanp maintenance-done))
   (booleanp-of-tpm-state->disable-full-da-logic-info
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