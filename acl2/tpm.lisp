(in-package "ACL2")

; Some notes on ACL2 coding conventions:

; Typically Rager will simply append a "p" to the name of functions that he
; defines as predicates.  This makes the naming consistent with functions like
; "true-listp" and "subsetp".  However, to increase readability for code that
; has names stranger than "true-listp", ACL2 users will often include a hyphen
; before the "p".  In this project, we make such a decision, because we have
; things like "ek", and adding "ekp" should cause our minds to beg the question
; "what does the p stand for?"  To quell Rager's mind from asking this question
; (because it will more easily know the answer), we adopt the style of affixing
; a "-p" to the end of the name for predicate functions.

; An ACL2 style that is common among most ACL2 users is the use of the hyphen
; and typing with lower case letters.  For example, in Java, one would be
; tempted to call "pcrs-reset-senter-state" pcrsResetSenterState.  But, that's
; simply not the convention.  Also, noone uses underscores.  If one must use a
; space, then one could write |pcrs reset senter state|, however, the vertical
; bars are annoying and typically avoided.

(include-book "misc/assert" :dir :system)
(include-book "misc/defun-plus" :dir :system)
(include-book "cutil/defaggregate" :dir :system)

(defmacro why (rule)
  ;; Proof debugging tool.
  `(ACL2::er-progn
    (ACL2::brr t)
    (ACL2::monitor '(:rewrite ,rule) ''(:eval :go t))))

(include-book "pcr")
(include-book "crypto")
(include-book "key")
(include-book "perm-flags")
(include-book "perm-data")

(defn srk-p (srk)
  (asymmetric-key-p srk))

(defthm srk-p-implies-asymmetric-key-p
  (implies (srk-p key)
           (asymmetric-key-p key)))

(defn ek-p (ek)
  (asymmetric-key-p ek))

(defthm ek-p-implies-asymmetric-key-p
  (implies (ek-p key)
           (asymmetric-key-p key)))

(in-theory (disable srk-p ek-p))

#|
(defun key-p (key) 
  (declare (xargs :guard t))
  (integerp key))

(defun keys-p (keys)
  (declare (xargs :guard t))
  (cond ((atom keys)
         (null keys))
        (t (and (key-p (car keys))
                (keys-p (cdr keys))))))

(defthm keys-p-implies-true-listp
; requires induction, so we go ahead and write the lemma
  (implies (keys-p x) 
           (true-listp x)))
|#

(cutil::defaggregate restore-state-data
  (valid srk ek key-gen-count keys pcrs perm-flags perm-data)
  :require  ((booleanp-of-restore-state-data->valid
              (booleanp valid)
              :rule-classes :forward-chaining)
             (srk-p-of-restore-state-data->srk
              (srk-p srk)
              :rule-classes :forward-chaining)
             (ek-p-of-restore-state-data->ek
              (ek-p ek)
              :rule-classes :forward-chaining)
             (keyset-p-of-restore-state-data->keys
              (keyset-p keys)
              :rule-classes :forward-chaining)
             ;; TODO: add predicate about key-gen-count, but just saying K-p
             ;; seems weak
             (pcr-list-p-of-restore-state-data->pcrs
              (pcr-list-p pcrs)
              :rule-classes :forward-chaining)
             (perm-flags-p-of-restore-state-data->perm-flags
              (perm-flags-p perm-flags)
              :rule-classes :forward-chaining)
             (perm-data-p-of-restore-state-data->perm-data
              (perm-data-p perm-data)
              :rule-classes :forward-chaining))
  :tag :restore-state-data)

(defconst *pcrs-reset* nil)

(cutil::defaggregate tpm-state
  (restore memory post-init srk ek key-gen-count keys pcrs locality perm-flags perm-data disable-force-clear)
  :require ((restore-state-data-p-of-tpm-state->restore
             (restore-state-data-p restore)
             :rule-classes :forward-chaining)
            (true-listp-of-tpm-state->memory
             (true-listp memory)
             :rule-classes :forward-chaining
             )
            (booleanp-of-tpm-state->post-init
             (booleanp post-init)
             :rule-classes :forward-chaining
             )
            (srk-p-of-tpm-state->srk
             (srk-p srk)
             :rule-classes :forward-chaining
             )
            (ek-p-of-tpm-state->ek
             (ek-p ek)
             :rule-classes :forward-chaining
             )
            ;; TODO: make some statement about key-gen-count
            (keyset-p-of-tpm-state->keyset
             (keyset-p keys)
             :rule-classes :forward-chaining
             )
            (pcr-list-p-of-tpm-state->pcrs
             (pcr-list-p pcrs)
             :rule-classes :forward-chaining
             )
            (locality-p-of-tpm-state->locality
             (locality-p locality)
             :rule-classes :forward-chaining
             )
            (perm-data-p-of-tpm-state->perm-data
             (perm-data-p perm-data)
             :rule-classes :forward-chaining)

            (perm-flags-p-of-tpm-state->perm-flags
             (perm-flags-p perm-flags))

            (booleanp-of-tpm-state->disable-force-clear
             (booleanp disable-force-clear)
             :rule-classes :type-prescription))
  :tag :tpm-state)

(defthm tpm-state->locality-nat-p
  (implies (force (tpm-state-p x))
           (natp (tpm-state->locality x)))
  :rule-classes :type-prescription)

; locality < 5 as a linear rule

(defconst *default-srk* 1)
(defconst *default-ek* 1)
(defconst *default-keys* nil)
(defconst *default-pcrs* nil)
(defconst *default-perm-data* *perm-data-init*)
(defconst *default-perm-flags* *perm-flags-init*)

(defconst *default-restore-state-data*
  (make-restore-state-data
   :valid nil ; should maybe be t
   :srk *default-srk*
   :ek *default-ek*
   :keys *default-keys*
   :pcrs *default-pcrs*
   :perm-data *default-perm-data*
   :perm-flags *default-perm-flags*))

(defconst *tpm-post-init* 
  (make-tpm-state
        :restore *default-restore-state-data*
        :memory nil
        :post-init t
        :srk 1
        :ek 1
        :keys nil
        :pcrs nil
        :locality 4
        :perm-data *perm-data-init*
        :perm-flags *perm-flags-init*))

(assert! (tpm-state-p *tpm-post-init*))

; Example usage that accesses the mem field inside the variable tpm-s, which is
; of type tpm-state.

; (tpm-state->mem *tpm-post-init*)

; Example usage that changes the mem field inside the variable tpm-s, which is
; of type tpm-state.

; (change-tpm-state *tpm-post-init*
;         :memory '(1 2 3))

(defconst *tpm-startup*
  (make-tpm-state
        :restore *default-restore-state-data*
        :memory nil
        :post-init nil
        :srk 1
        :ek 1
        :keys nil
        :pcrs nil
        :locality 4
        :perm-data *perm-data-init*
        :perm-flags *perm-flags-init*))

(assert! (tpm-state-p *tpm-startup*))

(defun after-init-p (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)))
  (tpm-state->post-init tpm-s))

(defthm after-init-p-boolean-p
  (implies (tpm-state-p tpm-s)
           (booleanp (after-init-p tpm-s)))
  :rule-classes :type-prescription)

(defun after-startup-p (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)))
  (not (tpm-state->post-init tpm-s)))

; TODO: consider removing the "state" suffix from the following functions.  If
; Perry or someone else reads this, feel free to articulate the reason that
; "state" is a suffix and then remove this todo if I (Rager) was just missing
; something.

;(in-theory (enable tpm-state-p tpm-state->srk))

(defun+ pcrs-reset-senter-state (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)
                  :output (tpm-state-p (pcrs-reset-senter-state tpm-s))))
  (change-tpm-state tpm-s
                    :pcrs *pcrs-reset*))

(local
 (defthmd change-locality-state-lemma
   (implies (and (tpm-state-p tpm-s)
                 (< 0 (tpm-state->locality tpm-s)))
            (locality-p (1- (tpm-state->locality tpm-s))))
   :hints (("Goal" :use ((:instance locality-p-of-tpm-state->locality
                                    (x tpm-s)))
            :in-theory (e/d (locality-p) (locality-p-of-tpm-state->locality))))))

;; (local 
;;  (defthm change-locality-state-lemma-other-option
;;    (implies (and (tpm-state-p tpm-s)
;;                  (< 0 (tpm-state->locality tpm-s)))
;;             (<= (tpm-state->locality tpm-s)
;;                 5))
;;    :hints (("Goal" :use ((:instance locality-p-of-tpm-state->locality
;;                                     (x tpm-s)))
;;             :in-theory (e/d (locality-p) (locality-p-of-tpm-state->locality))))
;;    :rule-classes :linear))

;; "Hand" proof of change-locality-state-lemma2, based off of forward-chaining
;; (adding hypotheses until you get the conclusion).  ACL2 doesn't do this
;; forward-chaining on its own, so we added lemmas locality-p-implies-natp and
;; tpm-state->locality-nat-p.

;; (implies (tpm-state-p tpm-s)
;;          (rationalp (tpm-state->locality tpm-s)))

;; < locality-p-of-tpm-state->locality >

;; (implies (and (tpm-state-p tpm-s)
;;               (locality-p (tpm-state->locality tpm-s)))
;;          (rationalp (tpm-state->locality tpm-s)))

;; < definition of locality-p >

;; (implies (and (tpm-state-p tpm-s)
;;               (locality-p (tpm-state->locality tpm-s))
;;               (rationalp (tpm-state->locality tpm-s)))
;;          (rationalp (tpm-state->locality tpm-s)))

#|
(local
 (defthm change-locality-state-lemma2
   (implies (tpm-state-p tpm-s)
            (rationalp (tpm-state->locality tpm-s)))))
|#

(defun+ change-locality-state (tpm-s)

; Here is an example where our inability to restrict reasoning about the
; locality to be a natural number (as is done in tpm.pvs) bites us in the tail
; a bit.

  (declare (xargs :guard (tpm-state-p tpm-s)
                  :guard-hints (("Goal" :in-theory 
                                 (enable change-locality-state-lemma)))
                  :output (tpm-state-p (change-locality-state tpm-s))
                  :output-hints (("Goal" :in-theory 
                                  (enable change-locality-state-lemma)))))
  (let ((prev-locality (tpm-state->locality tpm-s)))
    (change-tpm-state tpm-s
                      :locality 
                      (if (> prev-locality 0)
                          (1- prev-locality)
                        prev-locality))))

(defun+ revoke-key-state (wrap-key tpm-s)
  (declare (xargs :guard (and (tpm-state-p tpm-s)
                              (wrap-key-p wrap-key))
                  :output (tpm-state-p (revoke-key-state wrap-key tpm-s))))
  (change-tpm-state tpm-s
          :keys (remove-key wrap-key
                            (tpm-state->keys tpm-s))))

(defthm revoke-key-state-preserves-tpm-state-p
  (implies (and (tpm-state-p tpm-s)
                (wrap-key-p wrap-key))
           (tpm-state-p (revoke-key-state wrap-key tpm-s))))

(defun+ load-key-to-state (wrap-key tpm-s)
  (declare (xargs :guard (and (tpm-state-p tpm-s)
                              (wrap-key-p wrap-key))
                  :output (tpm-state-p (load-key-to-state wrap-key tpm-s))))
  (change-tpm-state tpm-s
                    :keys (add-key wrap-key
                                   (tpm-state->srk tpm-s)
                                   (tpm-state->keys tpm-s))))

(defun+ extend-state (index hash-value tpm-s)
  (declare (xargs :guard (and (pcr-index-p index)
                              (valid-extension-value-p hash-value)
                              (tpm-state-p tpm-s))
                  :output (tpm-state-p (extend-state index hash-value
                                                     tpm-s))))
  (change-tpm-state tpm-s :pcrs
          (pcrs-extend (tpm-state->pcrs tpm-s)
                       index
                       hash-value)))

(defun+ activate-identity-state (wrap-key key tpm-s)

; The function in tpm.pvs accepts a third argument, called "key", which is of
; the type symKey.  We accept this third argument but ignore it for now.  In
; the long run, this argument should be either removed or used.

  (declare (xargs :guard (and (wrap-key-p wrap-key)
                              (tpm-state-p tpm-s))
                  :output (tpm-state-p (activate-identity-state wrap-key
                                                                free-var-key 
                                                                tpm-s)))
           (ignore key))
  (load-key-to-state wrap-key tpm-s))

(defun+ clear (tpm-s) ; not fully implemented
  (declare (xargs :guard (tpm-state-p tpm-s)
                  :output (tpm-state-p (clear tpm-s))))
  (change-tpm-state tpm-s :keys nil))

(defun+ owner-clear-state (auth tpm-s)
  (declare (xargs :guard (and (tpm-state-p tpm-s)
                              (asymmetric-key-p auth))
                  :output (tpm-state-p (owner-clear-state auth tpm-s))))
  (cond ((and (equal auth (compute-private-key-from-public-key 
                           (tpm-state->srk tpm-s)))
              (not (perm-flags->disable-owner-clear (tpm-state->perm-flags tpm-s))))
         (clear tpm-s))
        (t 
         tpm-s)))

(defun+ force-clear-state (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)
                  :output (tpm-state-p (force-clear-state tpm-s))))
  (cond ((tpm-state->disable-force-clear tpm-s)
         tpm-s)
        (t
         (clear tpm-s))))

(defun+ disable-owner-clear-state (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)
                  :output (tpm-state-p (disable-owner-clear-state tpm-s))))
  (change-tpm-state tpm-s :perm-flags
                    (change-perm-flags (tpm-state->perm-flags tpm-s)
                                       :disable-owner-clear
                                       t)))

(defun+ disable-force-clear-state (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)
                  :output (tpm-state-p (disable-force-clear-state tpm-s))))
  (change-tpm-state tpm-s :disable-force-clear t))

(defun+ save-state1 (keys ek srk key-gen-count pcrs perm-flags perm-data)

; Defined as saveState in startupData.pvs.

  (declare (xargs :guard (and (keyset-p keys)
                              (ek-p ek)
                              (srk-p srk)
                              (pcr-list-p pcrs)
                              (perm-flags-p perm-flags)
                              (perm-data-p perm-data))
                  :output (restore-state-data-p (save-state1 keys ek srk
                                                             key-gen-count pcrs 
                                                             perm-flags perm-data))))
  (make-restore-state-data
   :keys keys
   :ek ek
   :srk srk
   :key-gen-count key-gen-count
   :perm-flags perm-flags
   :perm-data perm-data
   :pcrs pcrs ; this used to be nil with a TODO, but I don't know why, so I'm changing it
   ))

(defun+ save-state (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)
                  :output (tpm-state-p (save-state tpm-s))))
  (change-tpm-state tpm-s :restore
                    (save-state1 (tpm-state->keys tpm-s)
                                 (tpm-state->ek tpm-s)
                                 (tpm-state->srk tpm-s)
                                 (tpm-state->key-gen-count tpm-s)
                                 (tpm-state->pcrs tpm-s)
                                 (tpm-state->perm-flags tpm-s)
                                 (tpm-state->perm-data tpm-s))))

