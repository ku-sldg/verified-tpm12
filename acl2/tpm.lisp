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

; (include-book "tools/defconsts" :dir :system)
(include-book "misc/assert" :dir :system)
(include-book "misc/defun-plus" :dir :system)
(include-book "cutil/defaggregate" :dir :system)

(defmacro why (rule)
  ;; BOZO eventually improve this to handle other rule-classes and
  ;; such automatically.  That is, look up the name of the rule, etc.
  `(ACL2::er-progn
    (ACL2::brr t)
    (ACL2::monitor '(:rewrite ,rule) ''(:eval :go t))))

(include-book "pcr")
(include-book "crypto")
(include-book "key")
(include-book "perm-flags")

; potentially useful for proof debugging
;(include-book "misc/untranslate-patterns" :dir :system)

#|
(defrec tpm-state
  (mem post-init srk ek keys pcrs locality)
  t)

; Have ACL2 untranslate the following terms when it does printing, so that
; it's easier to read.
(add-untranslate-pattern (car tpm-s) (mem tpm-s))
(add-untranslate-pattern (car (cdr tpm-s)) (post-init tpm-s))
(add-untranslate-pattern (car (cdr (cdr tpm-s))) (srk tpm-s))
(add-untranslate-pattern (car (cdr (cdr (cdr tpm-s)))) (ek tpm-s))
(add-untranslate-pattern (car (cdr (cdr (cdr (cdr tpm-s))))) (keys tpm-s))
(add-untranslate-pattern (car (cdr (cdr (cdr (cdr (cdr tpm-s)))))) 
                         (pcrs tpm-s))
(add-untranslate-pattern (car (cdr (cdr (cdr (cdr (cdr (cdr tpm-s))))))) 
                         (locality tpm-s))
|#

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

(defconst *pcrs-reset* nil)

(defnd locality-p (locality)
  (and (integerp locality)
       (<= locality 4)
       (>= locality 0)))

(cutil::defaggregate tpm-state
  (mem post-init srk ek keys pcrs locality perm-flags perm-data disable-force-clear)
  :require ((tpm-state->mem-true-listp
             (true-listp mem)
;             :rule-classes :forward-chaining
             )
            (tpm-state->post-init-booleanp
             (booleanp post-init)
 ;            :rule-classes :forward-chaining
             )
            (tpm-state->srk-srk-p
             (srk-p srk)
  ;           :rule-classes :forward-chaining
             )
            (tpm-state->ek-ek-p
             (ek-p ek)
   ;          :rule-classes :forward-chaining
             )
            (tpm-state->keyset-keyset-p
             (keyset-p keys)
    ;         :rule-classes :forward-chaining
             )
            (tpm-state->pcrs-pcrs-p
             (pcrs-p pcrs)
     ;        :rule-classes :forward-chaining
             )
            (tpm-state->locality-locality-p
             (locality-p locality)
      ;       :rule-classes :forward-chaining
             )
            (tpm-state->perm-flags-perm-flags-p
             (perm-flags-p perm-flags))

            (tpm-state->disable-force-clear-booleanp
             (booleanp disable-force-clear)
             :rule-classes :type-prescription))
  :tag :tpm-state)

(defthm locality-p-implies-natp
  
; TODO: ask someone why this is needed for the proof of
; change-locality-state-lemma1.  Shouldn't tpm-state->locality-locality-p
; suffice?

  (implies (locality-p x)
           (and (natp x)
                (<= x 4)
                (>= x 0)))
            
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable locality-p))))

(defthm tpm-state->locality-nat-p
  (implies (force (tpm-state-p x))
           (natp (tpm-state->locality x)))
  :rule-classes :type-prescription)

; locality < 5 as a linear rule



; (why tpm-state->locality-locality-p)

;; (defun tpm-state-p (tpm-s)
;;   (declare (xargs :guard t)) ; "type" predicate functions typically have a guard of t
;;   (and (true-listp tpm-s)
;;        (equal (length tpm-s) 7)
;;        (true-listp (access tpm-state tpm-s :mem))
;;        (booleanp (access tpm-state tpm-s :post-init))
;;        (srk-p (access tpm-state tpm-s :srk))
;;        (ek-p (access tpm-state tpm-s :ek))
;;        (keyset-p (access tpm-state tpm-s :keys))
;;        (pcrs-p (access tpm-state tpm-s :pcrs))
;;        (locality-p (access tpm-state tpm-s :locality))))

(defconst *tpm-post-init* 
  (make-tpm-state						
        :mem nil
        :post-init t
        :srk 1
        :ek 1
        :keys nil
        :pcrs nil
        :locality 4
        :perm-flags *perm-flags-init*))

(assert! (tpm-state-p *tpm-post-init*))

; Example usage that accesses the mem field inside the variable tpm-s, which is
; of type tpm-state.

; (tpm-state->mem *tpm-post-init*)

; Example usage that changes the mem field inside the variable tpm-s, which is
; of type tpm-state.

; (change-tpm-state *tpm-post-init*
;         :mem '(1 2 3))

(defconst *tpm-startup*
  (make-tpm-state
        :mem nil
        :post-init nil
        :srk 1
        :ek 1
        :keys nil
        :pcrs nil
        :locality 4
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
   :hints (("Goal" :use ((:instance tpm-state->locality-locality-p
                                    (x tpm-s)))
            :in-theory (e/d (locality-p) (tpm-state->locality-locality-p))))))

;; (local 
;;  (defthm change-locality-state-lemma-other-option
;;    (implies (and (tpm-state-p tpm-s)
;;                  (< 0 (tpm-state->locality tpm-s)))
;;             (<= (tpm-state->locality tpm-s)
;;                 5))
;;    :hints (("Goal" :use ((:instance tpm-state->locality-locality-p
;;                                     (x tpm-s)))
;;             :in-theory (e/d (locality-p) (tpm-state->locality-locality-p))))
;;    :rule-classes :linear))

;; "Hand" proof of change-locality-state-lemma2, based off of forward-chaining
;; (adding hypotheses until you get the conclusion).  ACL2 doesn't do this
;; forward-chaining on its own, so we added lemmas locality-p-implies-natp and
;; tpm-state->locality-nat-p.

;; (implies (tpm-state-p tpm-s)
;;          (rationalp (tpm-state->locality tpm-s)))

;; < tpm-state->locality-locality-p >

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


#|
(defun+ owner-clear-state (auth tpm-s)
  (declare (xargs :guard (and (tpm-state-p tpm-s)
                              (asymmetric-key-p auth))
                  :output (tpm-state-p (owner-clear-state auth tpm-s))))
  (cond ((and (equal auth (compute-private-key-from-public-key 
                           (tpm-state->srk tpm-s)))
              (not *disable-owner-clear-flag*))
         (clear tpm-s))
        (t 
         tpm-s)))

(defun+ force-clear-state (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)
                  :output (tpm-state-p (force-clear-state tpm-s))))
  (cond (*disable-force-clear*
         tpm-s)
        (t
         tpm-s)))
|#
