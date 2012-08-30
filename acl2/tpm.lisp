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

(include-book "pcr")

; potentially useful for proof debugging
(include-book "misc/untranslate-patterns" :dir :system)
(add-untranslate-pattern (cddddr (cddr ?x)) (asdf ?tpm-s))
(add-untranslate-pattern (cadddr (cdr tpm-s)) (keys tpm-s))

(defrec tpm-state
  (mem post-init srk ek keys pcrs locality)
  t)

(defun srk-p (srk)
  (declare (xargs :guard t))
  (declare (ignore srk))
  t
  ;(integerp srk)
  )
  

(defun ek-p (ek)
  (declare (xargs :guard t))
  (declare (ignore ek))
  ;(integerp ek)
  t)

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

(defconst *pcrs-reset* nil)

(defun locality-p (locality)
  (declare (xargs :guard t))
  (and (integerp locality)
       (<= locality 4)
       (>= locality 0)))

(defun tpm-state-p (tpm-s)
  (declare (xargs :guard t)) ; "type" predicate functions typically have a guard of t
  (and (true-listp tpm-s)
       (equal (length tpm-s) 7)
       (true-listp (access tpm-state tpm-s :mem))
       (booleanp (access tpm-state tpm-s :post-init))
       (srk-p (access tpm-state tpm-s :srk))
       (ek-p (access tpm-state tpm-s :ek))
       (keys-p (access tpm-state tpm-s :keys))
       (pcrs-p (access tpm-state tpm-s :pcrs))
       (locality-p (access tpm-state tpm-s :locality))))

(defconst *tpm-post-init* 
  (make tpm-state						
        :mem nil
        :post-init t
        :srk :srkval
        :ek :ekval
        :keys nil
        :pcrs nil
        :locality 4))

(assert! (tpm-state-p *tpm-post-init*))

; Example usage that accesses the mem field inside the variable tpm-s, which is
; of type tpm-state.

(access tpm-state *tpm-post-init* :mem)

; Example usage that changes the mem field inside the variable tpm-s, which is
; of type tpm-state.

(change tpm-state *tpm-post-init*
        :mem '(1 2 3))

(defconst *tpm-startup*
  (make tpm-state
        :mem nil
        :post-init nil
        :srk :srkval
        :ek :ekval
        :keys nil
        :pcrs nil
        :locality 4))

(assert! (tpm-state-p *tpm-startup*))

(defun after-init-p (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)))
  (access tpm-state tpm-s :post-init))

(defun after-startup-p (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)))
  (not (access tpm-state tpm-s :post-init)))

; TODO: consider removing the "state" suffix from the following functions.  If
; Perry or someone else reads this, feel free to articulate the reason that
; "state" is a suffix and then remove this todo if I (Rager) was just missing
; something.

(defun+ pcrs-reset-senter-state (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)
                  :output (tpm-state-p (pcrs-reset-senter-state tpm-s))))
  (change tpm-state tpm-s
          :pcrs *pcrs-reset*))

(defun+ change-locality-state (tpm-s)
  (declare (xargs :guard (tpm-state-p tpm-s)
                  :output (tpm-state-p (change-locality-state tpm-s))))
  (let ((prev-locality (access tpm-state tpm-s :locality)))
    (change tpm-state tpm-s
            :locality 
            (if (> prev-locality 0)
                (1- prev-locality)
              prev-locality))))

(defun+ remove-key (key keys)
  (declare (xargs :guard (and (key-p key)
                              (keys-p keys))
                  :output (keys-p (remove-key key keys))))
  (remove key keys))

(defun revoke-key-state (key tpm-s)
  (declare (xargs :guard (and (tpm-state-p tpm-s)
                              (key-p key))))
  (change tpm-state tpm-s
          :keys (remove-key key
                            (access tpm-state tpm-s
                                    :keys))))

(skip-proofs

; ACL2 should probably be able to prove this automatically, so there's a good
; chance there is a bug in remove-key or revoke-key-state.

 (defthm revoke-key-state-preserves-tpm-state-p

   (implies (and (tpm-state-p tpm-s)
                 (key-p key))
            (tpm-state-p (revoke-key-state key tpm-s)))))

(defun+ add-key (key keys)
  (declare (xargs :guard (and (key-p key)
                              (keys-p keys))
                  :output (keys-p (add-key key keys))))
  (cons key keys))

(defun+ load-key-to-state (key tpm-s)
  (declare (xargs :guard (and (tpm-state-p tpm-s)
                              (key-p key))
                  :output (tpm-state-p (load-key-to-state key tpm-s))))
  (change tpm-state tpm-s
          :keys (add-key key
                         (access tpm-state tpm-s :keys))))

(skip-proofs
 (defun+ extend-state (index hash-value tpm-s)

; TODO: ask Perry/Brigid whether this function should have a diff name

   (declare (xargs :guard (and (integerp index)
                               (hash-value-p hash-value)
                               (tpm-state-p tpm-s))
                   :output (tpm-state-p (extend-state index hash-value tpm-s))))
   (change tpm-state tpm-s :pcrs
           (pcrs-extend (access tpm-state tpm-s :pcrs)
                        index
                        hash-value))))


