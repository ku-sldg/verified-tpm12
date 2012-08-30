(in-package "ACL2")

(defconst *pcr-count* 24)

(defconst *pcr-bit-length* 8) ; 32? 64? 256?

;; (defun pcr-key-p (pcr-key)
;;   (declare (xargs :guard t))
;;   (and (integerp pcr-key)
;;        (<= pcr-key (1- *pcr-count))))

;; (defun pcr-val-p (pcr-val)
;;   (declare (xargs :guard t))
;;   (integerp pcr-val))

;; (defun pcr-p (pcr)
;;   (declare (xargs :guard t))
;;   (and (consp pcr)
;;        (pcr-key-p (car pcr))
;;        (pcr-val-p (cdr pcr))))

(defun pcr-p (pcr)
  (declare (xargs :guard t))
  (integerp pcr))

(defun pcrs-p (pcrs)
  (declare (xargs :guard t))
  (cond ((atom pcrs)
         (null pcrs))
        (t (and (pcr-p (car pcrs))
                (pcrs-p (cdr pcrs))))))

(defthm pcrs-p-implies-true-listp
  (implies (pcrs-p x) (true-listp x)))

(defun nonce-p (nonce)
  (declare (xargs :guard t))
  (integerp nonce))

(defun hash-value-p (hv)
  (declare (xargs :guard t))
  (integerp hv))

(defun pcr-reset-ones-p (pcr)
  (declare (xargs :guard (pcr-p pcr)))
  ;(declare (xargs :guard t))
  (equal pcr (1- (expt 2 *pcr-bit-length*))))

(defun pcr-reset-zeros-p (pcr)
  (declare (xargs :guard (pcr-p pcr)))
  ; maybe guard should be pcr-p
  (equal pcr 0))

(defun+ pcrs-reset-ones-p (pcrs)
  (declare (xargs :guard (pcrs-p pcrs)
                  :output (booleanp (pcrs-reset-ones-p pcrs))))
  (cond ((atom pcrs)
         t)
        (t (and (pcr-reset-ones-p (car pcrs))
                (pcrs-reset-ones-p (cdr pcrs))))))

(defun+ pcrs-reset-zeros-p (pcrs)
  (declare (xargs :guard (pcrs-p pcrs)
                  :output (booleanp (pcrs-reset-zeros-p pcrs))))
  (cond ((atom pcrs)
         t)
        (t (and (pcr-reset-zeros-p (car pcrs))
                (pcrs-reset-zeros-p (cdr pcrs))))))

(defun valid-extension-value-p (val)
  (declare (xargs :guard t))
  (and (integerp val)
       (>= val 0)
       (<= val (expt 2 *pcr-bit-length*))))

(defun+ extend (pcr value)
  (declare (xargs :guard (and (pcr-p pcr)
                              (valid-extension-value-p value))
                  :output (pcr-p (extend pcr value))))
  (mod (+ pcr value) (expt 2 *pcr-bit-length*)))

(skip-proofs
 (defun+ pcrs-extend (pcrs index value)
   (declare (xargs :guard (and (integerp index)
                               (<= 0 index)
                               (< index *pcr-count*)
                               (hash-value-p value)
                               )
                   :output (pcrs-p (pcrs-extend pcrs index value))))
   (cond ((atom pcrs)
          pcrs)
         ((equal index 0)
          (cons (extend (car pcrs) value)
                (cdr pcrs)))
         (t (cons (car pcrs)
                  (pcrs-extend (cdr pcrs) (1- index) value))))))

; TODO: define a predicate that includes integer-listp but also checks that it
; is of length <= *pcr-count* (or perhaps =).

(skip-proofs
 (defun+ get-pcrs (pcrs pcr-mask)
   (declare (xargs :guard (and (pcrs-p pcrs)
                               (integer-listp pcr-mask))
                   :output (pcrs-p (get-pcrs pcrs pcr-mask))))
   (cond ((atom pcr-mask)
          nil)
         (t (cons (nth (car pcr-mask) pcrs)
                  (get-pcrs pcrs (cdr pcr-mask)))))))

(defthm get-pcrs-correctness
  (implies (member index pcr-mask)
           (member (nth index pcrs)
                   (get-pcrs pcrs pcr-mask))))

(defthm extension-is-antisymmetric1
  (implies (equal (extend pcr val1)
                  (extend pcr val2))
           (equal val1 val2)
           )
  :rule-classes nil)

(defthm extension-is-antisymmetric
  (implies (and (not (equal val1 val2))
                (pcr-p pcr))
           (not (equal (extend pcr val1)
                       (extend pcr val2)))))



(defun+ pcrs-extend (pcrs nonce hash-value)
  (declare (xargs :guard (and (nonce-p nonce)
                              (hash-value-p hash-value)
                              (tpm-state-p tpm-s))
                  :output (pcrs-p (pcrs-extend prcrs nonce hash-value))))
  

