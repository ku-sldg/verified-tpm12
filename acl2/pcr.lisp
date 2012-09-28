(in-package "ACL2")

(include-book "misc/defun-plus" :dir :system)
(include-book "cutil/defaggregate" :dir :system)

(defconst *pcr-count* 24)

(defconst *pcr-bit-length* 8) ; 32? 64? 256?

(defconst *max-pcr-value* (1- (expt 2 *pcr-bit-length*)))

(defnd locality-p (locality)
  (and (integerp locality)
       (<= locality 4)
       (>= locality 0)))

(defthm locality-p-implies-natp
  (implies (locality-p x)
           (and (natp x)
                (<= x 4)
                (>= x 0)))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable locality-p))))

(defn pcr-p (pcr)
  (and (integerp pcr)
       (<= -1 pcr)
       (<= pcr *max-pcr-value*)))

(defn reset-one () -1)

(defn reset-zero () 0)

(defn pcr-index-p (index)
 (and (integerp index)
      (<= 0 index)
      (< index *pcr-count*)))

(cutil::defaggregate pcr-flag
; resettable is called pcrReset in pcr.pvs, but the concept is really
; "resettable", so I name it as such here.
  (locality resettable)
  :require ((locality-p-of-pcr-flag->locality
             (locality-p locality))
            (boolean-p-of-pcr-flag->resettable
             (booleanp resettable)))
  :tag :pcr-flag)

(defn pcr-flags-p (flags)
; in the PVS model, pcv.pvs, PCRFLAGS is a type, where it is an array from an
; pcr-index to a pcr-flag.  Here, we make it a list, where the location in the
; list is the index.
  (cond ((atom flags)
         (null flags))
        (t (and (pcr-flag-p (car flags))
                (pcr-flags-p (cdr flags))))))

(defthm pcr-flags-p-implies-true-listp
  (implies (pcr-flags-p lst)
           (true-listp lst))
  :rule-classes :compound-recognizer)

(defthm pcr-flags-p-of-cons
  (implies (and (pcr-flags-p lst)
                (pcr-flag-p x))
           (pcr-flags-p (cons x lst))))

(defthm pcr-flags-p-recursive
  (implies (pcr-flags-p (cons x lst))
           (pcr-flags-p lst)))

(defthm pcr-flag-p-car-case
  (implies (pcr-flags-p (cons x lst))
           (pcr-flag-p x)))

(defthm pcr-flags-p-and-member-p-imply-pcr-flag-p
  (implies (and (member x lst)
                (pcr-flags-p lst))
           (pcr-flag-p x)))

(in-theory (disable pcr-flags-p))

(defn pcrs-p (pcrs)

; in the PVS model, pcv.pvs, PCRS is a type, where it is an array from a
; pcr-index to a pcr.  Here, we make it a list, where the location in the list
; is the index.

  (cond ((atom pcrs)
         (null pcrs))
        (t (and (pcr-p (car pcrs))
                (pcrs-p (cdr pcrs))))))

(defthm pcrs-p-implies-true-listp
  (implies (pcrs-p lst)
           (true-listp lst))
  :rule-classes :compound-recognizer)

(defthm pcrs-p-of-cons
  (implies (and (pcrs-p lst)
                (pcr-p x))
           (pcrs-p (cons x lst))))

(defthm pcr-p-of-car-pcrs
  (implies (and (consp lst)
                (pcrs-p lst))
           (pcr-p (car lst))))

(defthm pcr-p-and-member-p-imply-pcr-p
  (implies (and (member x lst)
                (pcrs-p lst))
           (pcr-p x)))

#|
(defthm pcrs-p-implies-true-listp
  (implies (pcrs-p x) (true-listp x))
  :rule-classes :forward-chaining)


(defthm pcr-p-of-member-pcrs
  (implies (and (member x lst)
                (pcrs-p lst))
           (pcr-p (car (member x lst))))
  :rule-classes (:rewrite :type-prescription)) ; type-presc is kind of silly
|#

(in-theory (disable pcrs-p))

(encapsulate

; Instead of declaring a variable pcrs-power of type pcr-p, as done in pcr.pvs
; (which is not really possible in ACL2), we define a function that returns the
; value for pcrs-power and prove that the function returns something of type
; pcr-p.  We then effectively throw away the definition and are left just with
; that theorem (implemented by the call of "encapsulate" and "local").

 (((pcrs-power) => *))
 (local (defun pcrs-power ()
          nil))
 (defthm pcrs-p-of-pcrs-power
   (pcrs-p (pcrs-power))
   :rule-classes (:rewrite :type-prescription)))

(defun+ pcrs-reset1 (flags)
  (declare (xargs :guard (pcr-flags-p flags)
;                  :guard-hints (("Goal" :in-theory (enable pcr-flags-p)))
                  :output (pcrs-p (pcrs-reset1 flags))
;                  :output-hints (("Goal" :in-theory (enable pcr-flags-p
;                                                            pcrs-p)))
                  ))
  (cond ((atom flags)
         nil)
        (t (cons (if (pcr-flag->resettable (car flags))
                     (reset-one)
                   (reset-zero))
                 (pcrs-reset1 (cdr flags))))))

(defun+ pcrs-reset (flags)
  (declare (xargs :guard (pcr-flags-p flags)
                  :output (pcrs-p (pcrs-reset flags))))
  


#|
(defun pcr-reset-ones-p (pcr)
  (declare (xargs :guard (pcr-p pcr)))
  ;(declare (xargs :guard t))
  (equal pcr *max-pcr-value*))

(defun pcr-reset-zeros-p (pcr)
  (declare (xargs :guard (pcr-p pcr)))
  ; maybe guard should be pcr-p
  (equal pcr 0))

(defun+ pcrs-reset-ones-p (pcrs)
  (declare (xargs :guard (pcrs-p pcrs)
                  :output (booleanp (pcrs-reset-ones-p pcrs))
                  ))
  (cond ((atom pcrs)
         t)
        (t (and (pcr-reset-ones-p (car pcrs))
                (pcrs-reset-ones-p (cdr pcrs))))))

(defun+ pcrs-reset-zeros-p (pcrs)
  (declare (xargs :guard (pcrs-p pcrs)
                  :output (booleanp (pcrs-reset-zeros-p pcrs))
                  ))
  (cond ((atom pcrs)
         t)
        (t (and (pcr-reset-zeros-p (car pcrs))
                (pcrs-reset-zeros-p (cdr pcrs))))))
|#

(defun valid-extension-value-p (val)
  (declare (xargs :guard t))
  (and (integerp val)
       (>= val 0)
       (< val (expt 2 *pcr-bit-length*))))

(local (include-book "arithmetic-5/top" :dir :system))

(defun+ extend (pcr value)
  (declare (xargs :guard (and (pcr-p pcr)
                              (valid-extension-value-p value))
                  :output (pcr-p (extend pcr value))
                  ))
  (mod (+ pcr value) (expt 2 *pcr-bit-length*)))




(defun+ pcrs-extend (pcrs index value)
  (declare (xargs :guard (and (pcrs-p pcrs)
                              (pcr-index-p index)
                              (valid-extension-value-p value))
                  :output (pcrs-p (pcrs-extend pcrs index value))))
  (cond ((atom pcrs)
         pcrs)
        ((equal index 0)
         (cons (extend (car pcrs) value)
               (cdr pcrs)))
        (t (cons (car pcrs)
                 (pcrs-extend (cdr pcrs) (1- index) value)))))

; TODO: define a predicate that includes integer-listp but also checks that it
; is of length <= *pcr-count* (or perhaps =).

(defun nat-listp (lst)
  (declare (xargs :guard t))
  (cond ((atom lst)
         (null lst))
        (t (and (natp (car lst))
                (nat-listp (cdr lst))))))
(defthm lemma
  (implies (and (pcrs-p pcrs)
                (natp n)
                (< n (length pcrs)))
           (pcr-p (nth n pcrs))))

(defun valid-pcr-mask-element (index length-pcrs)
; the current element/index in the pcr-mask is less than the length of the pcrs
  (declare (xargs :guard (natp length-pcrs)))
  (and (natp index)
       (< index length-pcrs)))

(defun valid-pcr-masks (pcr-masks length-pcrs)
; every element in the pcr-mask is less than the length of the pcrs
  (declare (xargs :guard (natp length-pcrs)))
  (cond ((atom pcr-masks)
         t)
        (t (and (valid-pcr-mask-element (car pcr-masks) length-pcrs)
                (valid-pcr-masks (cdr pcr-masks) length-pcrs)))))

(defun+ get-pcrs (pcrs pcr-masks)
  (declare (xargs :guard (and (pcrs-p pcrs)
                              (valid-pcr-masks pcr-masks (length pcrs)))
                  :output (pcrs-p (get-pcrs pcrs pcr-masks))
                  ))
  (cond ((atom pcr-masks)
         nil)
        (t (cons (nth (car pcr-masks) pcrs)
                 (get-pcrs pcrs (cdr pcr-masks))))))

(defthm get-pcrs-correctness
  (implies (member index pcr-mask)
           (member (nth index pcrs)
                   (get-pcrs pcrs pcr-mask))))

(local ; requires arithmetic-5
 (defthm extension-is-antisymmetric-lemma
   (implies (and (< a n)
                 (< b n)
                 (< 0 a)
                 (< 0 b)
                 (rationalp n)
                 (rationalp x)
                 (not (equal a b)))
            (not (equal (mod (+ x a) n)
                        (mod (+ x b) n))))))

(defthm extension-is-antisymmetric
  (implies (and (not (equal val1 val2))
                (pcr-p pcr)
                (valid-extension-value-p val1)
                (valid-extension-value-p val2))
           (not (equal (extend pcr val1)
                       (extend pcr val2)))))

(in-theory (disable extend)) ; will eventually disable many more functions