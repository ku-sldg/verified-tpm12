(in-package "ACL2")

(include-book "misc/defun-plus" :dir :system)
(include-book "cutil/defaggregate" :dir :system)
(include-book "cutil/deflist" :dir :system)

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

;(IMPLIES (AND X Y (BOOLEANP X) (BOOLEANP Y))
;         (EQUAL X Y))

(defn pcr-index-p (index)
 (and (integerp index)
      (<= 0 index)
      (< index *pcr-count*)))

(defthm nat-p-of-pcr-index-p
  (implies (pcr-index-p x)
           (natp x))
  :rule-classes :compound-recognizer)

(cutil::deflist pcr-index-list-p (x)
  (pcr-index-p x)
  :elementp-of-nil nil
  :true-listp t)

(cutil::defaggregate pcr-flag
; resettable is called pcrReset in pcr.pvs, but the concept is really
; "resettable", so I name it as such here.
  (locality resettable)
  :require ((locality-p-of-pcr-flag->locality
             (locality-p locality))
            (boolean-p-of-pcr-flag->resettable
             (booleanp resettable)))
  :tag :pcr-flag)

(cutil::deflist pcr-flag-list-p (x)
  (pcr-flag-p x)
  :elementp-of-nil nil
  :true-listp t)

;; (defthm pcr-flag-list-p-implies-true-listp
;;   (implies (pcr-flag-list-p lst)
;;            (true-listp lst))
;;   :rule-classes :compound-recognizer
;;   :hints (("Goal" :in-theory (enable pcr-flag-list-p))))


;; (defn pcr-flags-p (flags)
;; ; in the PVS model, pcv.pvs, PCRFLAGS is a type, where it is an array from an
;; ; pcr-index to a pcr-flag.  Here, we make it a list, where the location in the
;; ; list is the index.
;;   (cond ((atom flags)
;;          (null flags))
;;         (t (and (pcr-flag-p (car flags))
;;                 (pcr-flags-p (cdr flags))))))

;; (defthm pcr-flags-p-implies-true-listp
;;   (implies (pcr-flags-p lst)
;;            (true-listp lst))
;;   :rule-classes :compound-recognizer)

;; #|
;; (defthm pcr-flags-p-of-cons
;;   (implies (and (pcr-flags-p lst)
;;                 (pcr-flag-p x))
;;            (pcr-flags-p (cons x lst))))

;; (defthm pcr-flags-p-recursive
;;   (implies (pcr-flags-p (cons x lst))
;;            (pcr-flags-p lst)))

;; (defthm pcr-flag-p-car-case
;;   (implies (pcr-flags-p (cons x lst))
;;            (pcr-flag-p x)))
;; |#

;; (defthm pcr-flag-constructors
;;   (equal (pcr-flags-p (cons e lst))
;;          (and (pcr-flag-p e)
;;               (pcr-flags-p lst))))

;; (defthm pcr-flags-p-and-member-p-imply-pcr-flag-p
;;   (implies (and (member x lst)
;;                 (pcr-flags-p lst))
;;            (pcr-flag-p x)))


;(in-theory (disable pcr-flags-p))

(cutil::deflist pcr-list-p (x)
  (pcr-p x)
  :elementp-of-nil nil
  :true-listp t)

;; (defthm pcr-list-p-implies-true-listp
;;   (implies (pcr-list-p lst)
;;            (true-listp lst))
;;   :rule-classes :compound-recognizer)

;; (defn pcrs-p (pcrs)

;; ; in the PVS model, pcv.pvs, PCRS is a type, where it is an array from a
;; ; pcr-index to a pcr.  Here, we make it a list, where the location in the list
;; ; is the index.

;;   (cond ((atom pcrs)
;;          (null pcrs))
;;         (t (and (pcr-p (car pcrs))
;;                 (pcrs-p (cdr pcrs))))))

;; (defthm pcrs-p-implies-true-listp
;;   (implies (pcrs-p lst)
;;            (true-listp lst))
;;   :rule-classes :compound-recognizer)

;; #|
;; (defthm pcrs-p-of-cons
;;   (implies (and (pcrs-p lst)
;;                 (pcr-p x))
;;            (pcrs-p (cons x lst))))

;; (defthm pcr-p-of-car-pcrs
;;   (implies (and (consp lst)
;;                 (pcrs-p lst))
;;            (pcr-p (car lst))))

;; (defthm pcr-p-and-member-p-imply-pcr-p
;;   (implies (and (member x lst)
;;                 (pcrs-p lst))
;;            (pcr-p x)))


;; (defthm pcrs-p-implies-true-listp
;;   (implies (pcrs-p x) (true-listp x))
;;   :rule-classes :forward-chaining)


;; (defthm pcr-p-of-member-pcrs
;;   (implies (and (member x lst)
;;                 (pcrs-p lst))
;;            (pcr-p (car (member x lst))))
;;   :rule-classes (:rewrite :type-prescription)) ; type-presc is kind of silly
;; |#

;; (in-theory (disable pcrs-p))

(encapsulate

; Instead of declaring a variable pcrs-power of type pcr-p, as done in pcr.pvs
; (which is not really possible in ACL2), we define a function that returns the
; value for pcrs-power and prove that the function returns something of type
; pcr-p.  We then effectively throw away the definition and are left just with
; that theorem (implemented by the call of "encapsulate" and "local").

 (((pcrs-power) => *))
 (local (defun pcrs-power ()
          nil))
 (defthm pcr-list-p-of-pcrs-power
   (pcr-list-p (pcrs-power))
   :rule-classes (:rewrite :type-prescription)))

;; (defun+ pcrs-reset1 (flags)
;;   (declare (xargs :guard (pcr-flag-list-p flags)
;;                   :output (pcr-list-p (pcrs-reset1 flags))
;;                   ))
;;   (cond ((atom flags)
;;          nil)
;;         (t (cons (if (pcr-flag->resettable (car flags))
;;                      (reset-one)
;;                    (reset-zero))
;;                  (pcrs-reset1 (cdr flags))))))

(defun+ pcr-reset (flag)
  (declare (xargs :guard (pcr-flag-p flag)
                  :output (pcr-p (pcr-reset flag))))
  (if (pcr-flag->resettable flag)
      (reset-one)
    (reset-zero)))

(defun+ pcr-senter (pcr flag)
  (declare (xargs :guard (and (pcr-flag-p flag)
                              (pcr-p pcr))
                  :output (pcr-p (pcr-senter pcr flag))))
  (if (pcr-flag->resettable flag)
      (reset-zero)
    pcr))

;; (defthm pcr-flag-p-of-nth-pcr-flag-list
;;   (implies (and (pcr-flag-list-p flags)
;;                 (natp n)
;;                 (< n (len flags))
;;                 )
;;            (pcr-flag-p (nth n flags))))

;; (defthm pcrs-reset-lemma
;;   (implies (and (pcr-index-p n)
;;                 (pcr-list-p pcrs)
;;                 (< n (len pcrs))
;;                 (pcr-p v))
;;            (pcr-list-p (update-nth n v pcrs))))

(defn all-pcr-indexes-are-within-range (indexes lst-len)
  (declare (xargs :guard (and (pcr-index-list-p indexes)
                              (integerp lst-len))))
  (cond ((atom indexes)
         t)
        (t (and (< (car indexes) lst-len)
                (all-pcr-indexes-are-within-range (cdr indexes) lst-len)))))

;; (defthm pcr-flag-p-of-nth-of-pcr-flag-list
;;   (implies (and (pcr-flag-list-p flags)
;;                 (natp n)
;;                 (< n (len flags)))
;;            (equal (pcr-flag-p (nth n flags))
;;                   t)))

;; (defthm pcr-p-of-nth-of-pcr-list
;;   (implies (and (pcr-list-p pcrs)
;;                 (natp n)
;;                 (< n (len pcrs)))
;;            (equal (pcr-p (nth n pcrs))
;;                   t)))



;; (defthm ahcak
;;   (implies (and (all-pcr-indexes-are-within-range indexes (len pcr-flags))
;;                 (pcr-flag-p pcr-flags)
;;                 (pcr-index-list-p indexes)
;;                 )
;;            (pcr-flag-p (nth (car indexes) pcr-flags))))

;; (defthm pcrs-reset-hack
;;   (implies (and (pcr-index-list-p indexes)
;;                 (consp indexes)
;;                 (consp (cdr indexes)))
;;            (pcr-index-p (cadr indexes)))
;;   :rule-classes :forward-chaining)

;; (defthm pcrs-reset-hack3
;;   (implies (and (pcr-index-p index)
;;                 (pcr-flag-list-p flags)
;;                 (nth index flags))
;;            (pcr-flag-p (nth index flags))))
                
(defun induction-hint (n val lst)
  (declare (ignorable val))
  (cond ((zp n)
         lst)
        (t (induction-hint (1- n) val (cdr lst)))))

(defthm pcr-list-p-of-update-nth
  (implies (and (pcr-list-p pcrs)
                (pcr-p pcr)
                (< n (len pcrs)))
           (pcr-list-p (update-nth n pcr pcrs)))
  :hints (("Goal" :in-theory (e/d (pcr-list-p) (pcr-p))
           :induct (induction-hint n pcr pcrs))
          ("Subgoal *1/2'" :expand (update-nth n pcr pcrs))))

(defun+ pcrs-reset (pcrs flags indexes)
  (declare (xargs :guard (and (true-listp pcrs)
                              (true-listp flags)
                              (true-listp indexes)
                              (pcr-list-p pcrs)
                              (pcr-flag-list-p flags)
                              (pcr-index-list-p indexes)
                              (all-pcr-indexes-are-within-range indexes 
                                                                (len flags))
                              (all-pcr-indexes-are-within-range indexes 
                                                                (len pcrs)))
                  :output (pcr-list-p (pcrs-reset pcrs flags indexes))))
  (cond ((atom indexes)
         pcrs)
        (t (let* ((index (car indexes))
                  (pcr-flag (nth index flags))
                  (new-pcr (pcr-reset pcr-flag)))
             (pcrs-reset (update-nth index
                                     new-pcr
                                     pcrs)
                         flags
                         (cdr indexes))))))

(defun+ pcrs-senter (pcrs flags indexes)
  (declare (xargs :guard (and (true-listp pcrs)
                              (true-listp flags)
                              (true-listp indexes)
                              (pcr-list-p pcrs)
                              (pcr-flag-list-p flags)
                              (pcr-index-list-p indexes)
                              (all-pcr-indexes-are-within-range indexes 
                                                                (len flags))
                              (all-pcr-indexes-are-within-range indexes 
                                                                (len pcrs)))
                  :guard-hints (("Goal" :in-theory (disable pcr-p)))
                  :output (pcr-list-p (pcrs-senter pcrs flags indexes))))
  (cond ((atom indexes)
         pcrs)
        (t (let* ((index (car indexes))
                  (pcr-flag (nth index flags))
                  (curr-pcr (nth index pcrs))
                  (new-pcr (pcr-senter curr-pcr pcr-flag)))
             (pcrs-senter (update-nth index
                                      new-pcr
                                      pcrs)
                          flags
                          (cdr indexes))))))

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

(defun all-reset-access (count)
; Return a list of pcr-flags where each flag has pcr-reset set to true and a
; locality of 0.
  (declare (xargs :guard (natp count)))
  (cond  ((zp count)
          nil)
         (t (cons (make-pcr-flag :resettable t
                                 :locality 0)
                  (all-reset-access (1- count))))))

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
  (declare (xargs :guard (and (pcr-list-p pcrs)
                              (pcr-index-p index)
                              (valid-extension-value-p value))
                  :output (pcr-list-p (pcrs-extend pcrs index value))))
  (cond ((atom pcrs)
         pcrs)
        ((equal index 0)
         (cons (extend (car pcrs) value)
               (cdr pcrs)))
        (t (cons (car pcrs)
                 (pcrs-extend (cdr pcrs) (1- index) value)))))

(in-theory (disable extend (extend))) ; will eventually disable many more functions


; TODO: define a predicate that includes integer-listp but also checks that it
; is of length <= *pcr-count* (or perhaps =).

(cutil::deflist nat-list-p (x)
  (natp x)
  :elementp-of-nil nil
  :true-listp t)

; TODO: remove this lemma since it should be part of deflist now

(defthm pcr-p-of-nth-of-pcr-list-p
  (implies (and (pcr-list-p pcrs)
                (natp n)
                (< n (len pcrs)))
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
  (declare (xargs :guard (and (pcr-list-p pcrs)
                              (valid-pcr-masks pcr-masks (len pcrs)))
                  :output (pcr-list-p (get-pcrs pcrs pcr-masks))
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
                       (extend pcr val2))))
  :hints (("Goal" :in-theory (enable extend))))
