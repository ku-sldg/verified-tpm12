(in-package "ACL2")

(include-book "misc/defun-plus" :dir :system)
(include-book "cutil/defaggregate" :dir :system)

; This library assumes that the user will only wish to model the encryption and
; decryption of integer lists.  

; Suppose instead that the user wished to model the encryption and decryption
; of lists of strings.  Instead of adding/subtracting a key to/from each
; element (which would not work for strings), the key could be cons'd onto each
; element.  Another alternative would be to explode the string into character
; atoms, explode the key into character atoms, append the resulting two lists
; together, and then turn the concatenated list into a string.  The
; possibilities are endless, but we focus on our present needs for now.

(defn encryptable-list-p (x)

; We could also call this "plaintext-p".

  (integer-listp x))

(defn decryptable-list-p (x)
  (integer-listp x))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;; symmetric encryption ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn symmetric-key-p (key)
  (integerp key))

(defun+ encrypt-symmetric-list (lst key)
  (declare (xargs :guard (and (symmetric-key-p key)
                              (encryptable-list-p lst))
                  :output (decryptable-list-p (encrypt-symmetric-list lst key))))
  (if (atom lst)
      nil
    (cons (+ (car lst) key)
          (encrypt-symmetric-list (cdr lst) key))))

(defun+ decrypt-symmetric-list (lst key)
  (declare (xargs :guard (and (symmetric-key-p key)
                              (decryptable-list-p lst))
                  :output (encryptable-list-p (decrypt-symmetric-list lst key))))
  (if (atom lst)
      nil
    (cons (- (car lst) key)
          (decrypt-symmetric-list (cdr lst) key))))

(defthm decrypt-of-encrypt-symmetric-equals-plaintext
  (implies (force (encryptable-list-p lst))
           (equal (decrypt-symmetric-list (encrypt-symmetric-list lst key)
                                          key)
                  lst)))
(defthm decrypt-of-encrypt-symmetric-needs-key
  (implies (and (encryptable-list-p lst)
                (not (null lst))
                (symmetric-key-p keyA)
                (symmetric-key-p keyB)
                (not (equal keyA keyB)))
           (not (equal (decrypt-symmetric-list (encrypt-symmetric-list lst keyA)
                                               keyB)
                       lst))))

(in-theory (disable symmetric-key-p encrypt-symmetric-list decrypt-symmetric-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; asymmetric encryption ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn asymmetric-key-p (key)
  (integerp key))

#|
(defthm asymmetric-key-p-implies-integer-p
  (implies (asymmetric-key-p key)
           (integerp key)))

(defthm asymmetric-key-p-implies-asymmetric-key-p-of-negative

; This is a bit ugly to have around, but it's necessary for now since we don't
; have a nicer story about 

  (implies (asymmetric-key-p key)
           (asymmetric-key-p (- key))))
|#

(defun+ compute-private-key-from-public-key (public-key)

; This is a terrible modeling choice in ACL2, but I'm just mimic'ing the PVS
; model (tpm.pvs) for now.

  (declare (xargs :guard (asymmetric-key-p public-key)
                  :output (asymmetric-key-p
                           (compute-private-key-from-public-key public-key))))
  (- public-key))


(defun public-private-key-pair-p (x y)
  (declare (xargs :guard (and (asymmetric-key-p x)
                              (asymmetric-key-p y))))
  (equal x (- y)))

(defun+ encrypt-asymmetric-list (lst key)
  (declare (xargs :guard (and (asymmetric-key-p key)
                              (encryptable-list-p lst))
                  :output (decryptable-list-p (encrypt-asymmetric-list lst key))))
  (if (atom lst)
      nil
    (cons (+ (car lst) key) ; maybe make operation * in future
          (encrypt-asymmetric-list (cdr lst) key))))

(defun+ decrypt-asymmetric-list (lst key)
  (declare (xargs :guard (and (asymmetric-key-p key)
                              (decryptable-list-p lst))
                  :output (encryptable-list-p (decrypt-asymmetric-list lst key))))
  (if (atom lst)
      nil
    (cons (+ (car lst) key)
          (decrypt-asymmetric-list (cdr lst) key))))

(defthm decrypt-of-encrypt-asymmetric-equals-plaintext
  (implies (and (encryptable-list-p lst)
                (public-private-key-pair-p key1 key2))
           (and (equal (decrypt-asymmetric-list
                        (encrypt-asymmetric-list lst key1)
                        key2)
                       lst)

; We happen to get this second property because of our implementation.
; Arguably, this could be either a bug or a feature of our implementation.
; But, at least we formally recognize this potential weakness.

; The fact that we've written both versions of this equality is similar to the
; double_private axiom found in key.pvs.

                (equal (decrypt-asymmetric-list 
                        (encrypt-asymmetric-list lst key2)
                        key1)
                       lst))))

(defthm decrypt-of-encrypt-asymmetric-needs-key
  (implies (and (encryptable-list-p lst)
                (not (null lst))
                (asymmetric-key-p keyA)
                (asymmetric-key-p keyB)
                (not (public-private-key-pair-p keyA keyB)))
           (not (equal (decrypt-asymmetric-list (encrypt-asymmetric-list lst keyA)
                                                keyB)
                       lst))))
(in-theory (disable asymmetric-key-p public-private-key-pair-p
                    encrypt-asymmetric-list decrypt-asymmetric-list))

(cutil::defaggregate wrap-key

; The "child-key" in key.pvs is called the derived-key here.

  (parent-key
   derived-key)
  :require ((wrap-key->parent-key-asymmetric-key-p 
             (asymmetric-key-p parent-key)
             :rule-classes :type-prescription)
            (wrap-key->derived-key-asymmetric-key-p 
             (asymmetric-key-p derived-key)
             :rule-classes :type-prescription))
  :tag :wrap-key)

;; (defn wrap-key-p (wkey)

;; ; Not modeling authdata yet

;;   (and (consp wkey)
;;        (asymmetric-key-p (car wkey))
;;        (asymmetric-key-p (cdr wkey))))

