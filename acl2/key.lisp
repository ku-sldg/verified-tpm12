(in-package "ACL2")

(include-book "crypto")

(in-theory (disable asymmetric-key-p))

(defn blob-p (x)
  (declare (ignore x))
  t)

(defn keyset-p (keys)
  (cond ((atom keys)
         (null keys))
        (t 
         (and (asymmetric-key-p (car keys))
              (keyset-p (cdr keys))))))

(defthm keyset-p-implies-true-listp
  (implies (keyset-p lst)
           (true-listp lst)))
;  :rule-classes :type-prescription)

(defthm keyset-p-implies-car-asymmetric-key-p
  (implies (and (consp lst)
                (keyset-p lst))
           (asymmetric-key-p (car lst)))
  :rule-classes :type-prescription)

(defthm keyset-p-implies-member-asymmetric-key-p
  (implies (and (member x lst)
                (keyset-p lst))
           (asymmetric-key-p (car (member x lst)))))  

(defun check-key-root (wrap-key root-key)
  (declare (xargs :guard (and (wrap-key-p wrap-key)
                              (asymmetric-key-p root-key))))
  (equal (wrap-key->parent-key wrap-key)
         root-key))

(defun check-key (key root-key keyset)
  (declare (xargs :guard (and (asymmetric-key-p key)
                              (asymmetric-key-p root-key)
                              (keyset-p keyset))
                  :guard-hints (("Goal" :in-theory (enable asymmetric-key-p)))))
  (or (equal key root-key)
      (member key keyset)))

(defun+ add-key (wrap-key root-key keyset)
  (declare (xargs :guard (and (wrap-key-p wrap-key)
                              (asymmetric-key-p root-key)
                              (keyset-p keyset))
                  :output (keyset-p (add-key wrap-key root-key keyset))))
  (cond ((check-key (wrap-key->parent-key wrap-key) root-key keyset)
         (cons (wrap-key->derived-key wrap-key) keyset))
        (t
         keyset)))

(defun+ remove-key (wrap-key keyset)
  (declare (xargs :guard (and (wrap-key-p wrap-key)
                              (keyset-p keyset))
                  :output (keyset-p (remove-key wrap-key keyset))))

; This is silly to write, but I thought I'd point out that proving theorem
; revoke-key-state-preserves-tpm-state-p caught a bug here.  We used to have
; the bug that we were removing wrap-key, as opposed to the derived key that
; wrap-key contains.

  (remove-equal (wrap-key->derived-key wrap-key) keyset))

(defthm remove-key-lemma
  (implies (and (wrap-key-p wrap-key)
                (keyset-p keyset))
           (keyset-p (remove-key wrap-key keyset))))
(in-theory (disable remove-key))
