(in-package "ACL2")

(include-book "cutil/deflist" :dir :system)
(include-book "cutil/defaggregate" :dir :system)
(include-book "cutil/defenum" :dir :system)

; ===============================================================
; primitive structures (integers and byte arrays)
; ===============================================================

(defn byte-p (x)
  (and (integerp x)
       (<= 0 x)
       (<= x 255)))

(defn uint16-p (x)
  (and (integerp x)
       (<= 0 x)
       (<= x (- (expt 2 16) 1))))

(defn uint32-p (x)
  (and (integerp x)
       (<= 0 x)
       (<= x (- (expt 2 32) 1))))

(cutil::deflist byte-list-p (x)
  (byte-p x)
  :elementp-of-nil nil
  :true-listp t)

(defn 4-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 4)))

(defn 16-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 16)))

(defn 20-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 20)))

(defn 26-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 26)))

(defn 128-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 128)))

(defn 256-byte-list-p (lst)
  (and (byte-list-p lst)
       (equal (len lst) 256)))
