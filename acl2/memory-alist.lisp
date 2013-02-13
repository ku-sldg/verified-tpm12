(in-package "ACL2")

(include-book "cutil/defalist" :dir :system)
(include-book "misc/defun-plus" :dir :system)

(defn memory-val-p (x)
  (declare (ignore x))
  t)

(cutil::defalist memory-p (x)
  :key (natp x)
  :val (memory-val-p x)
  :keyp-of-nil nil
  :valp-of-nil t
  :true-listp t)

(defun+ empty-memory-p (mem)

; The use of this predicate is a little silly, but I'm using it in hopes that I
; can disable function empty-memory.

  (declare (xargs :guard (memory-p mem)))
  (null mem))

(defun+ empty-memory () ; initial empty memory
  (declare (xargs :guard t
                  :output (and (memory-p (empty-memory))
                               (empty-memory-p (empty-memory)))))
  nil)

(defun+ update-loc (i val mem)
  (declare (xargs :guard (and (memory-p mem)
                              (natp i)
                              (memory-val-p val))
                  :output (memory-p (update-loc i val mem))))
  (acons i val mem))

; I don't think having a lemma of empty_empty will help ACL2 solve any problems
; it couldn't solve before, so I'm leaving it out.

(defun+ lookup-loc (i mem)
  (declare (xargs :guard (and (memory-p mem)
                              (natp i))
                  :output (memory-val-p (lookup-loc i mem))))
  (let ((val (assoc-equal i mem)))
    (cond (val (cdr val))
          (t nil))))

(defthm read-of-write
  (equal (lookup-loc i (update-loc i val mem))
         val))

(defthm read-of-non-write
  (implies (not (equal i j))
           (equal (lookup-loc i (update-loc j val mem))
                  (lookup-loc i mem))))

(defthm write-of-write
  (equal (lookup-loc i (update-loc i val (update-loc i val2 mem)))
         (lookup-loc i (update-loc i val mem))))

(defthm read-of-empty-mem
  (implies (and (memory-p mem)
                (empty-memory-p mem))
           (equal (lookup-loc i mem)
                  nil)))

(in-theory (disable update-loc lookup-loc empty-memory-p empty-memory))