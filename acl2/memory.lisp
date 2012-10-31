; Rager would like to have a more records-based approach so that he can get the
; double-write theorem that records provie.  However, it's non-trivial
; (perhapss impossible) to prove that if update-loc is given a memory-p, that
; it will return a memory-p.  This is a property that Rager wants, so he's
; giving up on this file for now.

(in-package "ACL2")

(include-book "defexec/other-apps/records/records" :dir :system)

(include-book "cutil/defalist" :dir :system)
(include-book "misc/defun-plus" :dir :system)

(defn memory-val-p (x)
  (declare (ignore x))
  t)

;; (cutil::defalist memory-p1 (x)
;;   :key (natp x)
;;   :val (memory-val-p x)
;;   :keyp-of-nil nil
;;   :valp-of-nil t
;;   :true-listp t)

(defn memory-p1 (lst)
  (cond ((atom lst)
         (null lst))
        (t (and (consp (car lst))
                (natp (caar lst))
                (memory-val-p (cdar lst))
                (memory-p1 (cdr lst))))))

(defn memory-p (x)
  (and (memory-p1 x)
       (good-map x)))

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

(defun update-loc (i val mem)
  (declare (xargs :guard (and (memory-p mem)
                              (natp i)
                              (memory-val-p val))))      
  (mset i val mem))

;; (defthm subgoal-1-1
;;   (implies (good-map x)
;;            (equal (map->acl2 x)
;;                   x))
;;   :hints (("Goal" :in-theory (enable map->acl2))))

;; (defthm subgoal-1-1b
;;   (implies (good-map x)
;;            (equal (acl2->map x)
;;                   x))
;;   :hints (("Goal" :in-theory (enable acl2->map))))


;; (defthm subgoal-1
;;   (implies (and (integerp i) (<= 0 i))
;;            (memory-p1 (mset i val nil)))
;;   :hints (("Goal" :in-theory (enable mset))))

;; (defthm subgoal-3
;;   (implies (and (consp mem)
;;               (consp (car mem))
;;               (cdar mem)
;;               (not (cdr mem))
;;               (integerp (caar mem))
;;               (<= 0 (caar mem))
;;               (integerp i)
;;               (<= 0 i))
;;          (memory-p1 (mset i val mem)))
;;   :hints (("Goal" :in-theory (enable mset))))


;; (thm ; subgoal-5
;;   (implies (and (consp mem)
;;                 (consp (car mem))
;;                 (good-map (cdr mem))
;;                 (cdar mem)
;;                 (cdr mem)
;;                 (memory-p1 (mset i val (cdr mem)))
;;                 (integerp (caar mem))
;;                 (<= 0 (caar mem))
;;                 (memory-p1 (cdr mem))
;;                 (<< (caar mem) (caadr mem))
;;                 (integerp i)
;;                 (<= 0 i))
;;            (memory-p1 (mset i val mem)))
;;   :hints (("Goal" :in-theory (e/d (extend-records)
;;                                   ((ill-formed-key)
;;                                    ill-formed-key
;;                                    )))))


(in-theory (enable extend-records))

(defun+ update-loc (i val mem)
  (declare (xargs :guard (and (memory-p mem)
                              (natp i)
                              (memory-val-p val))
                  :output (memory-p (update-loc i val mem))))
  (mset i val mem))

(defun+ lookup-loc (i mem)
  (declare (xargs :guard (and (memory-p mem)
                              (natp i))
                  :output (memory-val-p (lookup-loc i mem))))
  (mget i mem))

(in-theory (disable extend-records))

(defthm read-of-write
  (equal (lookup-loc i (update-loc i val mem))
         val))

(defthm read-of-non-write
  (implies (not (equal i j))
           (equal (lookup-loc i (update-loc j val mem))
                  (lookup-loc i mem))))

(defthm write-of-write
  (equal (update-loc i val (update-loc i val2 mem))
         (update-loc i val mem)))


(defthm read-of-empty-mem
  (implies (empty-memory-p mem)
           (equal (lookup-loc i mem)
                  nil)))

(in-theory (disable update-loc lookup-loc empty-memory-p empty-memory))
