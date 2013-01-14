;; Shilpi Goel

(in-package "ACL2")

(include-book "misc/records" :dir :system)

(defun memp-aux (x)
  (declare (xargs :guard t))
  (cond ((atom x) (equal x nil))
        (t (and (consp (car x))
                (natp (caar x))
                (natp (cdar x))
                (memp-aux (cdr x))))))

(defun memp (x)
  (declare (xargs :guard t))
  (and (not (ifrp x))
       (rcdp x)
       (memp-aux x)))

(defun mem-get (i mem)
  (declare (xargs :guard (and (natp i)
                              (memp mem))))
  (or (g i mem) 0))

(defun mem-set (i v mem)
  (declare (xargs :guard (and (natp i)
                              (natp v)
                              (memp mem))))
  (s i v mem))

(defthm memp-g-aux-returns-a-natp
  (implies (and (memp x)
                (natp i)
                (g-aux i x))
           (natp (g-aux i x))))

(defthm memp-s-aux-returns-memp
  (implies (and (natp i)
                (natp v)
                (memp x))
           (memp (s-aux i v x))))

(defthm if-rcdp-then-acl2->rcd-is-identity
  (implies (not (ifrp x))
           (equal (acl2->rcd x) x))
  :hints (("Goal" :in-theory (e/d (acl2->rcd) ()))))

(defthm mem-get-returns-a-natp
  (implies (and (memp x)
                (natp i))
           (natp (mem-get i x)))
  :hints (("Goal" :expand (g i x))))

(defthm if-rcdp-then-rcd->acl2-is-identity
  (implies (not (ifrp x))
           (equal (rcd->acl2 x) x))
  :hints (("Goal" :in-theory (e/d (rcd->acl2) ()))))

(defthmd memp-s-aux-rcdp
  (implies (and (natp i)
                (natp v)
                (memp x))
           (rcdp (s-aux i v x)))
  :rule-classes :forward-chaining)

(defthmd memp-s-aux-not-ifrp
  (implies (and (natp i)
                (natp v)
                (memp x))
           (not (ifrp (s-aux i v x))))
  :rule-classes :forward-chaining)

(defthmd subgoal-1
  (implies (and (not (ifrp x))
                (rcdp x)
                (memp-aux x)
                (integerp i)
                (<= 0 i)
                (integerp v)
                (<= 0 v))
           (rcdp (rcd->acl2 (s-aux i v x))))
  :hints (("Goal" :use ((:instance memp-s-aux-not-ifrp)))))

(defthmd crock
  (implies (and (not (ifrp (s-aux i v x)))
                (not (ifrp x))
                (rcdp x)
                (memp-aux x)
                (integerp i)
                (<= 0 i)
                (integerp v)
                (<= 0 v))
           (memp-aux (s-aux i v x))))

(defthmd subgoal-2
  (implies (and (not (ifrp x))
                (rcdp x)
                (memp-aux x)
                (integerp i)
                (<= 0 i)
                (integerp v)
                (<= 0 v))
           (memp-aux (rcd->acl2 (s-aux i v x))))
  :hints (("Goal" :use ((:instance memp-s-aux-not-ifrp)
                        (:instance crock)))))

(defthm memp-s
  (implies (and (memp x)
                (natp i)
                (natp v))
           (memp (s i v x)))
  :hints (("Goal"
           :expand (s i v x))
          ("Subgoal 3"
           :use ((:instance if-rcdp-then-rcd->acl2-is-identity
                            (x (s-aux i v x)))
                 (:instance memp-s-aux-not-ifrp)))
          ("Subgoal 2" :use subgoal-2)
          ("Subgoal 1" :use subgoal-1))
  :otf-flg t)