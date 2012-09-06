(in-package "ACL2")

(defun sym-key-p (x)
  (declare (xargs :guard t))
  (integerp x))

(defun asym-key-p (x)
  (declare (xargs :guard t))
  (integerp x))

(defun auth-data-p (x)
  (declare (xargs :guard t))
  t)

(defrec wrap-key
  (wrapping-key ; parent key
   wrapped-key ; child, derived from parent
   auth-data))

(defun wrap-key-p (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (length x) 3)
       (asym-key-p (car x))
       (asym-key-p (cadr x))
       (auth-data-p (caddr x))))

