(in-package "ACL2")

;(include-book "startup-data")
;(include-book "key")
(include-book "lib/defenum-plus")

(defenum+
  tpm-output-p
  (
   :nothing
   ;;(:error)
   ;;(:quote)
   ;;(:wrap-key)
   ;;(:asym-key)
   ;; (:sym-key)
   ;; (:blob)
   ;; (:cert-req)
   ;; (:identity)
   ;; (:ident-activation)
   ;; (:full-quote)
   ;; (:pcr)
   ))

(defun tpm-output->command (x)

; This definition could be part of defenum+ in the future.

  (declare (xargs :guard (tpm-output-p x)))
  (cond ((atom x)
         x)
        (t (car x))))

(defun tpm-output->arg1 (x)
  (declare (xargs :guard (tpm-output-p x)))
  (cond ((atom x)

; (er hard? ...) causes an error when run but logically returns nil

         (er hard? 'tpm-output->arg1 
             "tpm-output->arg1 ~x0 does not have an argument"
             x))
        ((atom (cdr x))
         (er hard? 'tpm-output->arg1 
             "tpm-output->arg1 ~x0 does not have an argument"
             x))
        (t (cadr x))))

(defun tpm-output->arg2 (x)
  (declare (xargs :guard (tpm-output-p x)))
  (cond ((atom x)

; (er hard? ...) causes an error when run but logically returns nil

         (er hard? 'tpm-output->arg2
             "tpm-output->arg2 ~x0 does not have a second argument"
             x))
        ((atom (cdr x))
         (er hard? 'tpm-output->arg2 
             "tpm-output->arg2 ~x0 does not have a second argument"
             x))
        ((atom (cddr x))
         (er hard? 'tpm-output->arg2
             "tpm-output->arg2 ~x0 does not have a second argument"
             x))
        (t (caddr x))))

(defun tpm-output->arg3 (x)
  (declare (xargs :guard (tpm-output-p x)))
  (cond ((atom x)

; (er hard? ...) causes an error when run but logically returns nil

         (er hard? 'tpm-output->arg3
             "tpm-output->arg3 ~x0 does not have a third argument"
             x))
        ((atom (cdr x))
         (er hard? 'tpm-output->arg3 
             "tpm-output->arg3 ~x0 does not have a third argument"
             x))
        ((atom (cddr x))
         (er hard? 'tpm-output->arg3
             "tpm-output->arg3 ~x0 does not have a third argument"
             x))
        ((atom (cdddr x))
         (er hard? 'tpm-output->arg3
             "tpm-output->arg3 ~x0 does not have a third argument"
             x))

        (t (cadddr x))))
