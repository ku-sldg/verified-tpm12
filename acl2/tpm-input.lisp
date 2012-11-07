(in-package "ACL2")

(include-book "startup-data")
(include-book "key")
(include-book "lib/defenum-plus")

;; (defn unimp0 ()
;;   t)

;; (defn unimp1 (x)
;;   (declare (ignore x))
;;   t)

;; (defn unimp2 (x y)
;;   (declare (ignore x y))
;;   t)

;; (defn unimp3 (x y z)
;;   (declare (ignore x y z))
;;   t)

;; (defn tpm-input-guard (cmd x y z)
;;   (case cmd
;;     (:abs-reset
;;      (unimp0))
;;     (:abs-init
;;      (unimp0))
;;     (:abs-save-state
;;      (unimp0))
;;     (:abs-startup
;;      (tpm-startup-type x))
;;     (t 
;;      (er hard? 'tpm-input-guard
;;          "TPM-INPUT-GUARD given argumens of ~x0, ~x1, ~x2, and ~x3"
;;          cmd x y z))))

;; (defun step-tpm-input (cmd x y z)
;;   (declare (xargs :guard (tpm-input-guard cmd x y z)))
;;   (case cmd
;;     (:abs-startup
;;      (case x
;;        (:tpm-st-clear
;;         (tpm-startup))
;;        (:tpm-st-state
;;         (restore-state


(defenum+
  tpm-input-p
  (
    ;; startup commands
    :reset
    :init
    :save-state
    (:startup tpm-startup-type) ; defined in startup-data.lisp
    ;; protected storage commands
    (:seal asymmetric-key-p blob-p)
    ;; (:unseal)
    ;; (:unbind)
    ;; (:create-wrap-key)
    ;; key management commands

; We can observe a key difference between the PVS model and the ACL2 model by
; looking at the declaration of load-key-2.  In the PVS model, we must declare
; a return type for the monad.  However, in ACL2, we "get" to skip that syntax.
; If it turns out we need it, we can make the input signature a list and then
; also add a list that represents the output signature (to the syntax of
; defenum+).

    (:load-key-2 wrap-key-p)
    ;; measurement collection commands
    ;; (:extend)
    ;; measurement reporting commands
    ;; (:pcr-read)
    ;; (:quote)
    ;; AIK commands
    ;; (:make-identity)
    ;; (:activate-identity)
    ;; cryptographic commands
    ;; (:sign)
    ;; TPM ownership commands
    ;; (:take-ownership)
    ;; operational flags commands
    ;; (:owner-clear)
    ;; (:force-clear)
    ;; (:disable-owner-clear)
    ;; (:disable-force-clear)
    ;; software commands
    ;; (:senter)
    ;; (:sinit)
    ;; (:save)
    (:read natp)
    ;; (:data-bind)
    ;; ca commands
    ;; (:certify)
    ;; invented, imaginary commands
    ;; (:noop-com)
    ))

(defun tpm-input->command (x)

; This definition could be part of defenum+ in the future.

  (declare (xargs :guard (tpm-input-p x)))
  (cond ((atom x)
         x)
        (t (car x))))

(defun tpm-input->arg1 (x)
  (declare (xargs :guard (tpm-input-p x)))
  (cond ((atom x)

; (er hard? ...) causes an error when run but logically returns nil

         (er hard? 'tpm-input->arg1 
             "tpm-input->arg1 ~x0 does not have an argument"
             x))
        ((atom (cdr x))
         (er hard? 'tpm-input->arg1 
             "tpm-input->arg1 ~x0 does not have an argument"
             x))
        (t (cadr x))))

(defun tpm-input->arg2 (x)
  (declare (xargs :guard (tpm-input-p x)))
  (cond ((atom x)

; (er hard? ...) causes an error when run but logically returns nil

         (er hard? 'tpm-input->arg2
             "tpm-input->arg2 ~x0 does not have a second argument"
             x))
        ((atom (cdr x))
         (er hard? 'tpm-input->arg2 
             "tpm-input->arg2 ~x0 does not have a second argument"
             x))
        ((atom (cddr x))
         (er hard? 'tpm-input->arg2
             "tpm-input->arg2 ~x0 does not have a second argument"
             x))
        (t (caddr x))))

(defun tpm-input->arg3 (x)
  (declare (xargs :guard (tpm-input-p x)))
  (cond ((atom x)

; (er hard? ...) causes an error when run but logically returns nil

         (er hard? 'tpm-input->arg3
             "tpm-input->arg3 ~x0 does not have a third argument"
             x))
        ((atom (cdr x))
         (er hard? 'tpm-input->arg3 
             "tpm-input->arg3 ~x0 does not have a third argument"
             x))
        ((atom (cddr x))
         (er hard? 'tpm-input->arg3
             "tpm-input->arg3 ~x0 does not have a third argument"
             x))
        ((atom (cdddr x))
         (er hard? 'tpm-input->arg3
             "tpm-input->arg3 ~x0 does not have a third argument"
             x))

        (t (cadddr x))))
