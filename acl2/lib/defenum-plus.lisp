(in-package "ACL2")

; Adapted from: ACL2 book "cutil/defenum"
(include-book "str/cat" :dir :system)
(include-book "cutil/portcullis" :dir :system)
(include-book "cutil/deflist" :dir :system)

(set-state-ok t)

(defund defenum+-member-to-test1 (predicates n xvar)
  (declare (xargs :guard (natp n)))
  (cond ((atom predicates)
         nil)
        (t 
         (cons (list (car predicates)
                     `(nth ,n ,xvar))
               (defenum+-member-to-test1 (cdr predicates) 
                 (1+ n)
                 xvar)))))

(defnd defenum+-member-to-test (member xvar)
  (let* ((member-name (or (and (atom member)
                               member)
                          (car member)))
         (predicates (and (consp member)
                            (cdr member))))
         
         (cond ((atom member)
                (cond ((symbolp member)
                       `(eq ,xvar ',member))
                      ((eqlablep member)
                       `(eql ,xvar ',member))
                      (t
                       `(equal ,xvar ',member))))
               (t (list* 'and
                         `(consp ,xvar) ; redundant with true-listp
                         (cond ((symbolp member-name)
                                `(eq (car ,xvar) ',member-name))
                               ((eqlablep member-name)
                                `(eql (car ,xvar) ',member-name))
                               (t
                                `(equal (car ,xvar) ',member-name)))
                         `(true-listp ,xvar)
                         `(eql (len ,xvar)
                               ,(len member))
                         (defenum+-member-to-test1 predicates 1 xvar))))))

(defnd defenum+-members-to-tests (members xvar)
  ;; Generate ((equal xvar member1) (equal xvar member2) ...), except use EQ or
  ;; EQL instead of EQUAL where possible.
  (if (atom members)
      nil
      (cons (defenum+-member-to-test (car members) xvar)
            (defenum+-members-to-tests (cdr members) xvar))))

; (defenum-members-to-tests '(:a :b 3 5 #\a "foo" '(1 . 2)) 'x)

(defn defenum-strip-cars-lite (members)
  (cond ((atom members)
         nil)
        ((atom (car members))
         (cons (car members)
               (defenum-strip-cars-lite (cdr members))))
        (t ; car of members is a list
         (cons (caar members)
               (defenum-strip-cars-lite (cdr members))))))

(defun defenum-deduce-type-set (members)
  ;; Figure out the best type set that covers all of members.
  (declare (xargs :mode :program))
  (if (atom members)
      0
    (acl2::ts-union
     (acl2::type-set-quote (car members))
     (defenum-deduce-type-set (cdr members)))))

;(acl2::decode-type-set
; (defenum-deduce-type-set '(:foo :bar 3 5)))
;  -->
; (ACL2::TS-UNION ACL2::*TS-POSITIVE-INTEGER*
;                 ACL2::*TS-NON-T-NON-NIL-SYMBOL*)


(defun defenum+-fn (name members mode parents short long state)
  (declare (xargs :mode :program)
           (ignorable state))
  (b* (((unless (symbolp name))
        (er hard 'deflist "Name must be a symbol, but is ~x0." name))

       (?mksym-package-symbol name)
       (x (intern-in-package-of-symbol "X" name))

       ((unless (consp members))
        (er hard 'defenum+ "There must be at least one member."))

       ((unless (uniquep members))
        (er hard 'defenum+
            "The members must be a list of unique, but there are ~
             duplicate entries for ~x0."
            (duplicated-members members)))

       ((unless (or (eq mode :logic)
                    (eq mode :program)))
        (er hard 'defenum+
            ":mode must be one of :logic or :program, but is ~x0." mode))

       (body (cons 'or (defenum+-members-to-tests members x)))
       (def `(defund ,name (,x)
               (declare (xargs :guard t))
               ,body))

       ;; (long (str::cat (or long "")
       ;;                 "<p>This is an ordinary @(see defenum+).</p>"
       ;;                 "@(def " (symbol-name name) ")"))

       (doc `(defxdoc ,name
               :parents ,parents
               :short ,short
               :long ,long))

       ((when (eq mode :program))
        `(encapsulate
           ()
           (program)
           ,doc
           ,def))


       ;; (long (str::cat long "@(gthm type-when-" (symbol-name name) ")"))

       (doc `(defxdoc ,name
               :parents ,parents
               :short ,short
               :long ,long))

       (ts (defenum-deduce-type-set members))

       ((mv ?ts-concl &)
        ;; Magic function from :doc type-set
        (acl2::convert-type-set-to-term x ts (acl2::ens state) (w state) nil)))

    `(encapsulate
       ()
       (logic)
       ,doc
       ,def
       (local (in-theory (enable ,name)))

       ;; (with-output
       ;;  :off observation
       ;;  (defthm ,(CUTIL::mksym 'type-when- name)
       ;;    (implies (,name ,x)
       ;;             ,ts-concl)
       ;;    :rule-classes :compound-recognizer))

       )))

(defmacro defenum+ (name members
                        &key
                        mode
                        (parents '(undocumented))
                        (short 'nil)
                        (long 'nil))
  `(make-event (let ((mode (or ',mode (default-defun-mode (w state)))))
                 (defenum+-fn ',name ',members mode ',parents ',short ',long state))))


;; Primitive tests
(local
 (encapsulate
   ()
   (defn food-p (x)
     (or (eq x 'pizza)
         (eq x 'hamburger)))

   (defn drink-p (x)
     (or (eq x 'lemonade)
         (eq x 'coffee)))

   (defn place-p (x)
     (or (eq x 'mount-rushmore)
         (eq x 'ut-tower)
         (eq x 'where-unicorns-grow-from-rainbows)))

   (defenum+ day-p
     (:monday (:tuesday food-p drink-p) (:wednesday place-p) :thursday :friday :saturday :sunday))

   (defenum+ chartest-p
     (#\a #\b #\c))

   (defenum+ strsymtest-p
     ("foo" "bar" foo bar))

   (defenum+ universal-ts-test-p
     (0 1 -1 1/2 -1/2 #c(3 4) nil t foo (1 . 2) (1) "foo" #\a))))

