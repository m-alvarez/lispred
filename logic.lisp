(shadow '(substitute))

(use-package :cl-algebraic-data-type)
(use-package :anaphora)

(defgeneric to-string (elt))

(deftype <name> () '(or string atom))

(defdata <term>
  (<var> <name>)
  (<cst> <name>)
  (<fun> <name> list))

(defmethod to-string ((k <term>))
  (cl-algebraic-data-type:match <term> k
    ((<var> name) (string name))
    ((<cst> name) (string name))
    ((<fun> name args)
     (format nil "~a(~{~a~^, ~})"
	     (string name)
	     (mapcar #'to-string args)))))

(defun V (name)
  (<var> name))
(defun C (name)
  (<cst> name))
(defun F (name &rest args)
  (<fun> name args))

(defdata <binop>
  <binop-impl>
  <binop-and>
  <binop-or>)

(defmethod to-string ((op <binop>))
  (match <binop> op
    (<binop-impl> "->")
    (<binop-and>  "/\\")
    (<binop-or>   "\\/")))

(defun logic-function (b)
  (match <binop> b
    (<binop-impl> (lambda (a b) (or (not a) b)))
    (<binop-and>  (lambda (a b) (and a b)))
    (<binop-or>   (lambda (a b) (or a b)))))

(defdata <formula>
  (<bin> <binop> <formula> <formula>)
  (<not> <formula>)
  (<all> <var> <formula>)
  (<pred> <name> list)
  (<eq> <term> <term>))
  
(defun $AND (f1 f2)
  (<bin> <binop-and> f1 f2))
(defun $NOT (f)
  (<not> f))
(defun $ALL (var f)
  (<all> var f))
(defun $OR (f1 f2)
  (<bin> <binop-or> f1 f2))
(defun $IMPL (f1 f2)
  (<bin> <binop-impl> f1 f2))
(defun $EQ (t1 t2)
  (<eq> t1 t2))
(defun $PRED (name &rest terms)
  (<pred> name terms))
(defun P (name &rest terms)
  (<pred> name terms))

(defmethod to-string ((f <formula>))
  (match <formula> f
    ((<bin> op f1 f2) (format nil "(~a ~a ~a)"
			      (to-string f1)
			      (to-string op)
			      (to-string f2)))
    ((<not> f) (format nil "! ~a" (to-string f)))
    ((<all> var f) (format nil "all ~a : ~a"
			   (to-string var)
			   (to-string f)))
    ((<eq> t1 t2) (format nil "~a = ~a"
			  (to-string t1)
			  (to-string t2)))
    ((<pred> p args) (format nil "~a(~{~a~^, ~})"
			     (string p)
			     (mapcar #'to-string args)))))

(defgeneric atomic-formulae (f))

(defmethod atomic-formulae ((f <formula>))
  (match <formula> f
    ((<bin> _ f1 f2)
     (union (atomic-formulae f1)
	    (atomic-formulae f2)
	    :test #'equalp))
    ((<not> f)
     (atomic-formulae f))
    (_ (list f))))


(defgeneric free-variables (f))

(defmethod free-variables ((f <formula>))
  (match <formula> f
    ((<bin> _ f1 f2)
     (union (free-variables f1)
	    (free-variables f2)
	    :test #'equalp))
    ((<not> f) (free-variables f))
    ((<all> v f)
     (remove-if (lambda (var) (equalp var v)) (free-variables f)))
    ((<eq> t1 t2)
     (union (free-variables t1)
	    (free-variables t2)
	    :test #'equalp))
    ((<pred> _ terms)
     (reduce (lambda (v1 v2) (union v1 v2 :test #'equalp))
	     (cons nil (mapcar #'free-variables terms))))))
	    
(defmethod free-variables ((term <term>))
  (match <term> term
    ((<var> _) (list term))
    ((<cst> _) nil)
    ((<fun> _ terms)
     (reduce (lambda (v1 v2) (union v1 v2 :test #'equalp))
	     (cons nil (mapcar #'free-variables terms))))))

(defgeneric satisfiesp (assignment formula))

(defmethod satisfiesp (assignment (f <formula>))
  (match <formula> f
    ((<bin> op f1 f2)
     (funcall (logic-function op)
	      (satisfiesp assignment f1)
	      (satisfiesp assignment f2)))
    ((<not> f)
     (not (satisfiesp assignment f)))
    ((<all> _) (assoc f assignment :test #'equalp))
    ((<eq> _ _) (assoc f assignment :test #'equalp))
    ((<pred> _ _) (assoc f assignment :test #'equalp))))
      

(defun partially-satisfies-p (set-atomic-formulae unset-atomic-formulae formula)
  (if (null unset-atomic-formulae)
      (satisfiesp set-atomic-formulae formula)
      (let ((current-atomic-formula    (car unset-atomic-formulae))
	    (remaining-atomic-formulae (cdr unset-atomic-formulae)))
      (every #'(lambda (x) x)
	     (loop for truth-value in '(t nil)
		collect (partially-satisfies-p
			 (cons (cons current-atomic-formula truth-value)
			       set-atomic-formulae)
			 remaining-atomic-formulae
			 formula))))))

(defun tautologyp (f)
  (partially-satisfies-p '() (atomic-formulae f) f))

(defstruct (proof-step
	     (:constructor proof-step (n formula rule-text)))
  n formula rule-text)

(defvar *proof-steps* (list nil))

(defun new-proof ()
  (setf *proof-steps* (list nil)))

(defun current-proof ()
  (car *proof-steps*))

(defun current-proof-step-number ()
  (if (null (current-proof))
      0
      (proof-step-n (caar *proof-steps*))))

(defun get-proof-step (k)
  (loop for step in (current-proof)
       if (= (proof-step-n step)
	     k)
       return step))

(defmethod to-string ((s proof-step))
  (format nil "~10<~@r~> | ~30<~;~a~;~>(~a)"
	  (proof-step-n s)
	  (to-string (proof-step-formula s))
	  (proof-step-rule-text s)))

(defun print-current-proof ()
  (dolist (step (reverse (current-proof)))
    (princ (to-string step))
    (terpri)))

(defun add-proof-step (&key formula rule-text)
  (let ((new-step (proof-step (1+ (current-proof-step-number))
			      formula
			      rule-text)))
    (setf *proof-steps*
	  (cons (cons new-step (current-proof))
		(cdr *proof-steps*)))
    (print-current-proof)))

(defun undo (&optional (num-steps 1))
  (dotimes (x num-steps)
    (setf *proof-steps*
	  (cons (cdr (current-proof))
		(cdr *proof-steps*))))
  (print-current-proof))

(defun tautology (f)
  (if (tautologyp f)
      (add-proof-step :formula f
		      :rule-text "tautology")))

(defun modus-ponens (i1 i2)
  (let ((f1 (proof-step-formula (get-proof-step i1)))
	(f2 (proof-step-formula (get-proof-step i2))))
    (match <formula> f2
      ((<bin> op pre post)
       (if (not (equalp op <binop-impl>))
	   (format t "~a is not an implication!" f2)
	   (if (equalp pre f1)
	       (add-proof-step :formula post 
			       :rule-text (format nil "from ~@r and ~@r by Modus Ponens"
						  i1 i2))
	       (format t "Antecedent of ~a is not ~a!"
		       (to-string f2)
		       (to-string f1)))))
      (_ (format t "~a is not an implication!" f2)))))

(defun generalization (var i)
  (aif (get-proof-step i)
       (add-proof-step :formula ($all var (proof-step-formula it))
		       :rule-text (format nil "from ~@R by Generalization" i))
       (format t "No such step ~@R" i)))


(defgeneric substitutablep (obj &key var term))

(defmethod substitutablep ((f <formula>) &key var term)
  (match <formula> f
    ((<bin> _ f1 f2) (and (substitutablep f1 :var var :term term)
			  (substitutablep f2 :var var :term term)))
    ((<not> f) (substitutablep f :var var :term term))
    ((<eq> _ _ _) t)
    ((<pred> _ _) t)
    ((<all> v f)
     (or (equalp v var)
	 (and (not (find v (free-variables term)))
	      (substitutablep f :var var :term term))))))

(defgeneric substitute (obj &key var term))

(defmethod substitute ((obj <term>) &key var term)
  (match <term> obj
    ((<var> _) (if (equalp var obj) term obj))
    ((<cst> _) obj)
    ((<fun> f subterms)
     (<fun> f (mapcar #'(lambda (subterm) (substitute subterm :var var :term term))
		      subterms)))))

(defmethod substitute ((obj <formula>) &key var term)
  (match <formula> obj
    ((<bin> op f1 f2)
     (<bin> op
	    (substitute f1 :var var :term term)
	    (substitute f2 :var var :term term)))
    ((<not> f)
     (<not> (substitute f :var var :term term)))
    ((<all> v f)
     (if (equalp v var) obj
	 (<all> v (substitute f :var var :term term))))
    ((<pred> p terms)
     (<pred> p (mapcar #'(lambda (term) (substitute term :var var :term term)) terms)))
    ((<eq> t1 t2)
     (<eq> (substitute t1 :var var :term term)
	   (substitute t2 :var var :term term)))))

(defun substitution (i var term)
  (aif (get-proof-step i)
       (if (substitutablep it :var var :term term)
	   (substitute it :var var :term term)
	   (format t "~a is not substitutable by ~a in ~a"
		   (to-string var)
		   (to-string term)
		   (to-string it)))
       (format t "No such step ~@R" i)))

(defun axiom-forall (var f g)
  (if (not (find var (free-variables f) :test #'equalp))
      (add-proof-step :formula ($impl ($all var ($impl f g)) ($impl f ($all var g)))
		      :rule-text "axiom 2.1")
      (format t "~a appears free in ~a"
	      (to-string var)
	      (to-string f))))

(defun axiom-eq-refl (term)
  (add-proof-step :formula ($eq term term)
		  :rule-text "axiom 3.1"))

  

(defun construct-leibniz-fun ( fun-name binding-list )
  (let ((prop ($eq (<fun> fun-name (mapcar #'car binding-list))
		   (<fun> fun-name (mapcar #'cdr binding-list)))))
    (reduce (lambda (conseq pair) ($impl ($eq (car pair) (cdr pair)) conseq))
	    (cons prop (reverse binding-list)))))
	   
(defun axiom-leibniz-fun ( fun-name &rest binding-list )
  (add-proof-step :formula (construct-leibniz-fun fun-name binding-list)
		  :rule-text "axiom 3.2"))

(defun construct-leibniz-pred ( pred-name binding-list )
  (let ((prop ($impl (<pred> pred-name (mapcar #'car binding-list))
		     (<pred> pred-name (mapcar #'cdr binding-list)))))
    (reduce (lambda (conseq pair) ($impl ($eq (car pair) (cdr pair)) conseq))
	    (cons prop (reverse binding-list)))))

(defun axiom-leibniz-pred ( pred-name &rest binding-list )
  (add-proof-step :formula (construct-leibniz-pred pred-name binding-list)
		  :rule-text "axiom 3.3"))
  
