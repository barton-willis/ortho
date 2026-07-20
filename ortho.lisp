;; Copyright (C) 2000, 2001, 2003, 2008, 2009, 2026 Barton Willis

#|
  This is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License,
  http://www.gnu.org/copyleft/gpl.html.

 This software has NO WARRANTY, not even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

Maxima code for evaluating orthogonal polynomials listed in Chapter 22 of Abramowitz and Stegun (A & S). 
|#
#| Templates!

(defun ...-numeric (n x digits)
  (handler-case
      (let* ((bf-x (bigfloat::to x))
             (f0 ...)
             (f1 ...)
             (eps (bigfloat::to (ftake 'mexpt 2 (- digits))))
             (p #'(lambda (k) ...)
             (q #'(lambda (k) ...))
        (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error p q f0 f1 n)
          (cond ((bigfloat::relative-error-p value err eps)
                 (maxima::to value))
                (t
                 ;; If precision is insufficient, boost fpprec and convert to bigfloat
                 (bind-fpprec (mul 2 $fpprec)
                   (...-numeric n ($bfloat x) (- $fpprec 2)))))))
    ;; Catch binary64 overflow and switch automatically to bigfloats
    (arithmetic-error (c)
	  (declare (ignore c))
      (bind-fpprec $fpprec
        (...-numeric n ($bfloat x) (- $fpprec 2))))))

(defun ...-symbolic (n x)
    (let* ((f0 ...)
		   (f1 ...)
           (p #'(lambda (k) ...))
           (q #'(lambda (k) ...))
		   (generic-two-term-recursion-symbolic p q f0 f1 x n)))

 |#
(in-package :maxima)

(defun orthopoly-polynomial-simp (p x)
"Intended solely to “clean up” the output of orthogonal‑polynomial constructors."
	(let (($ratfac t) ($algebraic t)) ($expand ($ratdisrep ($rat p x)) 0 0)))

(defmvar *binary64-digits* (floor (* (float-digits 1.0d0) (log 2 10))))
;; A left continuous unit step function; thus 
;;
;;       unit_step(x) = 0 for x <= 0 and 1 for x > 0.  
;;
;; This function differs from (1 + signum(x))/2 which isn't left or right
;; continuous at 0. We do not attempt to give unit_step a grad property.

;(defmfun $unit_step (x)
 ; (ftake '%unit_step x))
  
;(def-simplifier unit_step (x)
 ; (let ((sgn ($csign x)))
;	 (cond ((member sgn '($neg $nz $zero)) 0)
	;;       ((eq sgn '$pos) 1)
	 ;      (t (give-up)))))

(defun simp-unit-step (a y z)
  (oneargcheck a)
  (setq y (simpcheck (cadr a) z))
  (let ((s (csign y)))
    (cond ((or (eq s '$nz) (eq s '$zero) (eq s '$neg)) 0)
	  ((eq s '$pos) 1)
	  (t `(($unit_step simp) ,y)))))
(setf (get '$unit_step 'operators) 'simp-unit-step)
(setf (get '%unit_step 'operators) 'simp-unit-step)

;; A sign function for unit_step. When the argument to unit_step is declared to be negative or positive,
;; unit_step is simplified away before it arrives here--so returning pz is safe. For now, unit_step(%i)
;; is a nounform, so sign(unit_step(%i)) => pz.
(defun unit_step-sign-function (x)
   (declare (ignore x))
   (setq sign '$pz))
(setf (get '%unit_step 'sign-function) 'unit_step-sign-function)

;; antiderivative of unit_step
(putprop '%unit_step
  '((x) ((mtimes) ((rat) 1 2) ((mplus) x ((mabs) x))))  'integral)

(defun simplim%unit_step (e x pt)  
 "Return limit(unit_step(X),x, pt)."
  (let* ((*preserve-direction* t) 
         (z (cadr e))
         (lim (limit z x pt 'think)))
     (cond ((eq lim '$ind)
	        (cond ((eq t (mgrp 0 z)) 0)
                  ((eq t (mgrp z 0)) 1)
			      (t '$ind)))
           ((eq lim '$minf) 0)
		   ((eq lim '$inf) 1)
		   ((eq lim '$zerob) 0)
           ((eq lim '$zeroa) 1)
           ((or (eq lim '$und) (eq lim '$infinity)) (throw 'limit nil)) ; don't know
           (t (ftake '%unit_step lim))))) ; use direct substitution

(setf (get '%unit_step 'simplim%function) 'simplim%unit_step)


(print "at 1")
(defun multiplicative-identity (&rest a)
  "Return the appropriate multiplicative identity (1 for rational numbers, 1.0do for binary64, and 1.0b0 for bigfloats)
  for the numbers in the list a."
  (flet ((local-one (s) 
           (cond ((complex-number-p s #'$ratnump) 1)
                 ((complex-number-p s #'(lambda (q) (or ($ratnump q) (floatp q)))) 1.0d0)
                 ((complex-number-p s #'(lambda (q) (or ($ratnump q) (floatp q) ($bfloatp q)))) *bigfloatone*)
                 (t nil)))) ;not a complex number, return nil
    (let ((ones (mapcar #'local-one a)))
      (unless (member nil ones) ; If any element failed the check, abort numeric calculation
        (fapply 'mtimes ones)))))

(defun number-coerce (x one)
	(cond (($ratnump one) ($rationalize x))
	      ((floatp one) ($float x))
		  (t ($bfloat x))))

(def-simplifier jacobi_p (n a b x)
	(cond ((and (integerp n) 
	            (complex-number-p a #'$numberp)
				(complex-number-p b #'$numberp)
				(complex-number-p x #'$numberp))
		  (let* ((digits (if (floatp x)
			                  13
							  (- $fpprec 2)))
		        (one (multiplicative-identity a b x)))
			(if one 
			    (number-coerce (jacobi_p-numeric n a b x digits) one)
				(give-up))))
         ;; symbolic case call generic-two-term-recursion-symbolic
		((integerp n)
            (jacobi_p-symbolic n a b x))
        ;; reflection
		((great (neg x) x) ; jacobi_p(n,a,b,-x) = (-1)^n jacobi_p(n,b,a,x)
			(mul (ftake 'mexpt -1 n) (ftake '%jacobi_p n b a (neg x))))

		;; jacobi_p(n,a,b,1) = pochhammer(a+1,n)/n!
		((eql x 1)
			(div (ftake '$pochhammer (add a 1) n)
			     (ftake 'mfactorial n)))

		(t (give-up))))

(putprop '%jacobi_p
	 '((n a b x)
       nil
	   nil
	   nil
	   ((mtimes)
	    ((mexpt) ((mplus ) a b ((mtimes ) 2 n)) -1)
	    ((mplus)
	     ((mtimes) 2
	      ((%unit_step) n)
	      ((mplus) a n) ((mplus) b n)
	      ((%jacobi_p) ((mplus) -1 n) a b x))
	     ((mtimes) n ((%jacobi_p) n a b x)
	      ((mplus) a ((mtimes ) -1 b)
	       ((mtimes)
		((mplus) ((mtimes) -1 a) ((mtimes ) -1 b)
		 ((mtimes) -2 n)) x))))
	    ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt ) x 2))) -1)))
	 'grad)
 	   
;; See A&S 22.5.46, page 779.
(def-simplifier ultraspherical (n a x)
    (mtell "n = ~M ; a = ~M ; x = ~M ~%" n a x)
	(cond ((and (integerp n) (complex-number-p a #'$ratnump) (complex-number-p x #'$ratnump))
            (let* ((digits (if (floatp x)
			                  (- *binary64-digits* 2)
							  (- $fpprec 2)))
		        (one (multiplicative-identity a x)))
			(if one 
			    (number-coerce (ultraspherical-numeric n a x digits) one)
				(give-up))))

		  ((integerp n)
		    (ultraspherical-symbolic n a x))

		((great (neg x) x)
		 (mul (ftake 'mexpt -1 n) (ftake '%ultraspherical n a (neg x))))

        ((eql x 1)
	      (div (ftake '$pochhammer (mul 2 a) n) (ftake 'mfactorial n)))

        ;; see http://dlmf.nist.gov/18.7.E2 & http://dlmf.nist.gov/18.7.E3
		((and nil (eql a 0) ($featurep n '$integer) (eq t (mgqp n 0)))
			(mul
			    (div
				    (ftake '$pochhammer 0 n)
					(ftake 'mfactorial n))
			     (ftake '%chebyshev_t n x))) 

		(t (give-up))))

(print "at 2")
(putprop '%ultraspherical 
	 '((n a x)
	   nil 
	   nil
	   ((mtimes)
	    ((mplus)
	     ((mtimes)
	      ((%unit_step) n)
	      ((mplus) -1 ((mtimes) 2 a) n)
	      ((%ultraspherical) ((mplus) -1 n) a x))
	     ((mtimes) -1 n ((%ultraspherical) n a x) x))
	    ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1)))
	 'grad) 	

(defun ultraspherical-symbolic (n lam x)
  (let* ((f0 1)
         (f1 (mul 2 lam x))
         (2lam (mul 2 lam))
         (2lam-1 (sub 2lam 1))
         
         (p #'(lambda (k)
                (let* ((k+1 (add k 1))
                       ;; Numerator: 2(k + lam)x
                       (num (mul 2 (add k lam) x))
                       ;; Denominator: k + 1
                       (den k+1))
                  (div num den))))
         
         (q #'(lambda (k)
                (let* ((k+1 (add k 1))
                       ;; Numerator: -(k + 2lam - 1)
                       (num (mul -1 (add k 2lam-1)))
                       ;; Denominator: k + 1
                       (den k+1))
                  (div num den)))))
    (cond ((eql n 0) f0)
          ((eql n 1) f1)
          (t (generic-two-term-recursion-symbolic p q f0 f1 x n)))))
		  
(defun ultraspherical-numeric (n lam x digits)
  (handler-case
      (let* ((bf-x (bigfloat::to x))
             (f0 (bigfloat::to 1))
             (f1 (bigfloat::* (bigfloat::to 2) (bigfloat::to lam) bf-x)) ; Removed redundant (bigfloat::to bf-x)
             (eps (bigfloat::to (ftake 'mexpt 2 (- digits))))
             (bf-lam (bigfloat::to lam))
             (2lam (bigfloat::* (bigfloat::to 2) bf-lam))
             (2lam-1 (bigfloat::- 2lam (bigfloat::to 1)))

             (p #'(lambda (k)
                    (let* ((k+1 (bigfloat::+ k 1))
                           ;; Numerator: 2(k + lam)x
                           ;; FIXED: Coerced 2 to bigfloat and added missing closing parenthesis
                           (num (bigfloat::* (bigfloat::to 2) (bigfloat::+ k bf-lam) bf-x))
                           ;; Denominator: k + 1
                           (den k+1))
                      (bigfloat::/ num den))))
         
             (q #'(lambda (k)
                    (let* ((k+1 (bigfloat::+ k 1))
                           ;; Numerator: -(k + 2lam - 1)
                           (num (bigfloat::- (bigfloat::+ k 2lam-1)))
                           ;; Denominator: k + 1
                           (den k+1))
                      (bigfloat::/ num den)))))
        (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error p q f0 f1 n)
          (cond ((bigfloat::relative-error-p value err eps)
                 (maxima::to value))
                (t
                 ;; If precision is insufficient, boost fpprec and convert to bigfloat
                 (bind-fpprec (mul 2 $fpprec)
                   (ultraspherical-numeric n ($bfloat lam) ($bfloat x) (- $fpprec 2)))))))
    ;; Catch binary64 overflow and switch automatically to bigfloats
    (arithmetic-error (c)
      (declare (ignore c))
      (bind-fpprec $fpprec
        (ultraspherical-numeric n ($bfloat lam) ($bfloat x) (- $fpprec 2))))))

(print "at 3")
(def-simplifier chebyshev_t (n x)
  (cond ((and (integerp n) (complex-number-p x #'$ratnump))
            (let* ((digits (if (floatp x)
			                  (- *binary64-digits* 2)
							  (- $fpprec 2)))
		        (one (multiplicative-identity x)))
			(if one 
			    (number-coerce (chebyshev_t-numeric n x digits) one)
				(give-up))))

		  ((integerp n)
		    (chebyshev_t-symbolic n x))
          ;; See DLMF Table Table 18.6.1 for the following three simplifications:
		  ((eql x 1)  1)
		  ((and (eql x 0) ($featurep n '$even)) (ftake 'mexpt 1 (div n 2)))
		  ;; chebyshev_t(n,-x) = (-1)^n chebyshev_t(n,-x)
          ((great (neg x) x)
		    (mul (ftake 'mexpt -1 n) (ftake '%chebyshev_t n (neg x))))
          ;; no simplifications--give up
		  (t (give-up))))
  
(defun chebyshev_t-symbolic (n x)
  (let* ((f0 1)
         (f1 x)
         (p #'(lambda (k) 
                (declare (ignore k))
                (mul 2 x)))
         (q #'(lambda (k) 
                (declare (ignore k))
                -1)))
    (cond ((eql n 0) f0)
          ((eql n 1) f1)
          (t (generic-two-term-recursion-symbolic p q f0 f1 x n)))))

(defun chebyshev_t-numeric (n x digits)
  (handler-case
      (let* ((bf-x (bigfloat::to x))
             
             (f0 (bigfloat::to 1))
             (f1 bf-x)
             
             (eps (bigfloat::to (ftake 'mexpt 2 (- digits))))
             
             (p #'(lambda (k)
                    (declare (ignore k))
                    (bigfloat::* 2 bf-x)))
             
             (q #'(lambda (k)
                    (declare (ignore k))
                    (bigfloat::to -1))))
        
        (cond ((eql n 0) (maxima::to f0))
              ((eql n 1) (maxima::to f1))
              (t
               (multiple-value-bind (value err)
                   (bigfloat::generic-two-term-recursion-running-error p q f0 f1 n)
                 (cond ((bigfloat::relative-error-p value err eps)
                        (maxima::to value))
                       (t
                        (let ((new-fpprec (mul 2 $fpprec)))
                          (bind-fpprec new-fpprec
                            (chebyshev_t-numeric n ($bfloat x) (- new-fpprec 2))))))))))
    
    (arithmetic-error (c)
      (declare (ignore c))
      (let ((new-fpprec (mul 2 $fpprec)))
        (bind-fpprec new-fpprec
          (chebyshev_t-numeric n ($bfloat x) (- new-fpprec 2)))))))

(print "at 4")
(putprop '$chebyshev_t 
	 '((n x)
	   nil
	   ((mtimes)
	    ((mplus)
	     ((mtimes) n ((%chebyshev_t) ((mplus ) -1 n) x))
	     ((mtimes ) -1 n ((%chebyshev_t) n x) x))
	    ((mexpt) ((mplus ) 1 ((mtimes) -1 ((mexpt) x 2))) -1)))
	   'grad)


(def-simplifier chebyshev_u (n x)
   (cond ((and (integerp n) (complex-number-p x #'$ratnump))
             (let* ((digits (if (floatp x)
			                  (- *binary64-digits* 2)
							  (- $fpprec 2)))
		        (one (multiplicative-identity x)))
			(if one 
			    (number-coerce (chebyshev_u-numeric n x digits) one)
				(give-up))))

		  ((integerp n)
		    (chebyshev_u-symbolic n x))

		  ;; See DLMF Table Table 18.6.1 for the following three simplifications:
		  ((eql x 1) (add n 1))
		  
		  ((and (eql x 0) ($featurep n '$even)) 
		     (ftake 'mexpt 1 (div n 2)))

		  ;; chebyshev_t(n,-x) = (-1)^n chebyshev_t(n,-x)
          ((great (neg x) x)
		    (mul (ftake 'mexpt -1 n) (ftake '%chebyshev_u n (neg x))))
          ;; no simplifications--give up
		  (t (give-up))))

(defun chebyshev_u-symbolic (n x)
  (let* ((f0 1)
         (f1 (mul 2 x))
         (p #'(lambda (k) 
                (declare (ignore k))
                (mul 2 x)))
         (q #'(lambda (k) 
                (declare (ignore k))
                -1)))
    (cond ((eql n 0) f0)
          ((eql n 1) f1)
          (t (generic-two-term-recursion-symbolic p q f0 f1 x n)))))

(defun chebyshev_u-numeric (n x digits)
  (handler-case
      (let* ((bf-x (bigfloat::to x))
             
             (f0 (bigfloat::to 1))
             (f1 (bigfloat::* 2 bf-x))
             
             (eps (bigfloat::to (ftake 'mexpt 2 (- digits))))
             
             (p #'(lambda (k)
                    (declare (ignore k))
                    (bigfloat::* 2 bf-x)))
             
             (q #'(lambda (k)
                    (declare (ignore k))
                    (bigfloat::to -1))))
        
        (cond ((eql n 0) (maxima::to f0))
              ((eql n 1) (maxima::to f1))
              (t
               (multiple-value-bind (value err)
                   (bigfloat::generic-two-term-recursion-running-error p q f0 f1 n)
                 (cond ((bigfloat::relative-error-p value err eps)
                        (maxima::to value))
                       (t
                        (let ((new-fpprec (mul 2 $fpprec)))
                          (bind-fpprec new-fpprec
                            (chebyshev_u-numeric n ($bfloat x) (- new-fpprec 2))))))))))
    
    (arithmetic-error (c)
      (declare (ignore c))
      (let ((new-fpprec (mul 2 $fpprec)))
        (bind-fpprec new-fpprec
          (chebyshev_u-numeric n ($bfloat x) (- new-fpprec 2)))))))


(putprop '%chebyshev_u
	 '((n x)
	    nil
	   ((mtimes)
	    ((mplus)
	     ((mtimes)
	      ((%unit_step) n)
	      ((mplus) 1 n) ((%chebyshev_u) ((mplus) -1 n) x))
	     ((mtimes) -1 n ((%chebyshev_u) n x) x))
	    ((mexpt) ((mplus ) 1 ((mtimes) -1 ((mexpt) x 2))) -1)))
	 'grad) 

(def-simplifier legendre_p (n x)
   (cond ((and (integerp n) (complex-number-p x #'$numberp)) ;evaluate numerically
            (let* ((digits (if (floatp x)
			                  (- *binary64-digits* 2)
							  (- $fpprec 2)))
		        (one (multiplicative-identity x)))
			(if one 
			    (number-coerce (legendre_p-numeric n x digits) one)
				(give-up))))

		  ((integerp n)
              (legendre-p-symbolic n x))

		(t (give-up))))

(defun legendre_p-numeric (n x digits)
  (handler-case
      (let* ((bf-x (bigfloat::to x))
             (one (bigfloat::to 1))
             (f0 one)
             (f1 bf-x)
             (eps (bigfloat::to (ftake 'mexpt 2 (- digits))))
             (p #'(lambda (kk)
                    (let ((k (bigfloat::to kk)))
                      (bigfloat::/ (bigfloat::* (bigfloat::+ (bigfloat::* 2 k) 1) bf-x) (bigfloat::+ k 1))))) 
             (q #'(lambda (kk) 
                    (let ((k (bigfloat::to kk))) 
                      (bigfloat::/ k (bigfloat::+ k one))))))
        (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error p q f0 f1 n)
          (cond ((bigfloat::relative-error-p value err eps)
                 (maxima::to value))
                (t
                 ;; If precision is insufficient, boost fpprec and convert to bigfloat
                 (bind-fpprec (mul 2 $fpprec)
                   (legendre_p-numeric n ($bfloat x) (- $fpprec 2)))))))
    
    ;; Catch binary64 overflow and switch automatically to bigfloats
    (arithmetic-error (c)
      (declare (ignore c)) ; Bound 'c' to prevent compiler/runtime errors
      (bind-fpprec $fpprec
        (legendre_p-numeric n ($bfloat x) (- $fpprec 2))))))

(defun legendre-p-symbolic (n x)
    (let* ((f0 1)
		   (f1 x)
           (p #'(lambda (k) (div (mul (add (mul 2 k) 1) x) (add k 1)))) ; (2k+1)x/(k+1) 
           (q #'(lambda (k) (mul -1 (div k (add k 1))))))
	 (generic-two-term-recursion-symbolic p q f0 f1 x n)))
         
(print "at 5")
(putprop '%legendre_p 
	 '((n x) 
	   nil
	   ((mtimes)
	     ((mplus)
	      ((mtimes) n ((%legendre_p) ((mplus) -1 n) x))
	      ((mtimes) -1 n ((%legendre_p) n x) x))
	     ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1)))
	 'grad)
  


;;fred(l,m,x) := (-1)^m * (1-x^2)^(m/2) * ultraspherical(l-m,m+1/2,x);

(def-simplifier assoc_legendre_p (l m x)
  (cond ((and (integerp l) (integerp m) (<= (abs m) l) (complex-number-p x #'$ratnump))
           (let* ((digits (if (floatp x)
			                        (- *binary64-digits* 2)
							                (- $fpprec 2)))
		        (one (multiplicative-identity x)))
		    	(if one 
			        (number-coerce (assoc_legendre_p-numeric l m x digits) one)
				      (give-up))))

        ((and (integerp l) (integerp m) (<= (abs m) l))
          (assoc_legendre_p-symbolic l m x))
        (t  (give-up))))

(defun assoc_legendre_p-numeric (l m x digits)
  (cond ((< m 0)
          (mul 
              (div 1 (ftake 'mfactorial (sub l m)))
              (ftake 'mexpt -1 (div (- m) 2))
              (ftake 'mfactorial (add l m))
              (assoc_legendre_p-numeric l (- m) x digits)))
        (t 
          (let ((bf-x (bigfloat::to x)))
                (mul 
                   (if (evenp m) 1 -1)
                   (maxima::to (bigfloat::sqrt (bigfloat::- 1 (bigfloat::* bf-x bf-x))))
                   (ultraspherical-numeric (sub l m) (add m (div 1 2)) x digits))))))
            

(defun assoc_legendre_p-symbolic (l m x)
    (cond ((< m 0)
           (mul 
              (div 1 (ftake 'mfactorial (sub l m)))
              (if (evenp m) 1 -1)
              (ftake 'mfactorial (add l m))
              (assoc_legendre_p-symbolic l (- m) x)))
        (t 
           (let ((cnst (div (mul (ftake 'mexpt 2 m) (ftake '%gamma (add m (div 1 2))))
		                    (ftake 'mexpt '$%pi (div 1 2)))))
           (mul 
               (if (evenp m) 1 -1)
               cnst
               (ftake 'mexpt (sub 1 (mul x x)) (div m 2))
               (ftake '%ultraspherical (sub l m) (add m (div 1 2)) x))))))

;; For the derivative of the associated legendre p function, see
;; A & S 8.5.4 page 334.

(putprop '%assoc_legendre_p
	 '((n m x)
	   nil
	   nil
	   ((mtimes simp)
	    ((mplus simp)
	     ((mtimes simp) -1 ((mplus simp) m n) ((%unit_step) n)
	      ((%assoc_legendre_p simp) ((mplus simp) -1 n) m x))
	     ((mtimes simp) n ((%assoc_legendre_p simp) n m x) x))
	    ((mexpt simp) ((mplus simp) -1 ((mexpt simp) x 2)) -1))) 
	   'grad)
	   
;;; Simplifier for the Hermite polynomial H_n, not He_n; see DLMF Table Table 18.3.1. 
;;; (https://dlmf.nist.gov/18.3) For the recusion, see DLMF Table http://dlmf.nist.gov/18.9.T1. 
;;; For special values, see DLMF Table http://dlmf.nist.gov/18.6.i
(def-simplifier hermite (n x)
  (cond ((and (integerp n) (>= n 0) (complex-number-p x #'$numberp)) ;evaluate numerically
           (let* ((digits (if (floatp x)
			                  (- *binary64-digits* 2)
							  (- $fpprec 2)))
		        (one (multiplicative-identity x)))
			(if one 
			    (number-coerce (hermite-numeric n x digits) one)
				(give-up))))
        ;; symbolic case call generic-two-term-recursion-symbolic
        ((integerp n)
           (if (< n 0)
		     (give-up)
		    (hermite-symbolic n x)))
        ;; reflection: hermite(n,-x) = (-1)^n hermite(-n,-x)
        ((great (neg x) x)
         (mul (ftake 'mexpt -1 n) (ftake '%hermite n (neg x))))
        ;; hermite(2n,0) = (-1/2)^(n) pochhammer(n/2 + 1,n)
        ((and (eql 0 x) ($featurep n '$even))
         (let ((halfn (div n 2)))
           (mul (ftake 'mexpt (div -1 2) halfn)
                (ftake '$pochhammer (add 1 halfn) halfn))))
        ;; hermite(2n+1,0) = (-1/2)^m pochhammer(n+1,n+1)
        ((and (eql 0 x) ($featurep n '$odd))
         (let ((halfn (div (sub n 1) 2)))
           (mul (ftake 'mexpt (div -1 2) halfn)
                (ftake '$pochhammer (add 1 halfn) (add 1 halfn)))))
        (t (give-up))))

(defgrad %hermite ($n $x)
  nil
  #$$ 2*n*herite(n-1,x)$
  )

(def-simplifier gen_laguerre (n a x)
	(cond ((and (integerp n) (complex-number-p a #'$numberp) (complex-number-p x #'$numberp)
              (let* ((digits (if (floatp x)
			                  (- *binary64-digits* 2)
							  (- $fpprec 2)))
		        (one (multiplicative-identity a x)))
			(if one 
			    (number-coerce (gen_laguerre-numeric n a x digits) one)
				(give-up)))))
          ;; symbolic case 
		  ((integerp n)
             (gen_laguerre-symbolic n a x))
          ;; value for x=0 (see https://en.wikipedia.org/wiki/Laguerre_polynomials)
		  ((and (eql x 0) ($featurep n '$integer))
		   (ftake '%binomial (add n a) n))
          ;; nothing known--noun form return
 		  (t (give-up))))

(putprop '$gen_laguerre
	 '((n a x)
	   nil
	   nil
	   ((mtimes)
	    ((mplus)
	     ((mtimes) -1 ((mplus) a n)
	      ((%unit_step) n) ((%gen_laguerre) ((mplus) -1 n) a x))
	     ((mtimes) n ((%gen_laguerre) n a x)))
	    ((mexpt) x -1)))
	 'grad)

(def-simplifier laguerre (n x)
  (cond ((and (integerp n) (complex-number-p x #'$numberp))
          (let* ((digits (if (floatp x)
			                  (- *binary64-digits* 2)
							  (- $fpprec 2)))
		        (one (multiplicative-identity x)))
			(if one 
			    (number-coerce (laguerre-numeric n x digits) one)
				(give-up))))
          ;; symbolic case 
		  ((integerp n)
             (laguerre-symbolic n x))
          ;; nothing known--noun form return
 		  (t (give-up))))

(putprop '%laguerre
	 '((n x)
	   nil
	   ((mtimes)
	    ((mplus)
	     ((mtimes) -1 n ((%laguerre) ((mplus) -1 n) x))
	     ((mtimes) n ((%laguerre) n x)))
	    ((mexpt) x -1)))
	 'grad)

(defun laguerre-numeric (n x digits)
   (gen_laguerre-numeric n 0 x digits))

(defun laguerre-symbolic (n  x)
  (gen_laguerre-symbolic n 0 x))

(defun hermite-numeric (n x digits)
  (handler-case
      (let* ((bf-x (bigfloat::to x))
	         (bf-2x (bigfloat::* 2 bf-x))
             (f0 (bigfloat::to 1))
             (f1 bf-2x)
             (eps (bigfloat::to (ftake 'mexpt 2 (- digits))))
             (p #'(lambda (k) (declare (ignore k)) bf-2x))
             (q #'(lambda (k) (bigfloat::* -2 k)))) 
        (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error p q f0 f1 n)
          (cond ((bigfloat::relative-error-p value err eps)
                 (maxima::to value))
                (t
                 ;; If precision is insufficient, boost fpprec and convert to bigfloat
                 (bind-fpprec (mul 2 $fpprec)
                   (hermite-numeric n ($bfloat x) (- $fpprec 2)))))))
    ;; Catch binary64 overflow and switch automatically to bigfloats
    (arithmetic-error (c)
	  (declare (ignore c))
      (bind-fpprec $fpprec
        (hermite-numeric n ($bfloat x) (- $fpprec 2))))))

(defun hermite-symbolic (n x)
    (let* ((f0 1)
		       (f1 (mul 2 x))
           (p #'(lambda (k) (declare (ignore k)) (mul 2 x)))
           (q #'(lambda (k) (mul -2 k))))
		    (generic-two-term-recursion-symbolic p q f0 f1 x n)))

(in-package #:bigfloat)
(defun jacobi-order-one (a b x)
	(* (+ a 1) (+ 1 (- (/ (* (+ b a 2) (+ 1 (- x))) (* 2 (+ 1 a))))))) 

(in-package :maxima)

;;; Table 22.7 (page 782) of Abramowitz and Stegun (1964) gives the order-only recursion for 
;;; the Jacobi polynomials.  This recursion is missing from Table 18.9.1 of the DLMF. 
(defun jacobi_p-numeric (n a b x digits)
  (handler-case
      (let* ((bf-a (bigfloat::to a))
             (bf-b (bigfloat::to b))
             (bf-x (bigfloat::to x))
             
             (f0 (bigfloat::to 1))
             (f1 (bigfloat::/ (bigfloat::+ (bigfloat::* (bigfloat::+ bf-a bf-b 2) bf-x) 
                                           (bigfloat::- bf-a bf-b)) 
                              2))
             
             (eps (bigfloat::to (ftake 'mexpt 2 (- digits))))
             
             (a+b (bigfloat::+ bf-a bf-b))
             (a+b+1 (bigfloat::+ bf-a bf-b 1))
             (a+b+2 (bigfloat::+ bf-a bf-b 2))
             
             ;; a^2 - b^2
             (a2-b2 (bigfloat::- (bigfloat::* bf-a bf-a) (bigfloat::* bf-b bf-b)))
             
             (p #'(lambda (k)
                    (let* ((bf-k (bigfloat::to k))
                           (2k (bigfloat::* 2 bf-k))
                           (k+1 (bigfloat::+ bf-k 1))
                           
                           ;; Numerator: (2k + a + b + 1)(a^2 - b^2) + x pochhammer(2k + a + b,3)
                           (num (bigfloat::+
                                 (bigfloat::* (bigfloat::+ 2k a+b+1) a2-b2)
                                 (bigfloat::* bf-x (bigfloat::+ 2k a+b) (bigfloat::+ 2k a+b+1) (bigfloat::+ 2k a+b+2))))
                           
                           ;; Denominator: 2(k + 1)(k + a + b + 1)(2k + a + b)
                           (den (bigfloat::* 2 k+1 (bigfloat::+ bf-k a+b+1) (bigfloat::+ 2k a+b))))
                      (bigfloat::/ num den))))
             
             (q #'(lambda (k)
                    (let* ((bf-k (bigfloat::to k))
                           (2k (bigfloat::* 2 bf-k))
                           (k+1 (bigfloat::+ bf-k 1))                   
                           
                           ;; Numerator: 2(k + a)(k + b)(2k + a + b + 2)
                           (num (bigfloat::* -2 (bigfloat::+ bf-k bf-a) (bigfloat::+ bf-k bf-b) (bigfloat::+ 2k a+b+2)))
                           
                           ;; Denominator: 2(k + 1)(k + a + b + 1)(2k + a + b)
                           (den (bigfloat::* 2 k+1 (bigfloat::+ bf-k a+b+1) (bigfloat::+ 2k a+b))))
                      (bigfloat::/ num den)))))
        
        (cond ((eql n 0) (maxima::to f0))
              ((eql n 1) (maxima::to f1))
              (t
               (multiple-value-bind (value err)
                   (bigfloat::generic-two-term-recursion-running-error p q f0 f1 n)
                 (cond ((bigfloat::relative-error-p value err eps)
                        (maxima::to value))
                       (t
                        (let ((new-fpprec (mul 2 $fpprec)))
                          (bind-fpprec new-fpprec
                            (jacobi_p-numeric n ($bfloat a) ($bfloat b) ($bfloat x) (- new-fpprec 2))))))))))
    
    (arithmetic-error (c)
      (declare (ignore c))
      (let ((new-fpprec (mul 2 $fpprec)))
        (bind-fpprec new-fpprec
          (jacobi_p-numeric n ($bfloat a) ($bfloat b) ($bfloat x) (- new-fpprec 2)))))))

(defun jacobi_p-symbolic (n a b x)
  ;; explict summation: see http://dlmf.nist.gov/18.5.E8 
  (let ((s 0))
		(dotimes (k (+ 1 n))
			(setq s 
			      (add s
			         (mul
                       (ftake '%binomial (add n a) k)
			           (ftake '%binomial (add n b) (sub n k))
                       (ftake 'mexpt (div (sub x 1) 2) (sub n k))
			           (ftake 'mexpt (div (add x 1) 2) k)))))
	(orthopoly-polynomial-simp s x)))

(defun gen_laguerre-numeric (n a x digits)
  (handler-case
      (let* ((bf-a (bigfloat::to a))
             (bf-x (bigfloat::to x))
             
             (f0 (bigfloat::to 1))
             (f1 (bigfloat::- (bigfloat::+ bf-a 1) bf-x))
             
             (eps (bigfloat::to (ftake 'mexpt 2 (- digits))))
             
             ;; Pre-cache static parameter term
             (a+1 (bigfloat::+ bf-a 1))
             
             (p #'(lambda (k)
                    (let* ((bf-k (bigfloat::to k))
                           (k+1 (bigfloat::+ bf-k 1))
                           ;; Numerator: 2k + a + 1 - x
                           (num (bigfloat::- (bigfloat::+ (bigfloat::* 2 bf-k) a+1) bf-x)))
                      (bigfloat::/ num k+1))))
             
             (q #'(lambda (k)
                    (let* ((bf-k (bigfloat::to k))
                           (k+1 (bigfloat::+ bf-k 1))
                           ;; Numerator: -(k + a)
                           (num (bigfloat::- (bigfloat::+ bf-k bf-a))))
                      (bigfloat::/ num k+1)))))
        
        (cond ((eql n 0) (maxima::to f0))
              ((eql n 1) (maxima::to f1))
              (t
               (multiple-value-bind (value err)
                   (bigfloat::generic-two-term-recursion-running-error p q f0 f1 n)
                 (cond ((bigfloat::relative-error-p value err eps)
                        (maxima::to value))
                       (t
                        (let ((new-fpprec (mul 2 $fpprec)))
                          (bind-fpprec new-fpprec
                            (gen_laguerre-numeric n ($bfloat a) ($bfloat x) (- new-fpprec 2))))))))))
    
    (arithmetic-error (c)
      (declare (ignore c))
      (let ((new-fpprec (mul 2 $fpprec)))
        (bind-fpprec new-fpprec
          (gen_laguerre-numeric n ($bfloat a) ($bfloat x) (- new-fpprec 2)))))))

(defun gen_laguerre-symbolic (n a x)
  (let* ((f0 1)
         (f1 (sub (add a 1) x))
         (a+1 (add a 1))
         (p #'(lambda (k)
                (let* ((2k (mul 2 k))
                       (k+1 (add k 1))
                       ;; Numerator: 2k + a + 1 - x
                       (num (sub (add 2k a+1) x)))
                  (div num k+1))))
         
         (q #'(lambda (k)
                (let* ((k+1 (add k 1))
                       ;; Numerator: k + a
                       (num (mul -1 (add k a))))
                  (div num k+1)))))
    
    (cond ((eql n 0) f0)
          ((eql n 1) f1)
          (t (generic-two-term-recursion-symbolic p q f0 f1 x n)))))

;;;;;end numeric & symbolic code

(def-simplifier spherical_hankel1 (n x)
	(cond ((and (integerp n) (complex-number-p x #'$ratnump))
	        (spherical_hankel1-symbolic n x))

		  ((and (integerp n) (complex-number-p x #'$numberp))
            (let* ((digits (if (floatp x)
			                  (- *binary64-digits* 2)
							  (- $fpprec 2)))
		        (one (multiplicative-identity x)))
			(if one 
			    (number-coerce (spherical_hankel1-numeric n x digits) one)
				(give-up))))

		  (t (give-up))))		     
		   
;; Define a sequence f(n) = spherical_hanke1(n,x). A recursion for f is
;; f(n+1) = (2n +1) f(n)/x - f(n-1,z).  
(defun spherical_hankel1-symbolic (n x)
    (let* ((cis (ftake 'mexpt '$%e (mul '$%i x)))
	       (f0 (div (mul -1 '$%i cis) x))
		   (f1 (mul (div (add (div '$%i x) 1) x) cis))
		   (p #'(lambda (k) (div (add (mul 2 k) 1) x)))
		   (q #'(lambda (k) (declare (ignore k)) -1)))
		 (generic-two-term-recursion-symbolic f0 f1 p q x n)))

(in-package #:bigfloat)
(defun order-zero-spherical_hankel1 (x)
	(let* ((i (bigfloat::complex 0 1))
	      (cis (if (realp x)
	               (cis x)
				   (+ (cos x) (* i (sin x))))))
		(/ (* -1 i cis) x)))

(defun order-one-spherical_hankel1 (x)
 	(let* ((i (bigfloat::complex 0 1))
	      (cis (if (realp x)
	               (cis x)
				   (+ (cos x) (* i (sin x))))))
		;; -((%i*(1-%i*x)*%e^(%i*x))/x^2)
		(/ (* -1 i (- 1 (* i x)) cis) (* x x))))

(in-package :maxima)
(defun spherical_hankel1-numeric (n x digits)
  (handler-case
    (let* ((bf-x (bigfloat::to x))
	      (f0 (bigfloat::order-zero-spherical_hankel1 bf-x))
		  (f1 (bigfloat::order-one-spherical_hankel1 bf-x))
		  (eps (bigfloat::to (ftake 'mexpt 2 (- digits))))
          (p #'(lambda (k) (bigfloat::/ (+ (* 2 k) 1) bf-x)))
          (q #'(lambda (k) (declare (ignore k)) (bigfloat::to -1))))
        (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error p q f0 f1 n)
          (cond ((bigfloat::relative-error-p value err eps)
                 (maxima::to value))
                (t
                 ;; If precision is insufficient, boost fpprec and convert to bigfloat
                 (bind-fpprec (mul 2 $fpprec)
                   (spherical_hankel1-numeric n ($bfloat x) (- $fpprec 2)))))))
    ;; Catch binary64 overflow and switch automatically to bigfloats
    (arithmetic-error (c)
	  (declare (ignore c))
      (bind-fpprec $fpprec
        (spherical_hankel1-numeric n ($bfloat x) (- $fpprec 2))))))

(putprop '%spherical_hankel1
	 '((n x)
	   nil
	   ((mplus simp) ((%spherical_hankel1) ((mplus) -1 n) x)
	    ((mtimes simp) -1 ((mplus) 1 n)
	     ((%spherical_hankel1) n x) ((mexpt) x -1))))
	 'grad)

;; See A & S 10.1.36.

(defun $spherical_hankel2 (n x)
  (declare (ignore n x))
  (merror "Yikes"))
  

(putprop '%spherical_hankel2
	 '((n x)
	   ((unk) first spherical_hankel2)
	   ((mplus simp) ((%spherical_hankel2) ((mplus) -1 n) x)
	    ((mtimes simp) -1 ((mplus) 1 n)
	     ((%spherical_hankel2) n x) ((mexpt) x -1))))
	 'grad)


(def-simplifier spherical_bessel_j (n x)
    (cond ((and (integerp n) (complex-number-p x))
             (let* ((digits (if (floatp x)
			                  (- *binary64-digits* 2)
							  (- $fpprec 2)))
		        (one (multiplicative-identity x)))
			(if one 
			    (number-coerce (spherical_bessel_j-numeric n x digits) one)
				(give-up))))

		  ((integerp n)	
		    (spherical_bessel_j-symbolic n x))

		  ((great (neg x) x)
		  	(mul (ftake 'mexpt -1 n) (ftake '%spherical_bessel_j n x)))
		
		  (t (give-up))))
		    
(putprop '%spherical_bessel_j
	 '((n x)
	   nil
	   ((mtimes) ((mexpt) ((mplus) 1 ((mtimes) 2 n)) -1)
	    ((mplus)
	     ((mtimes) n ((%spherical_bessel_j) ((mplus) -1 n) x))
	     ((mtimes) -1 ((mplus) 1 n)
	      ((%spherical_bessel_j) ((mplus) 1 n) x)))))
	 'grad)
 
(defun spherical_bessel_j-numeric (n x digits)
  (handler-case
      (let* ((bf-x (bigfloat::to x))
             (f0 (bigfloat::to 1))
             (f1 (bigfloat::* 2 bf-x))
             (eps (bigfloat::to (ftake 'mexpt 2 (- digits))))
             (p #'(lambda (k) (declare (ignore k)) (bigfloat::* 2 bf-x)))
             (q #'(lambda (k) (bigfloat::- (bigfloat::* 2 k))))) 
        (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error p q f0 f1 n)
          (cond ((bigfloat::relative-error-p value err eps)
                 (maxima::to value))
                (t
                 ;; If precision is insufficient, boost fpprec and convert to bigfloat
                 (bind-fpprec (mul 2 $fpprec)
                   (hermite-numeric n ($bfloat x) (- $fpprec 2)))))))
    ;; Catch binary64 overflow and switch automatically to bigfloats
    (arithmetic-error (c)
	  (declare (ignore c))
      (bind-fpprec $fpprec
        (hermite-numeric n ($bfloat x) (- $fpprec 2))))))

(defun spherical_bessel_j-symbolic (n x)
   (if (eql x 0)
       0
	   (let (($besselexpand t)
	         (ans (div (mul (ftake 'mexpt '$%pi (div 1 2))
			                (ftake '%bessel_j (add n (div 1 2)) x))
					   (ftake 'mexpt (mul 2 x) (div 1 2)))))
		ans)))
	    
;; For analytic continuation, see A&S 10.1.35.
 
(defun $spherical_bessel_y (n x)
   (declare (ignore n x))
   (merror "spherical_bessel_y"))

(putprop '%spherical_bessel_y
	 '((n x)
	   ((unk) first spherical_bessel_y)
	   ((mtimes) ((mexpt) ((mplus) 1 ((mtimes) 2 n)) -1)
	    ((mplus)
	     ((mtimes) n ((%spherical_bessel_y) ((mplus) -1 n) x))
	     ((mtimes) -1 ((mplus) 1 n)
	      ((%spherical_bessel_y) ((mplus) 1 n) x)))))
	 'grad)

#|  
;; Compute P_n^m(cos(theta)).  See Merzbacher, 9.59 page 184
;; and 9.64 page 185, and A & S 22.5.37 page 779.  This function
;; lacks error checking; it should only be called by spherical_harmonic.

;; We need to be careful -- for the spherical harmonics we can't use
;; assoc_legendre_p(n,m,cos(x)).  If we did, we'd get factors 
;; (1 - cos^2(x))^(m/2) that simplify to |sin(x)|^m but we want them
;; to simplify to sin^m(x).  Oh my!

(defun assoc-leg-cos (n m x)
  (interval-mult
   (if (= m 0) 1 (mul (take '(%genfact) (sub (mul 2 m) 1) (sub m (div 1 2)) 2) (power (take '(%sin) x) m)))
   ($ultraspherical (sub n m) (add m (div 1 2)) (take  '(%cos) x))))

(defun $spherical_harmonic (n m th p)
  (cond ((and (integerp n) (integerp m) (> n -1))
	 (cond ((> (abs m) n)
		0)
	       ((< m 0)
		(interval-mult (if (oddp m) -1 1) 
			       ($spherical_harmonic n (- m) th (mul -1 p))))
	       (t
		(interval-mult
		 (mul ($exp (mul '$%i m p))
		      (power (div (* (+ (* 2 n) 1) (factorial (- n m)))
				  (mul '$%pi (* 4 (factorial (+ n m))))) 
			     `((rat) 1 2)))
		 (assoc-leg-cos n m th)))))
	(t
	 `(($spherical_harmonic) ,n ,m ,th ,p))))



(putprop '$spherical_harmonic
	 '((n m theta phi)
	   ((unk) first spherical_harmonic)
	   ((unk) second spherical_harmonic)
	   ((mplus)
	    ((mtimes) ((rat ) -1 2)
	     ((mexpt)
	      ((mtimes) ((mplus) ((mtimes) -1 m) n)
	       ((mplus) 1 m n))
	      ((rat) 1 2))
	     (($spherical_harmonic) n ((mplus) 1 m) theta phi)
	     ((mexpt) $%e ((mtimes) -1 $%i phi)))
	    ((mtimes) ((rat) 1 2)
	     ((mexpt)
	      ((mtimes) ((mplus) 1 ((mtimes) -1 m) n)
	       ((mplus) m n))
	      ((rat) 1 2))
	     (($spherical_harmonic) n ((mplus) -1 m) theta phi)
	     ((mexpt) $%e ((mtimes) $%i phi)))) 
	   
	   ((mtimes) $%i m (($spherical_harmonic) n m theta phi)))
	 'grad)
	  	   	  	 				 	
|#

;; For recursion relations, see A & S 22.7 page 782. 

;; legendre_p(n+1,x) = ((2*n+1)*legendre_p(n,x)*x-n*legendre_p(n-1,x))/(n+1)

;;  jacobi_p(n+1,a,b,x) = (((2*n+a+b+1)*(a^2-b^2) + 
;;    x*pochhammer(2*n+a+b,3)) * jacobi_p(n,a,b,x) - 
;;    2*(n+a)*(n+b)*(2*n+a+b+2)*jacobi_p(n-1,a,b,x))/(2*(n+1)*(n+a+b+1)*(2*n+a+b))

;; ultraspherical(n+1,a,x) = (2*(n+a)*x * ultraspherical(n,a,x) - 
;;    (n+2*a-1)*ultraspherical(n-1,a,x))/(n+1)

;; chebyshev_t(n+1,x) = 2*x*chebyshev_t(n,x) -chebyshev_t(n-1,x)

;; chebyshev_u(n+1,x) = 2*x*chebyshev_u(n,x) -chebyshev_u(n-1,x)

;;  laguerre(n+1,x) = (((2*n+1) - x)*laguerre(n,x)  -(n)*laguerre(n-1,x))/(n+1)

;; gen_laguerre(n+1,a,x) = (((2*n+a+1) - x)*gen_laguerre(n,a,x)  
;;  -(n+a)*gen_laguerre(n-1,a,x))/(n+1)

;; hermite(n+1,x) = 2*x*hermite(n,x) -2*n*hermite(n-1,x)

;; See G & R 8.733.2; A & S 22.7.11 might be wrong -- or maybe I need
;; reading glasses.

;; (2*n+1)*x*assoc_legendre_p(n,m,x) = (n-m+1)*assoc_legendre_p(n+1,m,x) 
;; + (n+m)*assoc_legendre_p(n-1,m,x)

;; For the half-integer bessel functions, See A & S 10.1.19

;; fn(n-1,x) + fn(n+1,x) = (2*n+1)*fn(n,x)/x;

(defun check-arg-length (fn n m)
  (if (not (= n m))
      (merror "Function ~:M needs ~:M arguments, instead it received ~:M"
	      fn n m)))

(defun $orthopoly_recur (fn arg)
  (if (not ($listp arg)) 
      (merror "The second argument to orthopoly_recur must be a list"))
  (cond ((eq fn '$jacobi_p)
	 (check-arg-length fn 4 (- (length arg) 1))
	 (let ((n (nth 1 arg))
	       (a (nth 2 arg))
	       (b (nth 3 arg))
	       (x (nth 4 arg)))
	   (simplify
	    `((mequal) (($jacobi_p ) ((mplus) 1 ,n) ,a ,b ,x)
	      ((mtimes) ((rat) 1 2) ((mexpt) ((mplus) 1 ,n) -1)
	       ((mexpt) ((mplus) 1 ,a ,b ,n) -1)
	       ((mexpt) ((mplus) ,a ,b ((mtimes) 2 ,n)) -1)
	       ((mplus)
		((mtimes) -2 ((mplus) ,a ,n) ((mplus) ,b ,n)
		 ((mplus) 2 ,a ,b ((mtimes) 2 ,n))
		 (($jacobi_p ) ((mplus) -1 ,n) ,a ,b ,x))
		((mtimes) (($jacobi_p ) ,n ,a ,b ,x)
		 ((mplus)
		 ((mtimes)
		  ((mplus) ((mexpt) ,a 2)
		   ((mtimes) -1 ((mexpt) ,b 2)))
		  ((mplus) 1 ,a ,b ((mtimes) 2 ,n)))
		 ((mtimes) ((mplus) ,a ,b ((mtimes) 2 ,n))
		  ((mplus) 1 ,a ,b ((mtimes) 2 ,n))
		  ((mplus) 2 ,a ,b ((mtimes) 2 ,n)) ,x)))))))))

	((eq fn '$ultraspherical)
	 (check-arg-length fn 3 (- (length arg) 1))
	 (let ((n (nth 1 arg))
	       (a (nth 2 arg))
	       (x (nth 3 arg)))
	   (simplify
	    `((mequal) (($ultraspherical) ((mplus) 1 ,n) ,a ,x)
	     ((mtimes) ((mexpt) ((mplus) 1 ,n) -1)
	      ((mplus)
	       ((mtimes) -1 ((mplus) -1 ((mtimes) 2 ,a) ,n)
		(($ultraspherical) ((mplus) -1 ,n) ,a ,x))
	       ((mtimes) 2 ((mplus) ,a ,n)
		(($ultraspherical) ,n ,a ,x) ,x)))))))

	((member fn  `($chebyshev_t $chebyshev_u) :test 'eq)
	 (check-arg-length fn 2 (- (length arg) 1))
	 (let ((n (nth 1 arg))
	       (x (nth 2 arg)))
	  (simplify
	   `((mequal ) ((,fn) ((mplus ) 1 ,n) ,x)
	    ((mplus )
	     ((mtimes ) -1 ((,fn) ((mplus ) -1 ,n) ,x))
	     ((mtimes ) 2 ((,fn) ,n ,x) ,x))))))

	((member fn '($legendre_p $legendre_q) :test 'eq)
	 (check-arg-length fn 2 (- (length arg) 1))
	 (let* ((n (nth 1 arg))
	       (x (nth 2 arg))
	       (z (if (eq fn '$legendre_q) 
		      `((mtimes) -1 ((%kron_delta) ,n 0)) 0))) 
	   (simplify
	     `((mequal) ((,fn) ((mplus) 1 ,n) ,x)
	       ((mplus)
		((mtimes) ((mexpt) ((mplus) 1 ,n) -1)
		 ((mplus)
		  ((mtimes) ((mtimes) -1 ,n)
		   ((,fn) ((mplus) -1 ,n) ,x))
		  ((mtimes) ((mplus) 1 ((mtimes) 2 ,n))
		   ((,fn) ,n ,x) ,x)))
		,z)))))

	((member fn '($assoc_legendre_p $assoc_legendre_q) :test 'eq)
	 (check-arg-length fn 3 (- (length arg) 1))
	 (let ((n (nth 1 arg))
	       (m (nth 2 arg))
	       (x (nth 3 arg)))
	   (simplify
	    `((mequal) ((,fn) ((mplus) 1 ,n) ,m ,x)
	      ((mtimes)
	       ((mexpt) ((mplus) 1 ((mtimes) -1 ,m) ,n) -1)
	       ((mplus)
		((mtimes)
		 ((mplus) ((mtimes) -1 ,m)
		  ((mtimes) -1 ,n))
		 ((,fn) ((mplus) -1 ,n) ,m ,x))
		((mtimes) ((mplus) 1 ((mtimes) 2 ,n))
		 ((,fn) ,n ,m ,x) ,x))))))) 
	
	((eq fn '$laguerre)
	 (check-arg-length fn 2 (- (length arg) 1))
	 (let ((n (nth 1 arg))
	       (x (nth 2 arg)))
	   (simplify
	    `((mequal ) (($laguerre ) ((mplus ) 1 ,n) ,x)
	      ((mtimes ) ((mexpt ) ((mplus ) 1 ,n) -1)
	       ((mplus )
		((mtimes ) -1 ,n (($laguerre ) ((mplus ) -1 ,n) ,x))
		((mtimes ) (($laguerre ) ,n ,x)
		 ((mplus ) 1 ((mtimes ) 2 ,n) ((mtimes ) -1 ,x))))))))) 

	((eq fn '$gen_laguerre)
	 (check-arg-length fn 3 (- (length arg) 1))
	 (let ((n (nth 1 arg))
	       (a (nth 2 arg))
	       (x (nth 3 arg)))
	   (simplify
	    `((mequal) (($gen_laguerre) ((mplus) 1 ,n) ,a ,x)
	      ((mtimes) ((mexpt ) ((mplus) 1 ,n) -1)
	       ((mplus)
		((mtimes) -1 ((mplus) ,a ,n)
		 (($gen_laguerre) ((mplus) -1 ,n) ,a ,x))
		((mtimes) (($gen_laguerre) ,n ,a ,x)
		 ((mplus) 1 ,a ((mtimes) 2 ,n) ((mtimes ) -1 ,x))))))))) 

	((eq fn '$hermite)
	 (check-arg-length fn 2 (- (length arg) 1))
	 (let ((n (nth 1 arg))
	       (x (nth 2 arg)))
	   (simplify
	    `((mequal) (($hermite) ((mplus) 1 ,n) ,x)
	      ((mplus)
	       ((mtimes) -2 ,n (($hermite) ((mplus) -1 ,n) ,x))
	       ((mtimes) 2 (($hermite) ,n ,x) ,x))))))

	((member fn `($spherical_bessel_j $spherical_bessel_y
					  $spherical_hankel1 $spherical_hankel2)
		 :test 'eq)
	 (check-arg-length fn 2 (- (length arg) 1))
	 (let ((n (nth 1 arg))
	       (x (nth 2 arg)))
	   (simplify
	    `((mequal) ((,fn) ((mplus) 1 ,n) ,x)
	      ((mplus) ((mtimes) -1 ((,fn ) ((mplus) -1 ,n) ,x))
	       ((mtimes) ((,fn) ,n ,x) ((mexpt) ,x -1))
	       ((mtimes) 2 ,n ((,fn ) ,n ,x) ((mexpt) ,x -1)))))))
	 
	(t (merror "A recursion relation for ~:M isn't known to Maxima" fn))))
    
;; See A & S Table 22.2, page 774.

(defun $orthopoly_weight (fn arg)
  (if (not ($listp arg)) 
      (merror "The second argument to orthopoly_weight must be a list"))

  (if (not (or ($symbolp (car (last arg))) ($subvarp (car (last arg)))))
      (merror "The last element of the second argument to orthopoly_weight must
be a symbol or a subscripted symbol, instead found ~:M" (car (last arg))))

  (if (not (every #'(lambda (s) 
		      ($freeof (car (last arg)) s)) (butlast (cdr arg))))
      (merror "Only the last element of ~:M may depend on the integration
variable ~:M" arg (car (last arg))))

  (cond ((eq fn '$jacobi_p)
	 (check-arg-length fn 4 (- (length arg) 1))
	 (let ((a (nth 2 arg))
	       (b (nth 3 arg))
	       (x (nth 4 arg)))
	   (simplify
	    `((mlist)
	      ((mtimes) ((mexpt) ((mplus) 1 ((mtimes) -1 ,x)) ,a)
	       ((mexpt) ((mplus ) 1 ,x) ,b))
	      -1 1))))
	
	((eq fn '$ultraspherical)
	 (check-arg-length fn 3 (- (length arg) 1))
	 (let ((a (nth 2 arg))
	       (x (nth 3 arg)))
	   (simplify
	    `((mlist)
	      ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) ,x 2)))
	       ((mplus) ((rat) -1 2) ,a)) -1 1))))

	((eq fn '$chebyshev_t)
	 (check-arg-length fn 2 (- (length arg) 1))
	 (let ((x (nth 2 arg)))
	   (simplify
	    `((mlist)
	      ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) ,x 2)))
	       ((rat) -1 2)) -1 1)))) 
	  
	((eq fn '$chebyshev_u)
	 (check-arg-length fn 2 (- (length arg) 1))
	 (let ((x (nth 2 arg)))
	   (simplify
	    `((mlist)
	      ((mexpt) ((mplus) 1  ((mtimes) -1 ((mexpt) ,x 2)))
	       ((rat) 1 2)) -1 1))))

	((eq fn '$legendre_p)
	 (check-arg-length fn 2 (- (length arg) 1))
	 `((mlist) 1 -1 1))

	; This is for a fixed order.  There is also an orthogonality
	; condition for fixed degree with weight function 1/(1-x^2).
	; See A & S 8.14.11 and 8.14.12.
	((eq fn '$assoc_legendre_p)
	 (check-arg-length fn 3 (- (length arg) 1))
	 `((mlist) 1 -1 1))

	((eq fn '$laguerre)
	 (check-arg-length fn 2 (- (length arg) 1))
	 (let ((x (nth 2 arg)))
	   (simplify
	    `((mlist) ((mexpt) $%e ((mtimes) -1 ,x)) 0 $inf))))

	((eq fn '$gen_laguerre)
	 (check-arg-length fn 3 (- (length arg) 1))
	 (let ((a (nth 2 arg))
	       (x (nth 3 arg)))
	   (simplify
	    `((mlist)
	      ((mtimes) ((mexpt) ,x ,a)
	       ((mexpt) $%e ((mtimes) -1 ,x))) 0 $inf))))

	((eq fn '$hermite)
	 (check-arg-length fn 2 (- (length arg) 1))
	 (let ((x (nth 2 arg)))
	   (simplify
	    `((mlist) ((mexpt) $%e ((mtimes) -1 ((mexpt) ,x 2)))
	      ((mtimes ) -1 $inf) $inf))))

	(t (merror "A weight for ~:M isn't known to Maxima" fn))))

(defun generic-two-term-recursion-symbolic (p q f0 f1 x n)
  (cond ((eql n 0)
         f0)
        ((eql n 1)
         f1)
        (t
         (let ((fm1 f0)
               (fi  f1))
           (do ((i 1 (1+ i)))
               ((> i (1- n)) fi)
             (let* ((a (funcall p i))
                    (b (funcall q i))
                    (new (add (mul a fi)
                              (mul b fm1))))
               (setq fm1 fi
                     fi  new)))
			(let (($ratfac t))	($ratdisrep ($rat fi x)))))))

(in-package #:bigfloat)

;; Extend epsilon to rationals and complex rationals
(defmethod epsilon ((x cl:rational))
  (bigfloat::to 0))

(defmethod epsilon ((x cl:number))
  ;; Fallback catch-all for any other number types (like complex rationals)
  ;; by extracting the real part and evaluating its epsilon.
  (epsilon (cl:realpart x)))


(defun relative-error-p (x err eps)
  (< (abs err) (* eps (max 1 (abs x)))))

#| 
(defun hypergeo21-polynomial-numeric (n b c x) 
  "Return two values: the function value and its running error bound."
  (let* ((one (bigfloat::to 1))
         (f0 one)
         (f1 (- one (/ (* b x) c)))
         (p #'(lambda (i) (/ (+ (* 2 i) c (- (* x (+ b i)))) (+ c i))))
         (q #'(lambda (i) (/ (* i (- x 1)) (+ c i)))))
    
    (if (eql n 0)
        (values f0 (bigfloat::to 0))
        (generic-two-term-recursion p q f0 f1 (- n)))))
|#

(defun generic-two-term-recursion-running-error (p q f0 f1 n)
  "Evaluates the recurrence forward while simultaneously tracking the running error bound."
  (let* ((fm1 f0)   
         (fi f1)    
         (fnext)
         (eps (bigfloat::epsilon fi))
         (err-m1 (bigfloat::to 0))
         (err-i (* eps (bigfloat::abs fi))) 
         (err-next))
    
    (dotimes (i (- n 1))
      (let* ((current-i (+ i 1))
             (a (funcall p current-i))
             (b (funcall q current-i)))
        
        (setq fnext (+ (* a fi) (* b fm1)))
        
        (setq err-next (+ (* (bigfloat::abs a) err-i)
                          (* (bigfloat::abs b) err-m1)
                          (* eps (+ (bigfloat::abs (* a fi)) 
                                    (bigfloat::abs (* b fm1)) 
                                    (bigfloat::abs fnext)))))
        
        (setq fm1 fi
              fi fnext)
        (setq err-m1 err-i
              err-i err-next)))
              
    ;; Return both computed results using standard Lisp values
    (values fi err-i)))

(in-package :maxima)

(def-simplifier legendre_q (n x)
  (cond ((and (integerp n) (> n -1) (complex-number-p x #'$numberp))
          (let* ((digits (if (floatp x)
			                  (- *binary64-digits* 2)
							  (- $fpprec 2)))
		        (one (multiplicative-identity x)))
			(if one 
			    (number-coerce (legendre_q-numeric n x digits) one)
				(give-up))))
		((and (integerp n) (> n -1))
		   (legendre_q-symbolic n x))
        ((and (eql x 0) ($featurep n '$integer) (or  ($featurep n '$even) ($featurep n '$odd)))
           (legendre_q-at-zero n))
		(t (give-up))))

(defun legendre_q-numeric (n x digits)
	(let* ((g (gensym))
	       (f (legendre_q-symbolic n g)))
	  (mfuncall '$nfloat f (ftake 'mlist (ftake 'mequal g x)) digits)))

(defun legendre_q-at-zero (n)
  (if ($featurep n '$even)
      0
      (let* ((k (div (sub n 1) 2))
             (num (mul (ftake 'mexpt 2 (mul 2 k))
                       (ftake 'mfactorial k)
                       (ftake 'mfactorial k)))
             (den (ftake 'mfactorial (add (mul 2 k) 1)))
             (sgn (ftake 'mexpt -1 k)))
        (div (mul sgn num) den))))

;; See http://dlmf.nist.gov/14.7.E3
(defun legendre_q-symbolic (n x)
  "Return sum_{s=0}^{n-1} (n+s)!*(psi(n+1) - psi(s+1)) * (x-1)^s/(2^s * (n-s)!*(s!)^2)+(1/2) * P_n(x) * log((1+x)/(1-x))."

  ;; psi is a subscripted function: psi[0](k)
  (flet ((psi (subscript arg)
  
           ;; subscript is 0 for digamma
           ;; arg is the argument (n+1, s+1, etc.)
           (simplify (subfunmake '$psi (list subscript) (list arg)))))

    (let ((sum 0)
          (psi-n (psi 0 (add n 1))))
      ;; main sum: s = 0 .. n-1
      (dotimes (s n)
        (let* ((ns  (ftake 'mfactorial (add n s)))
               (nm  (ftake 'mfactorial (sub n s)))
               (sf  (ftake 'mfactorial s))
               (psi-s (psi 0 (add s 1)))
               (coef  (mul ns
                           (sub psi-n psi-s)
                           (ftake 'mexpt (sub x 1) s)))
               (den   (mul (ftake 'mexpt 2 s)
                           nm
                           (mul sf sf)))
               (term  (div coef den)))
          (setq sum (add sum term))))

      ;; add (1/2) * P_n(x) * log((1+x)/(1-x))
      (let* ((pn   (ftake '%legendre_p n x))
             (logt (ftake '%log
                          (div (add 1 x)
                               (sub 1 x))))
             (extra (mul (div 1 2) pn logt)))
        (setq sum (sub extra sum)))

      ;; final cleanup
      (orthopoly-polynomial-simp sum x))))

;; See G & R, 8.733, page 1005 first equation.

(putprop '%assoc_legendre_q
	 '((n m x)
     nil
	   nil	   
	   ((mplus)
	    ((mtimes)
	     ((mplus)
	      ((mtimes) -1 ((mplus) 1 ((mtimes) -1 m) n)
	       ((%assoc_legendre_q ) ((mplus ) 1 n) m x))
	      ((mtimes) ((mplus) 1 n)
	       ((%assoc_legendre_q ) n m x) x))
	     ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1))))
	 'grad) 

(def-simplifier assoc_legendre_q (n m x)
  (cond ((and (integerp n) (integerp m) (complex-number-p x #'$numberp) (> n -1) (<= (abs m) n))
           (let* ((digits (if (floatp x)
			                  (- *binary64-digits* 2)
							  (- $fpprec 2)))
		        (one (multiplicative-identity x)))
			(if one 
			    (number-coerce (assoc_legendre_q-numeric n m x digits) one)
				(give-up))))

      ((and (integerp n) (integerp m) (> n -1) (<= (abs m) n))
       (assoc_legendre_q-symbolic n m x))

      ((eql m 0)
        (ftake '%legendre_q n x))

      (t (give-up))))

(defun assoc_legendre_q-symbolic (n m x)
  (let* ((g (gensym))
         (f (ftake '%legendre_q n g)))

    (orthopoly-polynomial-simp 
        (maxima-substitute x g
           (mul (ftake 'mexpt -1 m)
            (ftake 'mexpt (sub 1 (mul x x)) (div m 2))
            ($diff f g m))) x)))

(defun assoc_legendre_q-numeric (n m x digits)
    (let* ((g (gensym))
           (f (assoc_legendre_q-symbolic n m g)))
      (nfloat f (ftake 'mlist (ftake 'mequal g x)) digits $max_fpprec)))
      
;; See G & R, 8.733, page 1005 first equation.

(putprop '%assoc_legendre_q
	 '((n m x)
	   nil
	   nil
	   ((mplus)
	    ((mtimes)
	     ((mplus)
	      ((mtimes) -1 ((mplus) 1 ((mtimes) -1 m) n)
	       ((%assoc_legendre_q ) ((mplus ) 1 n) m x))
	      ((mtimes) ((mplus) 1 n)
	       ((%assoc_legendre_q ) n m x) x))
	     ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1))))
	 'grad) 

;; improve & move to gamma.lisp

(defmvar $pochhammer_max_index 100)

;; This disallows noninteger assignments to $pochhammer_max_index.

(setf (get '$pochhammer_max_index 'assign)
      #'(lambda (a b) 
	  (declare (ignore a))
	  (if (not (and (atom b) (integerp b)))
	      (progn
		(mtell "The value of `pochhammer_max_index' must be an integer.~%")
		'munbindp))))

(defun $pochhammer (x n)
  (take '($pochhammer) x n))

(in-package #:bigfloat)

;; Numerical evaluation of pochhammer using the bigfloat package.
(defun pochhammer (x n)
  (let ((acc 1))
    (if (< n 0) (/ 1 (pochhammer (+ x n) (- n)))
      (dotimes (k n acc)
	(setq acc (* acc (+ k x)))))))

(in-package :maxima)

(defun simp-pochhammer (e y z)
  (declare (ignore y))
  (let ((x) (n) (return-a-rat))
    (twoargcheck e)
    (setq return-a-rat ($ratp (second e)))
    (setq x (simplifya (specrepcheck (second e)) z))
    (setq n (simplifya (specrepcheck (third e)) z))
 
    (cond ((or ($taylorp (second e)) ($taylorp (third e)))
	   (setq x (simplifya (second e) z))
	   (setq n (simplifya (third e) z))
	   ($taylor (div (take '(%gamma) (add x n)) (take '(%gamma) x))))
	   
	  ((eql n 0) 1)
	  
	  ;; pochhammer(1,n) = n! (factorial is faster than bigfloat::pochhammer.)
	  ((eql x 1) (take '(mfactorial) n))
     

      ((and (eql x 0) (eql n 0)) 1); pochhammer(0,0)=1

	  ;;;((and (eql x 0) (eq t (mnqp n 0))) 0)
	
	  ;; pure numeric evaluation--use numeric package.
	  ((and (integerp n) (complex-number-p x '$numberp))
	   (maxima::to (bigfloat::pochhammer (bigfloat::to x) (bigfloat::to n))))

	  ((and (integerp (mul 2 n)) (integerp (mul 2 x)) (> (mul 2 n) 0) (> (mul 2 x) 0))
	   (div (take '(%gamma) (add x n)) (take '(%gamma) x)))

	  ;; Use a reflection identity when (great (neg n) n) is true. Specifically,
	  ;; use pochhammer(x,-n) * pochhammer(x-n,n) = 1; thus pochhammer(x,n) = 1/pochhammer(x+n,-n).
	  ((great (neg n) n)
	   (div 1 (take '($pochhammer) (add x n) (neg n))))
	  
	  ;; Expand when n is an integer and either abs(n) < $expop or abs(n) < $pochhammer_max_index.
	  ;; Let's give $expand a bit of early help.
	  ((and (integerp n) (or (< (abs n) $expop) (< (abs n) $pochhammer_max_index)))
	   (if (< n 0) (div 1 (take '($pochhammer) (add x n) (neg n)))
	     (let ((acc 1))
	       (if (or (< (abs n) $expop) return-a-rat) (setq acc ($rat acc) x ($rat x)))
	       (dotimes (k n (if return-a-rat acc ($ratdisrep acc)))
		 (setq acc (mul acc (add k x)))))))

	 
	   
	  ;; return a nounform.
	  (t `(($pochhammer simp) ,x ,n)))))

(putprop '$pochhammer
	 '((x n)
	   ((mtimes) (($pochhammer) x n)
	    ((mplus) ((mtimes) -1 ((mqapply) (($psi array) 0) x))
	     ((mqapply) (($psi array) 0) ((mplus) n x)))) 
	   ((mtimes) (($pochhammer) x n)
	    ((mqapply) (($psi array) 0) ((mplus) n x))))
	 'grad)
;; patches for hyp.lisp 

;; Jacobi polynomial
(defun jacobpol (n a b x)
  (ftake '%jacobi_p n a b x))

;; 
;; Notice: ultraspherical(n,0,x) =/= chebyshev_t(n,x), so the conditional for v = 0 should 
;; likely be done somewhere in hyp.lisp, but we'll do it here.
(defun gegenpol (n v x)
  (if (eql v 0)
      (ftake '%chebyshev_t n x)
      (ftake '%ultraspherical n v x)))

;; Legendre polynomial
(defun legenpol (n x)
	(ftake '%legendre_p n x))

;; Chebyshev polynomial
(defun tchebypol (n x)
	(ftake '%chebyshev_t n x))

(defun hermpol (n arg)
  (let ((fact (inv (power 2 (div n 2))))
        (x (mul arg (inv (power 2 '((rat simp) 1 2))))))
    (mul fact (ftake '%hermite n x))))

;; Generalized Laguerre polynomial
(defun lagpol (n a arg)
	(ftake '%gen_laguerre n a arg))