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

(defun generic-two-term-recursion-running-error (p q f0 f1 n)
  "Evaluate the recurrence forward while tracking an absolute running error bound
   using the IEEE‑754 real floating‑point model."
  (cond ((eql n 0) f0)
        ((eql n 1) f1)
        (t
  (let* (;; absolute error bounds
         (e0 0)
         (e1 0)
         (k 1))

     (maxima::while (< k n)
      (let* ((a (funcall p k))
             (b (funcall q k))
             (f2 (+ (* a f1) (* b f0)))
             (e2 (+ (abs (* a e1)) (abs (* b e0)) (abs f2))))
        ;; update state
        (setq k (+ 1 k)
              f0 f1
              f1 f2
              e0 e1
              e1 e2)))
    (values f1 (* (epsilon f1) e1))))))

(in-package :maxima)

(defmvar *binary64-digits* (floor (* (float-digits 1.0d0) (log 2 10))))

(defun get-digits (x)
  (if (floatp x)
			(- *binary64-digits* 2)
			(- $fpprec 2)))

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

(defun orthopoly-number-coerce (x one)
  "Coerce the number `x` to the numeric type indicated by `one`.
   If `one` is an Maxima ratnump number, return an exact rationalized version of `x`.
   If `one` is a float, convert `x` to an IEEE float. Otherwise convert X 
   to a bigfloat."
	(cond (($ratnump one) ($rationalize x))
	      ((floatp one) ($float x))
		    (t ($bfloat x))))


;;; Simplifier for the Hermite polynomial H_n, not He_n; see DLMF Table Table 18.3.1. 
;;; (https://dlmf.nist.gov/18.3) For the recusion, see DLMF Table http://dlmf.nist.gov/18.9.T1. 
;;; For special values, see DLMF Table http://dlmf.nist.gov/18.6.i
(def-simplifier hermite (n x)
  (cond ((and (integerp n) (>= n 0) (complex-number-p x #'$numberp)) ;evaluate numerically
           (let* ((digits (get-digits x))
		        (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (hermite-numeric n x digits) one)
				(give-up))))
        ;; symbolic case call generic-two-term-recursion-symbolic
        ;((integerp n)
        ;   (if (< n 0)
;(give-up)
		 ;   (hermite-symbolic n x)))
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



(defun hermite-numeric (n x digits)
      (let* ((bf-x  (bigfloat::to x))
             (bf-2x (bigfloat::* 2 bf-x))
             (eps   (bigfloat::to (ftake 'mexpt 10 (- digits))))
             (f0    (bigfloat::to 1))
             (f1    bf-2x)
             (p     (lambda (k) (declare (ignore k)) bf-2x))
             (q     (lambda (k) (bigfloat::* -2 k))))
        (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error  p q f0 f1 n)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (hermite-numeric n ($bfloat x) digits))))))

