;; Copyright (C) 2000, 2001, 2003, 2008, 2009, 2026 Barton Willis

#|
  This is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License,
  http://www.gnu.org/copyleft/gpl.html.

 This software has NO WARRANTY, not even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

Maxima code for evaluating orthogonal polynomials listed in Chapter 22 of Abramowitz and Stegun (A & S). 

Most functions use the two term recursion in the upward direction to evaluate these polynomials for both
symbolic and numeric arguments. The recursion has the form f(k+1) = p(k) f(k) + q(k) f(k-1). (Some might
might call this a three term recursion, I'll call it a two term recursion).

For the floating point (either binary64 or big float numbers), the code uses a dynamic running error to 
estimate the rounding error. Specifically it works like this: let f(k) be the true value and let 
fa(k) be the approximate value computed with floating point numbers.  Then

     f(k+1) = p(k) f(k) + q(k) f(k-1)
     fa(k+1) = p(k) ⊗ fa(k) ⊕ q(k) ⊗ fa(k-1),

where ⊕ is floating point addition and ⊗ is floating point multiplication. This code assumes
that ⊗ = *, so that all the rounding error is from addition and none from addition. This, of 
course is an approximation.
     
Using the rules of ⊕, there is ε(k), whose magnitude is bounded by the machine epsilon ε, such that 

     fa(k+1) = (p(k) fa(k) + q(k) fa(k-1)) (1 + ε(k)).

Now define E(k) = fa(k) - f(k). We have

    E(k+1) =  p(k) E(k) + q(k) E(k-1) + ε(k) (p(k) fa(k) + q(k) fa(k-1)),
           =  p(k) E(k) + q(k) E(k-1) + ε(k) fa(k+1) + O(ε^2).

Applying the triangle inequality gives

   |E(k+1)| ≤ |p(k) E(k)| + |q(k) E(k-1)| + ε |fa(k+1)| + O(ε^2).

Rescaling the error bound as |E(k)| =  ε 𝓔(k), we have

    𝓔(k+1) ≤ |p(k)| 𝓔(k) + |q(k)| 𝓔(k-1) + |fa(k+1)| + O(ε).

This is the rule we use to update 𝓔.

The function generic-two-term-recursion-running error returns the two values fa(n) and ε 𝓔(n). When 
the value of 𝓔(n) is sufficiently small, the process is done and we accept fa(n) as the value; if not 
the process is repeated with a smaller value for the machine epsilon. 

This is called a running error method. Think of it as a "poor man's" interval arithmetic. A proper
interval arithmetic would rack the rounding errors in all computations, not just the additions. 
Of course, including the rounding errors with ⊗ is possible.

Also, this code assumes that for the recursion f(k+1) = p(k) f(k) + q(k) f(k-1) that the coefficients
p(k) and q(k) are computed without any rounding error. Again, a proper interval method would also 
track these errors too.

Our measure of sufficiently small is 

   |𝓔(n)| <  max(1, |fa(n)|).

 Notes:

  (a) The model I used for ⊕ is incorrect for subnormal numbers.

  (b) We ignore the rounding error for multiplication. This could be fixed.

  I know what you are thinking:

  (a) Shouldn't the code conditionally use downward recursion for large n, small x, or ...
   
      Oh, maybe. But a great deal of reasonable inputs are modestly sized making the choice
      between directions possibly a toss-up. Plus, cases with complex parameters likely makes
      the decision between up or down recursion a bit difficult to decide. Finally even using 
      the better choice for the recursion direction, rounding errors and cancellation 
      still happen and need to be managed. I'm do not want to add this much complexity 
      to the code.

  (b) Instead of the running error, why not just use Kahan summation? 

      Kahan summation is a lovely method, but it does not transform an ill-conditioned sum into a 
      well-conditioned sum. That said, there might be opportunities to use it in this code. Plus 
      as far as I know, Kahan summation is really only useful for an accumulated sum, but the
      two-term recursion isn't of this form.

  (c) Doesn't Clenshaw summation eliminate all cancellation problems?

     No, I think it might be good for many cases, but not all. Again, I'm not sure that I want to add 
     this much complexity of choosing between multiple methods.

  (d) Why not just turn over all the numerical code to the hypergeometric code?

      This should work--I'm not sure about the trade-offs. 

  (e) Why not do floating point evaluation using nfloat and the exact symbolic values?

    Even for modest degrees, my experiments show that this method is painfully slow.
    Currently, code does this for assoc_legendre_q.

  (f) Isn't the running error just a crude estimate? It's not rigorous!

      It's an estimate that is based on the properties of floating point arithmetic. Sure, it's
      an estimate, but it's not crude. The estimate ignores the O(ε^2), the errors in computing 
      the coefficients, and the errors in multiplications. But at every step, the error is 
      over estimated and testing shows that the method is reliable--not sufficiently reliable to
      prove theorems, but it is pretty good.

  (g) Can't you assume that rounding errors are uniformly distributed independent random variables
      and get a much lower error estimate?

      Yes, you can make those assumptions, but they are not grounded in fact.

  (h) The polynomials XXX extend to negative degree and order, but this package doesn't extend
      the to negative degrees. Why?

      The answer isn't very interesting--it's a design choice based on focusing on what I suspect that
      most users need and on keeping the code compact. If you need to extend a function to negative
      degrees or the like, let me know--or even better do it yourself and share it.

  (i) For large `n`, shouldn't the code switch over to asymptotic series?

      Maybe, but it's a design choice to keep the code compact and focused on typical cases
      that users need.

|#

(in-package :maxima)

(defun orthopoly-default-simp (p x)
  "Default cleanup for orthogonal polynomials."
  ($ratsimp p x))

;; If you prefer a Horner representation:
(defun orthopoly-horner-simp (p x)
  ($horner p x))

;; Function applied to every symbolically generated polynomial.
(defun orthopoly-polynomial-simp (p x &optional (simp-fn #'orthopoly-default-simp))
  "Apply 'simp-fn' to 'p'. If 'simp-fn' is nil, return 'p' unchanged."
  (if simp-fn
      (funcall simp-fn p x)
    p))

;; Number of base 10 digits in a binary64 number (it is 15).
(defmvar *binary64-digits* (floor (* (float-digits 1.0d0) (log 2 10))))

;;; The function generic-two-term-recursion-running-error uses recursion to evaluate
;;; the orthogonal polynomials, but calling it properly requires a great deal of boilerplate.
;;; Here is a macro for calling generic-two-term-recursion-running-error
(defmacro define-two-term-numeric* (name lambda-list
                                        &key let f0 f1 p q)
  "Generalized numeric evaluator for orthogonal polynomials with
   arbitrary parameters. The lambda-list must begin with N and end
   with DIGITS.  All intermediate parameters are passed through and
   coerced to bigfloat on recursive restart."

  ;; Extract required positions
  (let* ((n-var      (first lambda-list))
         (digits-var (car (last lambda-list)))
         (other-vars (butlast (rest lambda-list)))   ; all except n and digits
         ;; Build ($bfloat ...) coercions for restart
         (bf-others  (mapcar (lambda (v) `($bfloat ,v)) other-vars)))
    
    `(defun ,name ,lambda-list
       (handler-case
           (let* (,@let
                  (eps (bigfloat::to (ftake 'mexpt 2 (- ,digits-var))))
                  (f0 ,f0)
                  (f1 ,f1)
                  (p  ,p)
                  (q  ,q))
             (multiple-value-bind (value err)
                 (bigfloat::generic-two-term-recursion-running-error
                  p q f0 f1 ,n-var)
               (cond ((bigfloat::relative-error-p value err eps)
                      (maxima::to value))
                     (t
                      ;; restart with doubled precision
                      (bind-fpprec (mul 2 $fpprec)
                        (,name ,n-var ,@bf-others ,digits-var))))))
         (arithmetic-error (c)
           (declare (ignore c))
           ;; restart with same precision
           (bind-fpprec $fpprec
             (,name ,n-var ,@bf-others ,digits-var)))))))

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
(setf (get '$unit_step 'sign-function) 'unit_step-sign-function)

;; antiderivative of unit_step
(putprop '%unit_step
  '((x) ((mtimes) ((rat) 1 2) ((mplus) x ((mabs) x)))) 'integral)

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

;;; simplifier for the Jacobi polynomials
(def-simplifier jacobi_p (n a b x)
  (cond
    ;; Numeric evaluation: all arguments are numeric (complex-number-p)
    ((and (integerp n)
          (complex-number-p a #'$numberp)
          (complex-number-p b #'$numberp)
          (complex-number-p x #'$numberp))
     (let* ((digits (get-digits x))
            (one (multiplicative-identity a b x)))
       (if one
           (orthopoly-number-coerce
             (jacobi_p-dispatch n a b x digits)
             one)
           (give-up))))

    ;; Symbolic case
    ((integerp n)
      (if (> n -1)
         (orthopoly-polynomial-simp (jacobi_p-symbolic n a b x) x)
         (give-up)))

    ;; reflection: jacobi_p(n,a,b,x) = (-1)^n * jacobi_p(n,b,a,-x); 
    ;; see DLMF http://dlmf.nist.gov/18.6.E1
    ((great (neg x) x)
     (mul (ftake 'mexpt -1 n) (ftake '%jacobi_p n b a (neg x))))

    ;; special value: jacobi_p(n,a,b,1) = pochhammer(a+1,n) / n!;
    ;; see DLMF http://dlmf.nist.gov/18.6.E1
    ((eql x 1)
     (div (ftake '$pochhammer (add a 1) n) (ftake 'mfactorial n)))

    ;; Otherwise, no simplification available
    (t
     (give-up))))

;; Derivatives of the Jacobi polynomials. 
(defgrad %jacobi_p ($n $a $b $x)
  nil
  nil
  nil
  #$$ (n*jacobi_p(n,a,b,x)*((-(2*n)-b-a)*x-b+a)+2*jacobi_p(n-1,a,b,x)*(n+a)*(n+b)*unit_step(n))/((2*n+b+a)*(1-x^2))$)

;;; For the Jacobi polynoimals, we need to special case negative integer parameters. The code
;;; jacobi_p-dispatch handles these special cases.
(defun jacobi_p-dispatch (n a b x digits)
  "Top-level dispatcher for Jacobi polynomials that special cases negative integer parameters."
  (let* ((neg-a (and (integerp a) (< a 0)))
         (neg-b (and (integerp b) (< b 0))))

    (cond

      ;; jacobi_p(negative integer, a, b, x) = 0
      ((< n 0) 0)

      ;; Case 1: No negative integer parameters--safe to call the upward recursion code
      ((and (not neg-a) (not neg-b))
       (jacobi_p-numeric n a b x digits))

      ;; Both a & b are negative integers:
      ;; jacobi_p(n,a,b,x) = jacobi_p(n+a+b,-a,-b,x)/((x-1)/2)^a ((x+1)/2)^b)
      ((and neg-a neg-b)
        (div
            (jacobi_p-numeric (add n a b) (neg a) (neg b) x digits)
            (mul
                (ftake 'mexpt (div (sub x 1) 2) a)
                (ftake 'mexpt (div (add x 1) 2) b))))

      ;; a is a negative integer:
      ;; jacobi_p(n,a,b,x) = gamma(n+a+1) gamma(n+b+1) jacobi_p(n+a,-a,b,x)/(gamma(n+1) gamma(n+a+b+1) ((x-1)/2)^a.
      (neg-a
        (mul
           (ftake '%gamma (add n a 1))
           (ftake '%gamma (add n b 1))
           (div 1 (ftake '%gamma (add n 1)))
           (div 1 (ftake '%gamma (add n a b 1)))
           (ftake 'mexpt (div (sub x 1) 2) (neg a))
           (jacobi_p-numeric (add n a) (neg a) b x digits)))

      ;; b is a negative integer:
      ;; jacobi_p(n,a,b,x) = (-1)^n jacobi_p(n,b,a,-x)
      (neg-b
       (mul 
        (ftake 'mexpt -1 n) 
        (jacobi_p-numeric n b a (neg x) digits)))

      (t nil))))

;;; Recursion for the Jacobi polynomials; see http://dlmf.nist.gov/18.9.E1 
(define-two-term-numeric* jacobi_p-numeric (n a b x digits)
  :let ((bf-a   (bigfloat::to a))
        (bf-b   (bigfloat::to b))
        (bf-x   (bigfloat::to x))
        (a+b    (bigfloat::+ bf-a bf-b))
        (a+b+1  (bigfloat::+ bf-a bf-b 1))
        (a+b+2  (bigfloat::+ bf-a bf-b 2))
        ;; a^2 - b^2
        (a2-b2  (bigfloat::- (bigfloat::* bf-a bf-a)
                             (bigfloat::* bf-b bf-b))))
  
  :f0 (bigfloat::to 1)

  :f1 (bigfloat::/
       (bigfloat::+
        (bigfloat::* (bigfloat::+ bf-a bf-b 2) bf-x)
        (bigfloat::- bf-a bf-b))
       2)

  :p #'(lambda (k)
         (let* ((bf-k (bigfloat::to k))
                (2k   (bigfloat::* 2 bf-k))
                (k+1  (bigfloat::+ bf-k 1))

                ;; Numerator:
                ;; (2k + a + b + 1)(a^2 - b^2)
                ;;   + x * pochhammer(2k + a + b, 3)
                (num  (bigfloat::+
                       (bigfloat::* (bigfloat::+ 2k a+b+1) a2-b2)
                       (bigfloat::* bf-x
                                    (bigfloat::+ 2k a+b)
                                    (bigfloat::+ 2k a+b+1)
                                    (bigfloat::+ 2k a+b+2))))

                ;; Denominator:
                ;; 2 (k + 1)(k + a + b + 1)(2k + a + b)
                (den  (bigfloat::* 2
                                   k+1
                                   (bigfloat::+ bf-k a+b+1)
                                   (bigfloat::+ 2k a+b))))
           (bigfloat::/ num den)))

  :q #'(lambda (k)
         (let* ((bf-k (bigfloat::to k))
                (2k   (bigfloat::* 2 bf-k))
                (k+1  (bigfloat::+ bf-k 1))

                ;; Numerator:
                ;; -2 (k + a)(k + b)(2k + a + b + 2)
                (num  (bigfloat::* -2
                                   (bigfloat::+ bf-k bf-a)
                                   (bigfloat::+ bf-k bf-b)
                                   (bigfloat::+ 2k a+b+2)))

                ;; Denominator:
                ;; 2 (k + 1)(k + a + b + 1)(2k + a + b)
                (den  (bigfloat::* 2
                                   k+1
                                   (bigfloat::+ bf-k a+b+1)
                                   (bigfloat::+ 2k a+b))))
           (bigfloat::/ num den))))

;; To avoid the complications for negative integer parameters, we'll use explict summation for the
;; Jacobi polynomials: see http://dlmf.nist.gov/18.5.E8 

;; Careful: when x=+/-1, the k=0 or k=n terms can involve a factor of the form 0^0. To avoid this, 
;; we'll special case the k=0 & k=n terms. The speed penalty for these check for every loop counter
;; is, I think, insufficient to justify peeling these two terms out of the loop.
(defun jacobi_p-symbolic (n a b x)
  (let ((s 0))
		(dotimes (k (+ 1 n))
			(setq s 
			      (add s
			         (mul
                 (ftake '%binomial (add n a) k)
			           (ftake '%binomial (add n b) (sub n k))
                 (if (eql n k) 1 (ftake 'mexpt (div (sub x 1) 2) (sub n k)))
                  (if (eql k 0) 1 (ftake 'mexpt (div (add x 1) 2) k))))))
	(orthopoly-polynomial-simp s x)))

;; See A&S 22.5.46, page 779.
(def-simplifier ultraspherical (n a x)
	(cond ((and (integerp n) (complex-number-p a #'$numberp) (complex-number-p x #'$numberp))
            (let* ((digits (get-digits x))
		               (one (multiplicative-identity a x)))
			(if one 
			    (orthopoly-number-coerce (ultraspherical-numeric n a x digits) one)
				  (give-up))))

		  ((integerp n)
        (if (< n 0)
           (give-up)
		       (orthopoly-polynomial-simp (ultraspherical-symbolic n a x) x)))

		((great (neg x) x)
		 (mul (ftake 'mexpt -1 n) (ftake '%ultraspherical n a (neg x))))

        ((eql x 1)
	      (div (ftake '$pochhammer (mul 2 a) n) (ftake 'mfactorial n)))

        ;; see http://dlmf.nist.gov/18.7.E2 & http://dlmf.nist.gov/18.7.E3
		((and (eql a 0) ($featurep n '$integer) (eq t (mgqp n 0)))
			(mul
			    (div
				    (ftake '$pochhammer 0 n)
					(ftake 'mfactorial n))
			     (ftake '%chebyshev_t n x))) 

		(t (give-up))))

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
          (t (generic-two-term-recursion-symbolic p q f0 f1 n)))))
		  
(define-two-term-numeric* ultraspherical-numeric (n lam x digits)
  :let  ((bf-x (bigfloat::to x))
         (bf-lam (bigfloat::to lam))
         (2lam (bigfloat::* (bigfloat::to 2) bf-lam))
         (2lam-1 (bigfloat::- 2lam (bigfloat::to 1))))

  :f0 (bigfloat::to 1)
  :f1 (bigfloat::* (bigfloat::to 2) (bigfloat::to lam) bf-x)

  :p #'(lambda (k)
                    (let* ((k+1 (bigfloat::+ k 1))
                           ;; Numerator: 2(k + lam)x
                           (num (bigfloat::* (bigfloat::to 2) (bigfloat::+ k bf-lam) bf-x))
                           ;; Denominator: k + 1
                           (den k+1))
                      (bigfloat::/ num den)))
         
  :q #'(lambda (k)
                    (let* ((k+1 (bigfloat::+ k 1))
                           ;; Numerator: -(k + 2lam - 1)
                           (num (bigfloat::- (bigfloat::+ k 2lam-1)))
                           ;; Denominator: k + 1
                           (den k+1))
                      (bigfloat::/ num den))))

(def-simplifier chebyshev_t (n x)
  (cond ((and (integerp n) (complex-number-p x #'$numberp))
            (let* ((digits (get-digits x))
		               (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (chebyshev_t-numeric n x digits) one)
				(give-up))))

		  ((integerp n)
        (if (< n 0)
           (give-up)
		       (orthopoly-polynomial-simp (chebyshev_t-symbolic n x) x)))

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
          (t (generic-two-term-recursion-symbolic p q f0 f1 n)))))

(define-two-term-numeric* chebyshev_t-numeric (n x digits)
   :let ((bf-x (bigfloat::to x)))
    :f0 (bigfloat::to 1)
    :f1 bf-x
    :p #'(lambda (k) (declare (ignore k)) (bigfloat::* 2 bf-x))
    :q #'(lambda (k) (declare (ignore k)) (bigfloat::to -1)))
        
(def-simplifier chebyshev_u (n x)
   (cond ((and (integerp n) (complex-number-p x #'$numberp))
             (let* ((digits (get-digits x))
		                (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (chebyshev_u-numeric n x digits) one)
				(give-up))))

		  ((integerp n)
        (if (< n 0)
           (give-up)
		       (chebyshev_u-symbolic n x)))

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
          (t (generic-two-term-recursion-symbolic p q f0 f1 n)))))

(define-two-term-numeric* chebyshev_u-numeric (n x digits)
  :let  ((bf-x (bigfloat::to x)))
  :f0 (bigfloat::to 1)
  :f1 (bigfloat::* 2 bf-x)
             
  :p #'(lambda (k) (declare (ignore k)) (bigfloat::* 2 bf-x))
  :q #'(lambda (k) (declare (ignore k)) (bigfloat::to -1)))

(def-simplifier legendre_p (n x)
   (cond ((and (integerp n) (complex-number-p x #'$numberp)) ;evaluate numerically
            (let* ((digits (get-digits x))
		               (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (legendre_p-numeric n x digits) one)
				(give-up))))

		  ((integerp n)
          (if (< n 0)
              (give-up)
              (orthopoly-default-simp (legendre-p-symbolic n x) x)))

		(t (give-up))))

(define-two-term-numeric* legendre_p-numeric (n x digits)
  :let ((bf-x (bigfloat::to x))
         (one (bigfloat::to 1)))

  :f0 one
  :f1 bf-x
  :p #'(lambda (kk)
          (let ((k (bigfloat::to kk)))
                (bigfloat::/ (bigfloat::* (bigfloat::+ (bigfloat::* 2 k) 1) bf-x) (bigfloat::+ k 1))))
  :q #'(lambda (kk) 
          (let ((k (bigfloat::to kk))) 
                (bigfloat::/ k (bigfloat::+ k one)))))

(defun legendre-p-symbolic (n x)
    (let* ((f0 1)
		       (f1 x)
           (p #'(lambda (k) (div (mul (add (mul 2 k) 1) x) (add k 1)))) ; (2k+1)x/(k+1) 
           (q #'(lambda (k) (mul -1 (div k (add k 1))))))
	 (generic-two-term-recursion-symbolic p q f0 f1 n)))

(defun get-digits (x)
  (if (floatp x)
			(- *binary64-digits* 2)
			(- $fpprec 2)))

(def-simplifier assoc_legendre_p (l m x)
  (cond ((and (integerp l) (integerp m) (<= (abs m) l) (complex-number-p x #'$numberp))
           (let* ((digits (get-digits x))
		        (one (multiplicative-identity x)))
		    	(if one 
			        (orthopoly-number-coerce (assoc_legendre_p-numeric l m x digits) one)
				      (give-up))))

        ;; assoc_legendre_p(l,m,x) = assoc_legendre_p(-l-1,m,x)
        ((and (integerp l) (< l 0))
          (ftake '%assoc_legendre_p (sub (- l) 1) m x))

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
        ;; symbolic case
        ((integerp n)
           (if (< n 0)
		         (give-up)
		         (orthopoly-polynomial-simp (hermite-symbolic n x) x)))
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
  #$$ 2*n*herite(n-1,x)$)

(define-two-term-numeric* hermite-numeric (n x digits)
  :let  ((bf-x  (bigfloat::to x))
         (bf-2x (bigfloat::* 2 bf-x)))
  :f0   (bigfloat::to 1)
  :f1   bf-2x
  :p    (lambda (k) (declare (ignore k)) bf-2x)
  :q    (lambda (k) (bigfloat::* -2 k)))

(defun hermite-symbolic (n x)
    (let* ((f0 1)
		       (f1 (mul 2 x))
           (p #'(lambda (k) (declare (ignore k)) (mul 2 x)))
           (q #'(lambda (k) (mul -2 k))))
		    (generic-two-term-recursion-symbolic p q f0 f1 n)))

(def-simplifier gen_laguerre (n a x)
	(cond ((and (integerp n) (complex-number-p a #'$numberp) (complex-number-p x #'$numberp)
              (let* ((digits (get-digits x))      
		                 (one (multiplicative-identity a x)))
			(if one 
			    (orthopoly-number-coerce (gen_laguerre-numeric n a x digits) one)
				(give-up)))))
          ;; symbolic case 
		  ((integerp n)
         (if (< n 0)
            (give-up)
            (orthopoly-default-simp (gen_laguerre-symbolic n a x) x)))

      ;; value for x=0 (see https://en.wikipedia.org/wiki/Laguerre_polynomials)
		  ((and (eql x 0) ($featurep n '$integer))
		   (ftake '%binomial (add n a) n))
          ;; nothing known--noun form return
 		  (t (give-up))))

(def-simplifier laguerre (n x)
  (cond ((and (integerp n) (complex-number-p x #'$numberp))
          (let* ((digits (get-digits x)) 
		             (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (laguerre-numeric n x digits) one)
				(give-up))))
          ;; symbolic case 
		  ((integerp n)
           (if (< n 0)
              (give-up)
              (orthopoly-polynomial-simp (laguerre-symbolic n x) x)))
          ;; nothing known--noun form return
 		  (t (give-up))))

(defun laguerre-numeric (n x digits)
   (gen_laguerre-numeric n 0 x digits))

(defun laguerre-symbolic (n  x)
  (gen_laguerre-symbolic n 0 x))

(define-two-term-numeric* gen_laguerre-numeric (n a x digits)
  :let ((bf-a (bigfloat::to a))
        (bf-x (bigfloat::to x))
        ;; Pre-cache static parameter term
        (a+1 (bigfloat::+ bf-a 1)))
  
  :f0 (bigfloat::to 1)
  :f1 (bigfloat::- (bigfloat::+ bf-a 1) bf-x)
             
  :p #'(lambda (k)
                    (let* ((bf-k (bigfloat::to k))
                           (k+1 (bigfloat::+ bf-k 1))
                           ;; Numerator: 2k + a + 1 - x
                           (num (bigfloat::- (bigfloat::+ (bigfloat::* 2 bf-k) a+1) bf-x)))
                      (bigfloat::/ num k+1)))
             
  :q #'(lambda (k)
                    (let* ((bf-k (bigfloat::to k))
                           (k+1 (bigfloat::+ bf-k 1))
                           ;; Numerator: -(k + a)
                           (num (bigfloat::- (bigfloat::+ bf-k bf-a))))
                      (bigfloat::/ num k+1))))
        

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
          (t (generic-two-term-recursion-symbolic p q f0 f1 n)))))

(def-simplifier spherical_hankel1 (n x)
	(cond ((and (integerp n) (complex-number-p x #'$numberp))
	        (spherical_hankel1-symbolic n x))

		  ((and (integerp n) (complex-number-p x #'$numberp))
            (let* ((digits (get-digits x))
		               (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (spherical_hankel1-numeric n x digits) one)
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
		 (generic-two-term-recursion-symbolic f0 f1 p q n)))

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
(define-two-term-numeric* spherical_hankel1-numeric (n x digits)
  :let ((bf-x (bigfloat::to x)))
	:f0 (bigfloat::order-zero-spherical_hankel1 bf-x)
	:f1 (bigfloat::order-one-spherical_hankel1 bf-x)
  :p #'(lambda (k) (bigfloat::/ (+ (* 2 k) 1) bf-x))
  :q #'(lambda (k) (declare (ignore k)) (bigfloat::to -1)))

(def-simplifier spherical_hankel2 (n x)
  (give-up))

(def-simplifier spherical_bessel_j (n x)
    (cond ((and (integerp n) (complex-number-p x #'$numberp))
             (let* ((digits (get-digits x))
		                (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (spherical_bessel_j-numeric n x digits) one)
				(give-up))))

		  ((integerp n)	
		    (spherical_bessel_j-symbolic n x))

		  ((great (neg x) x)
		  	(mul (ftake 'mexpt -1 n) (ftake '%spherical_bessel_j n x)))
		
		  (t (give-up))))
		    
(define-two-term-numeric* spherical_bessel_j-numeric (n x digits)
  :let ((bf-x   (bigfloat::to x))
        (bf-one (bigfloat::to 1))
        (bf-two (bigfloat::to 2)))
      
  :f0 (bigfloat::/ (bigfloat::sin bf-x) bf-x)

  :f1 (bigfloat::- (bigfloat::/
                   (bigfloat::sin bf-x)
                   (bigfloat::expt bf-x 2))
                  (bigfloat::/
                   (bigfloat::cos bf-x)
                   bf-x))

             ;; p(k) = (2k+1)/x
  :p #'(lambda (k)
                    (bigfloat::/
                     (bigfloat::+
                      (bigfloat::* bf-two (bigfloat::to k))
                      bf-one)
                     bf-x))
  :q #'(lambda (k) (declare (ignore k)) (bigfloat::to -1)))

(defun spherical_bessel_j-symbolic (n x)
  "Symbolic spherical Bessel j_n(x) using the standard two-term recurrence.
   j_0(x) = sin(x)/x
   j_1(x) = sin(x)/x^2 - cos(x)/x
   j_{n+1}(x) = ((2n+1)/x) * j_n(x) - j_{n-1}(x)."
  (let* ((f0 (div (ftake '%sin x) x))
         (f1 (add (div (ftake '%sin x) (ftake 'mexpt x 2))
                  (mul -1 (div (ftake '%cos x) x))))
         ;; p(k) = ((2k+1)/x)
         (p #'(lambda (k) (div (add (mul 2 k) 1) x)))
         ;; q(k) = -1
         (q #'(lambda (k) (declare (ignore k)) -1)))
    (generic-two-term-recursion-symbolic p q f0 f1 n)))
	    
;; For analytic continuation, see A&S 10.1.35.
 
(defun $spherical_bessel_y (n x)
   (declare (ignore n x))
   (merror "spherical_bessel_y"))

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

(defun generic-two-term-recursion-symbolic (p q f0 f1 n)
  (cond ((eql n 0)  f0)
        ((eql n 1)  f1)
        (t
          (let ((k 1) (f2))
            (while (< k n)
               (setq f2 (add (mul (funcall p k) f1) (mul (funcall q k) f0)))
               (setq f0 f1
                   f1 f2
                   k (+ 1 k)))
          f1))))

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

(defun componentwise-abs (x)
"Return the componentwise absolute value of a real or complex number.
   For a real input, this is simply (abs x). For a complex input z = a + i b, 
   this returns the complex value abs(a) + i abs(b)."
  (complex (abs (realpart x)) (abs (imagpart x))))

(defun generic-two-term-recursion-running-error (p q f0 f1 n)
  "Evaluate the recurrence forward while tracking an absolute running error bound
   using the IEEE‑754 real floating‑point model."
  (cond ((eql n 0) (values f0 0))
        ((eql n 1) (values f1 0))
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

(def-simplifier legendre_q (n x)
  (cond ((and (integerp n) (> n -1) (complex-number-p x #'$numberp))
          (let* ((digits (get-digits x)) 
		             (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (legendre_q-numeric n x digits) one)
				(give-up))))
		((and (integerp n) (> n -1))
		   (orthopoly-polynomial-simp (legendre_q-symbolic n x) x))
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

(defun $assoc_legendre_q (n m x)
  (ftake '%assoc_legendre_q n m x))
  
(def-simplifier assoc_legendre_q (n m x)
  (cond ((and (integerp n) (integerp m) (complex-number-p x #'$numberp) (> n -1) (<= (abs m) n))
           (let* ((digits (get-digits x))
                  (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (assoc_legendre_q-numeric n m x digits) one)
				(give-up))))

      ((and (integerp m) (> 0 m) (integerp n))
         (div (mul
                (ftake 'mexpt -1 (- m))
                (ftake 'mfactorial (add n m))
                (ftake '%assoc_legendre_q n (- m) x))
              (ftake 'mfactorial (sub n m))))

      ((and (integerp n) (integerp m) (> n -1) (> m -1))
       (assoc_legendre_q-symbolic n m x))

      ((eql m 0)
        (ftake '%legendre_q n x))

      (t (give-up))))

(defun assoc_legendre_q-symbolic (n m x)
  (let* ((g (gensym))
         (f ($diff (ftake '%legendre_q n g) g m)))
         
    (orthopoly-polynomial-simp 
        (maxima-substitute x g
           (mul (ftake 'mexpt -1 m)
                (ftake 'mexpt (sub 1 (mul x x)) (div m 2))
                f)) x)))

(defun assoc_legendre_q-numeric (n m x digits)
    (let* ((g (gensym))
           (f (assoc_legendre_q-symbolic n m g)))
      (nfloat f (ftake 'mlist (ftake 'mequal g x)) digits $max_fpprec)))
      
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

(defgrad $pochhammer ($x $n)
  ;; ∂/∂x
  #$$ pochhammer(x,n)*psi[0](x+n) $
  ;; ∂/∂n
  #$$ pochhammer(x,n)*(psi[0](x+n) - psi[0](x)) $)

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


;;; ======================================================================
;;;  orthopoly-recursions.lisp
;;;  Unified recursion registry for orthogonal polynomials and related
;;;  special functions in Maxima.
;;;
;;;  Provides:
;;;    • Reader macro #$$ … $ for lambda forms
;;;    • Hash table storing recursion lambdas
;;;    • Registration and lookup functions
;;;    • Recursions for all functions listed in user documentation
;;; ======================================================================

(in-package :maxima)

(defparameter *orthopoly-recursion-table*
  (make-hash-table :test #'eq :size 128))

(defun register-orthopoly-recursion (name lambda-form)
  (setf (gethash name *orthopoly-recursion-table*) lambda-form)
  name)

(defun orthopoly-recursion (name)
  (or (gethash name *orthopoly-recursion-table*)
      (error "No recursion registered for ~A" name)))

(register-orthopoly-recursion
 '%hermite
 #$$ lambda([n,x],hermite(n+1,x) = 2*x*hermite(n,x) - 2*n*hermite(n-1,x)) $)

(register-orthopoly-recursion
 '%legendre_p
 #$$ lambda([n,x], (n+1)*legendre_p(n+1,x) = (2*n+1)*x*legendre_p(n,x) - n*legendre_p(n-1,x)) $)

(register-orthopoly-recursion
 '%legendre_q
 #$$ lambda([n,x], (n+1)*legendre_q(n+1,x) = (2*n+1)*x*legendre_q(n,x) - n*legendre_q(n-1,x)) $)

(register-orthopoly-recursion
 '%assoc_legendre_p
 #$$ lambda([n,m,x], (n-m+1)*assoc_legendre_p(n+1,m,x) = (2*n+1)*x*assoc_legendre_p(n,m,x)
          - (n+m)*assoc_legendre_p(n-1,m,x)) $)

(register-orthopoly-recursion
 '%assoc_legendre_q
 #$$ lambda([n,m,x], (n-m+1)*assoc_legendre_q(n+1,m,x)  = (2*n+1)*x*assoc_legendre_q(n,m,x)
          - (n+m)*assoc_legendre_q(n-1,m,x)) $)

(register-orthopoly-recursion
 '%chebyshev_t
 #$$ lambda([n,x],  chebyshev_t(n+1,x) = 2*x*chebyshev_t(n,x) - chebyshev_t(n-1,x)) $)

(register-orthopoly-recursion
 '%chebyshev_u
 #$$ lambda([n,x], chebyshev_u(n+1,x) = 2*x*chebyshev_u(n,x) - chebyshev_u(n-1,x)) $)

(register-orthopoly-recursion
 '%ultraspherical
 #$$ lambda([n,lambda,x], (n+1)*ultraspherical(n+1,lambda,x)
        = 2*(n+lambda)*x*ultraspherical(n,lambda,x)
          - (n+2*lambda-1)*ultraspherical(n-1,lambda,x)) $)

(register-orthopoly-recursion
 '%laguerre
 #$$ lambda([n,a,x], (n+1)*laguerre(n+1,a,x) = (2*n + a + 1 - x)*laguerre(n,a,x) - (n + a)*laguerre(n-1,a,x)) $)

(register-orthopoly-recursion
 '%gen_laguerre
 #$$ lambda([n,a,x],
      (n+1)*gen_laguerre(n+1,a,x)
        = (2*n + a + 1 - x)*gen_laguerre(n,a,x)
          - (n + a)*gen_laguerre(n-1,a,x)) $)

(register-orthopoly-recursion
 '%jacobi_p
 #$$ lambda([n,a,b,x],
      2*(n+1)*(n+a+b+1)*jacobi_p(n+1,a,b,x)
        = (2*n+a+b+1)
            * ((2*n+a+b+2)*x + a - b)
            * jacobi_p(n,a,b,x)
          - 2*(n+a)*(n+b)*(2*n+a+b+2)
            * jacobi_p(n-1,a,b,x)) $)

(register-orthopoly-recursion
 '%spherical_bessel_j
 #$$ lambda([n,x],
      spherical_bessel_j(n+1,x)
        = (2*n+1)/x * spherical_bessel_j(n,x)
          - spherical_bessel_j(n-1,x)) $)

(register-orthopoly-recursion
 '%spherical_bessel_y
 #$$ lambda([n,x],
      spherical_bessel_y(n+1,x)
        = (2*n+1)/x * spherical_bessel_y(n,x)
          - spherical_bessel_y(n-1,x)) $)

(register-orthopoly-recursion
 '%spherical_hankel1
 #$$ lambda([n,x],
      spherical_hankel1(n+1,x)
        = (2*n+1)/x * spherical_hankel1(n,x)
          - spherical_hankel1(n-1,x)) $)

(register-orthopoly-recursion
 '%spherical_hankel2
 #$$ lambda([n,x],
      spherical_hankel2(n+1,x)
        = (2*n+1)/x * spherical_hankel2(n,x)
          - spherical_hankel2(n-1,x)) $)

(register-orthopoly-recursion
 '%spherical_harmonic
 #$$ lambda([l,m,x],
      spherical_harmonic(l+1,m,x)
        = ((2*l+1)/sqrt(l^2 - m^2))*x*spherical_harmonic(l,m,x)
          - sqrt(((l-1)^2 - m^2)/(l^2 - m^2))
            * spherical_harmonic(l-1,m,x)) $)

(defmfun $orthopoly_recursion (name)
    (or (gethash name *orthopoly-recursion-table*) (merror "No recursion registered for ~M" name)))

;;; and the weights too:

(defparameter *orthopoly-weight-table*
  (make-hash-table :test #'eq :size 128))

(defun register-orthopoly-weight (name lambda-form)
  (setf (gethash name *orthopoly-weight-table*) lambda-form)
  name)

(defun orthopoly_weight (name)
  (or (gethash name *orthopoly-weight-table*)
      (error "No weight registered for ~A" name)))

;;; ----------------------------------------------------------------------
;;; USER-LEVEL FUNCTIONS
;;; ----------------------------------------------------------------------

(defmfun orthopoly_register_weight (name lambda_expr)
  (let* ((lname (mfuncall '$symbol name))
         (lform lambda_expr))
    (register-orthopoly-weight lname lform)
    lname))

(defmfun $orthopoly_weight (name)
  (or (gethash lname *orthopoly-weight-table*)
        (merror "No weight registered for ~M" name)))

(register-orthopoly-weight
 '%hermite
 #$$ lambda([x], [exp(-x^2), -inf, inf]) $)

(register-orthopoly-weight
 '%legendre_p
 #$$ lambda([x], [1, -1, 1]) $)

(register-orthopoly-weight
 '%legendre_q
 #$$ lambda([x], [1, -1, 1]) $)

(register-orthopoly-weight
 '%assoc_legendre_p
 #$$ lambda([x], [1, -1, 1]) $)

(register-orthopoly-weight
 '%assoc_legendre_q
 #$$ lambda([x], [1, -1, 1]) $)

(register-orthopoly-weight
 '%chebyshev_t
 #$$ lambda([x], [1/sqrt(1-x^2), -1, 1]) $)

(register-orthopoly-weight
 '%chebyshev_u
 #$$ lambda([x], [sqrt(1-x^2), -1, 1]) $)

(register-orthopoly-weight
 '%ultraspherical
 #$$ lambda([x,lambda], [(1-x^2)^(lambda-1/2), -1, 1]) $)

(register-orthopoly-weight
 '%laguerre
 #$$ lambda([x,a], [x^a * exp(-x), 0, inf]) $)

(register-orthopoly-weight
 '%gen_laguerre
 #$$ lambda([x,a], [x^a * exp(-x), 0, inf]) $)

(register-orthopoly-weight
 '%jacobi_p
 #$$ lambda([x,a,b], [(1-x)^a * (1+x)^b, -1, 1]) $)

(register-orthopoly-weight
 '%spherical_bessel_j
 #$$ lambda([x], [x^2, 0, inf]) $)

(register-orthopoly-weight
 '%spherical_bessel_y
 #$$ lambda([x], [x^2, 0, inf]) $)

(register-orthopoly-weight
 '%spherical_hankel1
 #$$ lambda([x], [x^2, 0, inf]) $)

(register-orthopoly-weight
 '%spherical_hankel2
 #$$ lambda([x], [x^2, 0, inf]) $)

(register-orthopoly-weight
 '%spherical_harmonic
 #$$ lambda([theta,phi], [sin(theta), [0,pi], [0,2*pi]]) $)

;;; Gradient definitions for orthogonal polynomials
(defgrad %jacobi_p ($n $a $b $x)
  nil nil nil
  #$$ (n*jacobi_p(n,a,b,x)*((-(2*n)-b-a)*x-b+a)
      +2*jacobi_p(n-1,a,b,x)*(n+a)*(n+b)*unit_step(n))
      /((2*n+b+a)*(1-x^2)) $)

(defgrad %ultraspherical ($n $lambda $x)
  nil nil
  #$$ (2*lambda*ultraspherical(n-1,lambda+1,x)
      -n*x*ultraspherical(n,lambda,x))
      /(1-x^2) $)

(defgrad %chebyshev_t ($n $x)
  nil
  #$$ n*chebyshev_u(n-1,x) $)

(defgrad %chebyshev_u ($n $x)
  nil
  #$$ ((n+1)*chebyshev_t(n+1,x) - x*chebyshev_u(n,x))
      /(1-x^2) $)

(defgrad %legendre_p ($n $x)
  nil
  #$$ (n*(legendre_p(n-1,x) - x*legendre_p(n,x)))/(1-x^2) $)

(defgrad %legendre_q ($n $x)
  nil
  #$$ (n*(legendre_q(n-1,x) - x*legendre_q(n,x)))
      /(1-x^2) $)

(defgrad %assoc_legendre_p ($n $m $x)
  nil 
  nil
  #$$ (1/(1-x^2))*(n*x*assoc_legendre_p(n,m,x) - (n+m)*assoc_legendre_p(n-1,m,x)) $)

(defgrad %assoc_legendre_q ($n $m $x)
  nil 
  nil
  #$$ (1/(1-x^2))*(n*x*assoc_legendre_q(n,m,x) - (n+m)*assoc_legendre_q(n-1,m,x)) $)

(defgrad %laguerre ($n $a $x)
  nil 
  nil
  #$$ -laguerre(n-1,a+1,x) $)

(defgrad %gen_laguerre ($n $a $x)
  nil 
  nil
  #$$ -gen_laguerre(n-1,a+1,x) $)

(defgrad %hermite ($n $x)
  nil
  #$$ 2*n*hermite(n-1,x) $)

(defgrad %spherical_bessel_j ($n $x)
  nil
  #$$ spherical_bessel_j(n-1,x)
      - (n+1)/x * spherical_bessel_j(n,x) $)

(defgrad %spherical_bessel_y ($n $x)
  nil
  #$$ spherical_bessel_y(n-1,x)
      - (n+1)/x * spherical_bessel_y(n,x) $)

(defgrad %spherical_hankel1 ($n $x)
  nil
  #$$ spherical_hankel1(n-1,x)
      - (n+1)/x * spherical_hankel1(n,x) $)

(defgrad %spherical_hankel2 ($n $x)
  nil
  #$$ spherical_hankel2(n-1,x)
      - (n+1)/x * spherical_hankel2(n,x) $)

(defgrad %spherical_harmonic ($l $m $theta $phi)
  nil 
  nil 
  #$$ (m*cos(theta)/sin(theta))*spherical_harmonic(l,m,theta,phi)
      - sqrt((l-m)*(l+m+1))*spherical_harmonic(l,m+1,theta,phi) $
  #$$ m*spherical_harmonic(l,m,theta,phi)/sin(theta)$)

