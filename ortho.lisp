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
might call this a three term recursion, but I will call it a two term recursion).

For floating point (either binary64 or big float numbers) evaluation, the code uses a dynamic running error to 
estimate the rounding error. Specifically it works like this: let f(k) be the true value and let 
fa(k) be the approximate value computed with floating point numbers.  Then

     f(k+1) = p(k) f(k) + q(k) f(k-1)
     fa(k+1) = p(k) ⊗ fa(k) ⊕ q(k) ⊗ fa(k-1),

where ⊕ is floating point addition and ⊗ is floating point multiplication. This code assumes
that ⊗ = *, so that all the rounding error is from addition and none from addition. This is an approximation.
     
Using the rules of ⊕, there is ε(k), whose magnitude is bounded by the machine epsilon ε, such that 

     fa(k+1) = (p(k) fa(k) + q(k) fa(k-1)) (1 + ε(k)).

Now define E(k) = fa(k) - f(k). We have

    E(k+1) =  p(k) E(k) + q(k) E(k-1) + ε(k) (p(k) fa(k) + q(k) fa(k-1)),
           =  p(k) E(k) + q(k) E(k-1) + ε(k) fa(k+1) + O(ε^2).

Applying the triangle inequality gives

   |E(k+1)| ≤ |p(k) E(k)| + |q(k) E(k-1)| + ε |fa(k+1)| + O(ε^2).

Rescaling the error bound as |E(k)| =  ε 𝓔(k), we have

    𝓔(k+1) ≤ |p(k)| 𝓔(k) + |q(k)| 𝓔(k-1) + |fa(k+1)| + O(ε).

Dropping the O(ε), this is the rule we use to update 𝓔.

The function generic-two-term-recursion-running error returns the two values fa(n) and ε 𝓔(n). When 
the value of 𝓔(n) is sufficiently small, the process is done and we accept fa(n) as the value; if not 
the process is repeated with a smaller value for the machine epsilon. 

This is called a running error method. Think of it as a "poor man's" interval arithmetic. A proper
interval arithmetic would track the rounding errors in all computations, not just the additions. 
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
   
      Maybe. But a great deal of reasonable inputs are modestly sized making the choice
      between directions possibly a toss-up. Plus, cases with complex parameters likely makes
      the decision between up or down recursion difficult to decide. Finally even using 
      the better choice for the recursion direction, rounding errors and cancellation 
      still happen and need to be managed. I'm do not want to add this much complexity 
      to the code.

  (b) Instead of the running error, why not just use Kahan summation on a series representation?

      Kahan summation is a lovely method, but it does not transform an ill-conditioned sum into a 
      well-conditioned sum. And as far as I know, Kahan summation is really only useful for an 
      accumulated sum, but the two-term recursion isn't of this form.

  (c) Why not just turn over all the numerical code to the hypergeometric code?

      I'm not sure about the trade-offs. Depending on parameters, I think that some of the functions 
      need to be choose between different hypergeometric  representations--this adds complexity to the code,
      plus some of the overall factors for the hypergeometric are quotients that might needlessly 
      overflow unless tricky methods are used. The two term recursions are simple.

  (d) Why not do floating point evaluation using nfloat on the exact symbolic values?

    Even for modest degrees, my experiments show that this method is painfully slow.

  (e) Isn't the running error just a crude estimate? It's not rigorous!

      It's an estimate that is based on the properties of floating point arithmetic. Sure, it's
      an estimate, but it's not crude. The estimate ignores the O(ε^2), the errors in computing 
      the coefficients, and the errors in multiplications. But at every step, the error is 
      over estimated and testing shows that the method is reliable--not sufficiently reliable to
      prove theorems, but it is pretty good.

  (f) Can't you assume that rounding errors are uniformly distributed independent random variables
      and get a much lower error estimate?

      Yes, you can make those assumptions, but they are not grounded in fact.

  (g) The polynomials XXX extend to negative degree and order, but this package doesn't extend
      them to negative degrees. Why?

      The answer isn't very interesting--it's a design choice based on focusing on what I suspect that
      most users need and on keeping the code compact. If you need to extend a function to negative
      degrees or the like, let me know--or even better do it yourself and share it.

  (h) For large `n`, shouldn't the code switch over to asymptotic series?

      Maybe, but it's a design choice to keep the code compact and focused on typical cases
      that users need. 

|#

(in-package :maxima)

(defun orthopoly-default-simp (p x)
  "Default cleanup for orthogonal polynomials."
  (declare (ignore x))
  (sratsimp p))

;; Function applied to every symbolically generated polynomial.
(defun orthopoly-polynomial-simp (p x &optional (simp-fn #'orthopoly-default-simp))
  "Apply 'simp-fn' to 'p'. If 'simp-fn' is nil, return 'p' unchanged."
  (if simp-fn
      (funcall simp-fn p x)
    p))

;; Number of base 10 digits in a binary64 number (it is 15).
(defmvar *binary64-digits* (floor (* (float-digits 1.0d0) (log 2 10))))

;; A left continuous unit step function; thus 
;;
;;       unit_step(x) = 0 for x <= 0 and 1 for x > 0.  
;;
;; This function differs from (1 + signum(x))/2 which isn't left or right
;; continuous at 0. We do not attempt to give unit_step a grad property.

(defun simp-unit-step (a y z)
  (oneargcheck a)
  (setq y (simpcheck (cadr a) z))
  (let ((s (csign y)))
    (cond ((or (eq s '$nz) (eq s '$zero) (eq s '$neg)) 0)
	  ((eq s '$pos) 1)
	  (t `(($unit_step simp) ,y)))))
(setf (get '$unit_step 'operators) 'simp-unit-step)
(setf (get '%unit_step 'operators) 'simp-unit-step)

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

(defun orthopoly-number-coerce (x one)
  (cond
    (($ratnump one)
     ($rationalize x))

    ((floatp one)
     ;; Try float conversion, but fall back to bigfloat on overflow
     (let ((f (errcatch ($float x))))
      (if f
          (car f)
          ($bfloat x))))

    (t
     ($bfloat x))))

;;; simplifier for the Jacobi polynomials
(def-simplifier jacobi_p (n a b x)
  (cond
    ;; Numeric evaluation: all arguments are numeric (either real or complex)
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
    ((and (eql x 1) ($featurep n '$integer) (eq t (mgqp n 0)))
     (div (ftake '$pochhammer (add a 1) n) (ftake 'mfactorial n)))

    ;; Otherwise, no simplification available
    (t
     (give-up))))

;;; For the Jacobi polynomials, we need to special case negative integer parameters. The code
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
(defun jacobi_p-numeric (n a b x digits)
  (let* ((bf-a   (bigfloat::to a))
         (bf-b   (bigfloat::to b))
         (bf-x   (bigfloat::to x))
         (eps   (bigfloat::to (ftake 'mexpt 10 (- digits))))
         (a+b    (bigfloat::+ bf-a bf-b))
         (a+b+1  (bigfloat::+ bf-a bf-b 1))
         (a+b+2  (bigfloat::+ bf-a bf-b 2))
         ;; a^2 - b^2
         (a2-b2  (bigfloat::- (bigfloat::* bf-a bf-a) (bigfloat::* bf-b bf-b)))
  
        (f0 (bigfloat::to 1))
        (f1 (bigfloat::/ (bigfloat::+ (bigfloat::* (bigfloat::+ bf-a bf-b 2) bf-x) (bigfloat::- bf-a bf-b))  2))

     (p #'(lambda (k)
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
           (bigfloat::/ num den))))

  (q #'(lambda (k)
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
           (bigfloat::/ num den)))))

    (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error  p q f0 f1 n)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (jacobi_p-numeric n ($bfloat a) ($bfloat b) ($bfloat x) digits))))))

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
		  
(defun ultraspherical-numeric (n lam x digits)
  (let* ((bf-x (bigfloat::to x))
         (bf-lam (bigfloat::to lam))
         (2lam (bigfloat::* (bigfloat::to 2) bf-lam))
         (eps (bigfloat::to (ftake 'mexpt 10 (- digits))))
         (2lam-1 (bigfloat::- 2lam (bigfloat::to 1)))
         (f0 (bigfloat::to 1))
         (f1 (bigfloat::* (bigfloat::to 2) (bigfloat::to lam) bf-x))
         (p #'(lambda (k)
                    (let* ((k+1 (bigfloat::+ k 1))
                           ;; Numerator: 2(k + lam)x
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
            (bigfloat::generic-two-term-recursion-running-error  p q f0 f1 n)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (ultraspherical-numeric n ($bfloat lam) ($bfloat x) digits))))))


(def-simplifier chebyshev_t (n x)
  (cond ((and (integerp n) (complex-number-p x #'$numberp))
            (let* ((digits (get-digits x))
		               (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (chebyshev_t-numeric n x digits) one)
				(give-up))))

		  ((integerp n)
        (if (< n 0)
           (orthopoly-polynomial-simp (chebyshev_t-symbolic (neg n) x) x)
		       (orthopoly-polynomial-simp (chebyshev_t-symbolic n x) x)))

      ;; See DLMF Table Table 18.6.1 for the following three simplifications:
		  ((eql x 1)  1)
		  ((and (eql x 0) ($featurep n '$even)) (ftake 'mexpt 1 (div n 2)))
		  ;; chebyshev_t(n,-x) = (-1)^n chebyshev_t(n,-x)
      ((great (neg x) x)
		    (mul (ftake 'mexpt -1 n) (ftake '%chebyshev_t n (neg x))))
      ;; chebyshev_t(n,x) = chebyshev_t(-n,x)
      ((great (neg n) n)
		    (ftake '%chebyshev_t (neg n) x))
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

(defun chebyshev_t-numeric (n x digits)
   (let* ((bf-x (bigfloat::to x))
          (eps (bigfloat::to (ftake 'mexpt 10 (- digits))))
          (f0 (bigfloat::to 1))
          (f1 bf-x)
          (p #'(lambda (k) (declare (ignore k)) (bigfloat::* 2 bf-x)))
          (q #'(lambda (k) (declare (ignore k)) (bigfloat::to -1))))
    (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error  p q f0 f1 n)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (chebyshev_t-numeric n ($bfloat x) digits))))))

        
(def-simplifier chebyshev_u (n x)
   (cond ((and (integerp n) (complex-number-p x #'$numberp))
             (let* ((digits (get-digits x))
		                (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (chebyshev_u-numeric n x digits) one)
				(give-up))))

		  ((integerp n)
        (if (< n 0)
           (chebyshev_u-symbolic (sub (- n) 2) x)
		       (chebyshev_u-symbolic n x)))

		  ;; See DLMF Table Table 18.6.1 for the following three simplifications:
		  ((eql x 1) (add n 1))
		  
		  ((and (eql x 0) ($featurep n '$even)) 
		     (ftake 'mexpt 1 (div n 2)))

		  ;; chebyshev_t(n,-x) = (-1)^n chebyshev_t(n,-x)
      ((great (neg x) x)
		    (mul (ftake 'mexpt -1 n) (ftake '%chebyshev_u n (neg x))))

      ;;U(n,x) = U(-n-2,x)
      ((and ($featurep n '$integer) (great (sub (neg n) 2) n))
        (ftake '%chebyshev_u (sub (neg n) 2) x))

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

(defun chebyshev_u-numeric (n x digits)
  (let*  ((bf-x (bigfloat::to x))
         (eps (bigfloat::to (ftake 'mexpt 10 (- digits))))
         (f0 (bigfloat::to 1))
         (f1 (bigfloat::* 2 bf-x))
         (p #'(lambda (k) (declare (ignore k)) (bigfloat::* 2 bf-x)))
         (q #'(lambda (k) (declare (ignore k)) (bigfloat::to -1))))
      (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error  p q f0 f1 n)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (chebyshev_u-numeric n ($bfloat x) digits))))))

(def-simplifier legendre_p (n x)
   (cond ((and (integerp n) (complex-number-p x #'$numberp)) ;evaluate numerically
            (let* ((digits (get-digits x))
		               (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (legendre_p-numeric n x digits) one)
				(give-up))))

      ;; see DLMF http://dlmf.nist.gov/14.9.E5
      ((eq t (mgrp 0 n))
       (ftake '%legendre_p (neg (add n 1)) x))

		  ((integerp n)
          (if (< n 0)
              (give-up) ; should be caught already!
              (orthopoly-polynomial-simp (legendre_p-symbolic n x) x)))

      ;; Simplifications from DLMF Table 18.6.1 
      ((eql x 1) 1)

      ((and (eql x 0) ($featurep n '$even))
        (let ((n2 (div n 2)))
          (div 
            (mul (ftake 'mexpt -1 n2) (ftake '$pochhammer (div 1 2) n2))
            (ftake 'mfactorial n2))))

      ((great (neg x) x)
       (mul (ftake 'mexpt -1 n) (ftake '%legendre_p n (neg x))))

 		(t (give-up))))

(defun legendre_p-numeric (n x digits)
  (let* ((bf-x (bigfloat::to x))   
         (one (bigfloat::to 1))
         (eps (bigfloat::to (ftake 'mexpt 10 (- digits))))
         (f0 one)
         (f1 bf-x)
         (p #'(lambda (kk)
             (let ((k (bigfloat::to kk)))
                   (bigfloat::/ (bigfloat::* (bigfloat::+ (bigfloat::* 2 k) 1) bf-x) (bigfloat::+ k 1)))))
         (q #'(lambda (kk) 
          (let ((k (bigfloat::to kk))) (bigfloat::/ k (bigfloat::+ k one))))))
      (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error  p q f0 f1 n)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (legendre_p-numeric n ($bfloat x) digits))))))
  

(defun legendre_p-symbolic (n x)
    (let* ((f0 1)
		       (f1 x)
           (p #'(lambda (k) (div (mul (add (mul 2 k) 1) x) (add k 1)))) ; (2k+1)x/(k+1) 
           (q #'(lambda (k) (mul -1 (div k (add k 1))))))
	 (generic-two-term-recursion-symbolic p q f0 f1 n)))

(defun get-digits (x)
  (if (floatp x)
			*binary64-digits*
			$fpprec))

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

        ((some #'$taylorp (cdr form))
         (let* ((data ($taylorinfo (third form)))
                (tp  (errcatch ($apply '$taylor ($cons (ftake '%hermite n x) data)))))
            (if (and tp (freeof '%derivative ($ratdisrep (car tp))))
               (car tp)
               (give-up))))

        ;; reflection: hermite(n,-x) = (-1)^n hermite(-n,-x)
        ((great (neg x) x)
         (mul (ftake 'mexpt -1 n) (ftake '%hermite n (neg x))))
        ;; hermite(n,0) = (-1)^(n/2) pochhammer(n/2 + 1,n/2), n even;
        ;; See Table 18.6.1 of DLMF
        ((and (eql 0 x) ($featurep n '$even))
          (div
             (mul (ftake 'mexpt 2 n)
                  (ftake 'mexpt '$%pi (div 1 2)))
             (ftake '%gamma (div (sub 1 n) 2))))
        ;; hermite(2n+1,0) = 0
        ((and (eql 0 x) ($featurep n '$odd))  0)
        (t (give-up))))

#| 
(define-two-term-numeric* hermite-numeric (n x digits)
  :let  ((bf-x  (bigfloat::to x))
         (bf-2x (bigfloat::* 2 bf-x)))
  :f0   (bigfloat::to 1)
  :f1   bf-2x
  :p    (lambda (k) (declare (ignore k)) bf-2x)
  :q    (lambda (k) (bigfloat::* -2 k)))
|#

(defun hermite-symbolic (n x)
    (let* ((f0 1)
		       (f1 (mul 2 x))
           (p #'(lambda (k) (declare (ignore k)) (mul 2 x)))
           (q #'(lambda (k) (mul -2 k))))
		    (generic-two-term-recursion-symbolic p q f0 f1 n)))

;; floating-point traps are disabled by defaultfloating-point traps are disabled by default f
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
			    (orthopoly-number-coerce (gen_laguerre-numeric n x 0 digits) one)
				(give-up))))
          ;; symbolic case 
		  ((integerp n)
           (if (< n 0)
              (give-up)
              (orthopoly-polynomial-simp (gen_laguerre-symbolic n 0 x) x)))
          ;; nothing known--noun form return
 		  (t (give-up))))

(defun gen_laguerre-numeric (n a x digits)
  (let* ((bf-a (bigfloat::to a))
         (bf-x (bigfloat::to x))
         (eps  (bigfloat::to (ftake 'mexpt 10 (- digits))))
         ;; hoist a constant 
         (a+1 (bigfloat::+ bf-a 1))
         (f0 (bigfloat::to 1))
         (f1 (bigfloat::- (bigfloat::+ bf-a 1) bf-x))
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
       (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error  p q f0 f1 n)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (gen_laguerre-numeric n ($bfloat a) ($bfloat x) digits))))))

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

(defun spherical_hankel1-numeric (n x digits)
  (let* ((bf-x (bigfloat::to x))
	       (f0 (bigfloat::order-zero-spherical_hankel1 bf-x))
	       (f1 (bigfloat::order-one-spherical_hankel1 bf-x))
         (eps   (bigfloat::to (ftake 'mexpt 10 (- digits))))
         (p #'(lambda (k) (bigfloat::/ (+ (* 2 k) 1) bf-x)))
         (q #'(lambda (k) (declare (ignore k)) (bigfloat::to -1))))
     (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error  p q f0 f1 n)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (spherical_hankel1-numeric n ($bfloat x) digits))))))

(def-simplifier spherical_hankel2 (n x)
  (give-up))

(def-simplifier spherical_bessel_j (n x)
    (cond 
       ;; spherical_bessel_j(n,x) = (-1)^n spherical_bessel_j(-n-1,x)
       ((great (neg n) n)
        (mul  
           (ftake 'mexpt -1 n) 
           (ftake '%spherical_bessel_j (add (neg n) -1) x)))

      ;; spherical_bessel_j(n,0) = kron_delta(n,-1) + kron_delta(n,1)
      ((zerop1 x)
        (add (ftake '%kron_delta n -1) (ftake '%kron_delta n 1)))
    
       ((and (integerp n) (complex-number-p x #'$numberp) (not (complex-number-p x #'$ratnump)))
             (let* ((digits (get-digits x))
		                (one (multiplicative-identity x)))
			   (if one 
			      (orthopoly-number-coerce (spherical_bessel_j-numeric n x digits) one)
			  	(give-up))))

		  ((integerp n)	
		    (orthopoly-polynomial-simp (spherical_bessel_j-symbolic n x) x))

      ;; spherical_bessel_j(n,x) = (-1)^n spherical_bessel_j(n,-x)
		  ((great (neg x) x)
		  	(mul (ftake 'mexpt -1 n) (ftake '%spherical_bessel_j n x)))

		  (t (give-up))))
		    
(defun spherical_bessel_j-numeric (n x digits)
  (let* ((bf-x (bigfloat::to x))
          (bf-zero (bigfloat::to 0))
          (bf-one (bigfloat::to 1))
          (eps (bigfloat::to (ftake 'mexpt 10 (- digits))))
          (bf-minus-one (bigfloat::to -1))
          (f0 (if (bigfloat::zerop bf-x)
                  bf-one
                  (bigfloat::/ (bigfloat::sin bf-x) bf-x)))

          (f1 (if (bigfloat::zerop bf-x)
                  bf-zero
                  (bigfloat::-
                    (bigfloat::/ (bigfloat::sin bf-x) (bigfloat::* bf-x bf-x))
                    (bigfloat::/ (bigfloat::cos bf-x) bf-x))))
          ;; p(k) = (2k+1)/x
          (p #'(lambda (k) (bigfloat::/ (bigfloat:to (+ (* 2 k) 1))  bf-x)))
          ;; q(k) = -1   
          (q #'(lambda (k) (declare (ignore k)) bf-minus-one)))
      (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error  p q f0 f1 n)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (spherical_bessel_j-numeric n ($bfloat x) digits))))))
  
(defun spherical_bessel_j-symbolic (n x)
  "Symbolic spherical Bessel j_n(x) using the recurrence:
   j_0(x) = sin(x)/x
   j_1(x) = sin(x)/x^2 - cos(x)/x
   j_{n+1}(x) = ((2n+1)/x) * j_n(x) - j_{n-1}(x)."
  (let* ((f0 (if (zerop1 x) 
               1
               (div (ftake '%sin x) x)))
         (f1 (if (zerop1 x) 
                  0
                  (sub (div (ftake '%sin x) (ftake 'mexpt x 2)) (div (ftake '%cos x) x))))
         ;; p(k) = ((2k+1)/x)
         (p #'(lambda (k) (div (+ (* 2 k) 1) x)))
         ;; q(k) = -1
         (q #'(lambda (k) (declare (ignore k)) -1)))
    (generic-two-term-recursion-symbolic p q f0 f1 n)))
	    
(def-simplifier spherical_bessel_y (n x)
  (cond
     ;; spherical_bessel_y(n,0) is not real.
    ((zerop1 x)
     (merror "spherical_bessel_y: encountered spherical_bessel_y(n,0)"))

    ;; spherical_bessel_y(n,x) = (-1)^n spherical_bessel_y(-n-1,x)
    ((great (neg n) n)
     (mul
       (ftake 'mexpt -1 n)
       (ftake '%spherical_bessel_y (add (neg n) -1) x)))

    ;; numeric evaluation path
    ((and (integerp n)
          (complex-number-p x #'$numberp)
          (not (complex-number-p x #'$ratnump)))
     (let* ((digits (get-digits x))
            (one (multiplicative-identity x)))
       (if one
           (orthopoly-number-coerce
             (spherical_bessel_y-numeric n x digits)
             one)
           (give-up))))

    ;; symbolic polynomial-like form
    ((integerp n)
     (orthopoly-polynomial-simp  (spherical_bessel_y-symbolic n x) x))

    ;; spherical_bessel_y(n,x) = (-1)^n spherical_bessel_y(n,-x)
    ((great (neg x) x)
     (mul
       (ftake 'mexpt -1 n)
       (ftake '%spherical_bessel_y n x)))

    (t (give-up))))

;; The spherical_bessel_y simplifier traps the case x = 0.
(defun spherical_bessel_y-numeric (n x digits)
  (let* ((bf-x (bigfloat::to x))
         (eps  (bigfloat::to (ftake 'mexpt 10 (- digits))))
         ;; y_0(x) = -cos(x)/x
         (f0 (bigfloat::/ (bigfloat::- (bigfloat::cos bf-x)) bf-x))
         ;; y_1(x) = -cos(x)/x^2 - sin(x)/x
         (f1 (bigfloat::- (bigfloat::/ (bigfloat::- (bigfloat::cos bf-x))
                     (bigfloat::* bf-x bf-x))
            (bigfloat::/ (bigfloat::sin bf-x) bf-x)))
        ;; p(k) = (2k+1)/x
        (p #'(lambda (k) (bigfloat::/ (bigfloat::to (+ (* 2 k) 1)) bf-x)))
        ;; q(k) = -1
        (q #'(lambda (k) (declare (ignore k)))))
     (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error  p q f0 f1 n)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (spherical_bessel_y-numeric n ($bfloat x) digits))))))

(defun spherical_bessel_y-symbolic (n x)
  "Symbolic spherical Bessel y_n(x) using the recurrence:
   y_0(x) = -cos(x)/x
   y_1(x) = -cos(x)/x^2 - sin(x)/x
   y_{n+1}(x) = ((2n+1)/x) * y_n(x) - y_{n-1}(x)."
  (let* ((f0 (div (sub 0 (ftake '%cos x)) x))

         (f1  (sub (div (neg (ftake '%cos x)) (ftake 'mexpt x 2))  (div (ftake '%sin x) x)))

         ;; p(k) = ((2k+1)/x)
         (p #'(lambda (k) (div (+ (* 2 k) 1) x)))

         ;; q(k) = -1
         (q #'(lambda (k) (declare (ignore k))  -1)))
    (generic-two-term-recursion-symbolic p q f0 f1 n)))
 

(def-simplifier spherical_harmonic (l m theta phi)
  (cond ((or (eq t (mgrp (ftake 'mabs m) l)) (eq t (mgrp 0 l))) 0) 

        ;; http://dlmf.nist.gov/14.30.E4 Y(l,m,0,phi)
        ((eql theta 0)
          (cond ((eql m 0) 
                  (ftake 'mexpt (div (add (mul 2 l) 1) (mul 4 '$%pi)) (div 1 2)))
                ((integerp m)
                 0)
                (t (give-up))))

        ((and (integerp l) (integerp m))
          ;; see http://dlmf.nist.gov/14.30.E1
          (let ((cnst
             (ftake 'mexpt 
               (div 
                  (mul (+ (* 2 l) 1) (ftake 'mfactorial (- l m)))
                  (mul 4 '$%pi (ftake 'mfactorial (+ l m))))
               (div 1 2)))

          (f1 (ftake '%ultraspherical (- l m) (add m (div 1 2)) (ftake '%cos theta)))
          (f2 (ftake 'mexpt (ftake '%sin theta) m))
          (f3 (ftake 'mexpt '$%e (mul '$%i m phi))))

          (mul cnst f1 f2 f3)))

       ((great m (neg m)) ;http://dlmf.nist.gov/14.30.E6 
        (mul
          (ftake 'mexpt -1 (neg m))
          (ftake '$conjugate (ftake '%spherical_harmonic l (neg m) theta phi))))
        
       (t (give-up))))

;; Converting the initial values f0 & f1 to  CRE form makes this calculation much faster.
(defun generic-two-term-recursion-symbolic (p q f0 f1 n)
  (let (($algebraic t))
    (setq f0 ($rat f0))
    (setq f1 ($rat f1))
    (cond ((eql n 0) f0)
          ((eql n 1) f1)
          (t
           (let ((f2)
                 (end (1- n)))
             (do ((k 1 (1+ k)))
                 ((> k end) ($ratdisrep f1))
               (setq f2 (add (mul (funcall p k) f1) (mul (funcall q k) f0)))
               (setq f0 f1
                     f1 f2)))))))


(in-package #:bigfloat)

;; Extend epsilon to rationals and complex rationals
(defmethod epsilon ((x cl:rational))
  (bigfloat::to 0))

(defmethod epsilon ((x cl:number))
  ;; Fallback catch-all for any other number types (like complex rationals)
  ;; by extracting the real part and evaluating its epsilon.
  (epsilon (cl:realpart x)))

(defun modified-relative-error-p (x err eps)
  "Return T if the componentwise modified relative error is <= eps.  Works for real or complex x and err"
  (setq eps (bigfloat::to eps))
   (setq x (bigfloat::to x))
    (setq err (bigfloat::to err))
  (flet ((okay (x err eps)
           (<= (abs err) (* eps (max 1 (abs x))))))
    (and
     (okay (realpart x) (realpart err) eps)
     (okay (imagpart x) (imagpart err) eps))))

(defun componentwise-abs (z)
  "Return the componentwise absolute value of a real or complex number.
   For real x, returns (abs x).
   For complex z = a + i b, returns abs(a) + i abs(b)."
  (if (complexp z)
      (complex (abs (realpart z))
               (abs (imagpart z)))
      (abs z)))

(defun generic-two-term-recursion-running-error (p q f0 f1 n)
  "Evaluate the recurrence forward while tracking a componentwise absolute
   running error bound using the IEEE‑754 real floating‑point model.

   Recurrence: f(k+1) = p(k)*f(k) + q(k)*f(k-1)

   Returns two values: (values f_n  error-bound-for-f_n)"
  (cond ((eql n 0) (values f0 0))
        ((eql n 1) (values f1 0))
        (t
         (let ((e0 (componentwise-abs f0))   ; initial error bounds
               (e1 (componentwise-abs f1))
               (end (1- n))
               f2 e2)
           (do ((k 1 (1+ k)))
               ((> k end)
                ;; final error bound: ε * e1, componentwise
                (values f1 (componentwise-abs (* (epsilon f1) e1))))
             (let* ((a (funcall p k))
                    (b (funcall q k))
                    ;; recurrence step
                    (next (+ (* a f1) (* b f0))))
               (setq f2 next)
               ;; componentwise error propagation
               (setq e2 (+ (componentwise-abs (* a e1))
                           (componentwise-abs (* b e0))
                           ;; rounding error from forming f2 itself
                           (componentwise-abs (* (epsilon next) next))))
               ;; update state
               (setq f0 f1
                     f1 f2
                     e0 e1
                     e1 e2)))))))

(in-package :maxima)

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

(in-package #:bigfloat)

(defun legendre-q-degree-0 (x)
  (/ (log (/ (+ x 1) (- 1 x))) 2))

(defun legendre-q-degree-1 (x)
  (- (* x (legendre-q-degree-0 x)) 1))

(in-package :maxima)

(defun legendre_q-numeric (n x digits)
  (let* ((bf-x (bigfloat::to x))
         (one (bigfloat::to 1))
         (f0 (bigfloat::legendre-q-degree-0 bf-x))
         (f1 (bigfloat::legendre-q-degree-1 bf-x))
         (eps (bigfloat::to (ftake 'mexpt 10 (- digits))))
         (p #'(lambda (kk)
          (let ((k (bigfloat::to kk)))
                (bigfloat::/ (bigfloat::* (bigfloat::+ (bigfloat::* 2 k) 1) bf-x) (bigfloat::+ k 1)))))
         (q #'(lambda (kk) 
          (let ((k (bigfloat::to kk))) 
                (bigfloat::/ (bigfloat::- k) (bigfloat::+ k one))))))
            (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error p q f0 f1 n)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (legendre_q-numeric n ($bfloat x) digits))))))

(defun legendre_q-symbolic (n x)
    (let* ((f0 (div (ftake '%log (div (add x 1) (sub 1 x))) 2))
		       (f1 (sub (mul x f0) 1))
           (p #'(lambda (k) (div (mul (add (mul 2 k) 1) x) (add k 1)))) ; (2k+1)x/(k+1) 
           (q #'(lambda (k) (mul -1 (div k (add k 1))))))
	 (generic-two-term-recursion-symbolic p q f0 f1 n)))
   
(def-simplifier assoc_legendre_q (n m x)
  (cond 
     ;; domain error for x = +/-1 or n+m a negative integer. See comment in DLMF that follows http://dlmf.nist.gov/14.3.E3 
     ;; in the print edition, it is on page 353.
     ((or (onep1 x) (onep1 (neg x)) (and (integerp n) (integerp m) (< (add n m) 0)))
       (merror "Domain error: ~M is not in the domain of ~M ~%" (ftake 'mlist n m x) 'assoc_legendre_q-symbolic))

    ;; http://dlmf.nist.gov/14.9.E4
    ((and (integerp n) (integerp m) (< m 0) (< (- m n) 0))
     (div
       (mul (ftake 'mexpt -1 (- m)) ; (-1)^(-m)
            (ftake '%gamma (+ n m 1)) ; gamma(n+m+1)
            (ftake '%assoc_legendre_q n (- m) x)) ; assoc_legendre_q(n,-m,x)
       (ftake '%gamma (+ n (- m) 1))))  ;gamma(n-m+1)
  
    ((and (integerp n) (integerp m) (complex-number-p x #'(lambda (q) (or (floatp q) ($bfloatp q))))   (> n -1) (<= (abs m) n))
           (let* ((digits (get-digits x))
                  (one (multiplicative-identity x)))
			(if one 
			    (orthopoly-number-coerce (assoc_legendre_q-numeric n m x digits) one)
				(give-up))))

      ((and (integerp n) (integerp m) (> n -1) (> m -1))
       (orthopoly-polynomial-simp (assoc_legendre_q-symbolic n m x) x))

      ((eql m 0)
        (ftake '%legendre_q n x))

      (t (give-up))))

;; Return  assoc_legendre_q(n,m,x) when n & m are integers, m is positive, n+m >= 0,  and x is symbolic. 
;; The general simplifier for assoc_legendre_q catches these cases.
(defun assoc_legendre_q-symbolic (n m x)
     (let* ((w (ftake 'mexpt (sub 1 (mul x x)) (div 1 2))) ;hoist constant sqrt(1-x^2)
            (qn0 (ftake '%legendre_q n x))
            (qn1 (div (mul (add n 1) (sub (ftake '%legendre_q (add n 1) x) (mul x qn0))) w)) ; assoc_legendre_q(n,1,x)
            (p   #'(lambda (m)  (div (mul -2 m x) w)))
            (q   #'(lambda (m)  (mul -1 (add n (neg m) 1) (add n m)))))
       (generic-two-term-recursion-symbolic  p q qn0 qn1 m)))

(defun assoc_legendre_q-numeric (n m x digits)
  (let*  ((bf-x (bigfloat::to x))
          (w (bigfloat::sqrt (bigfloat::- 1 (bigfloat::* bf-x bf-x))))
          (qn0 (bigfloat::to (legendre_q-numeric n x digits)))
          (zzz (bigfloat::to (legendre_q-numeric (+ n 1) x digits))) ; zzz=assoc_legendre_q(n,1,x)
          (qn1 (bigfloat::/ (bigfloat::* (+ n 1) (bigfloat::- zzz (bigfloat::* bf-x qn0))) w))
          (eps   (bigfloat::to (ftake 'mexpt 10 (- digits))))
          (f0 qn0)
          (f1 qn1)
          (p  (lambda (m) (bigfloat::/ (bigfloat::* -2 m bf-x) w)))
          (q  (lambda (m) (bigfloat::* -1 (+ n (- m) 1) (+ n m)))))

      (multiple-value-bind (value err)
            (bigfloat::generic-two-term-recursion-running-error p q f0 f1 m)
          (if (bigfloat::modified-relative-error-p value err eps)
              (maxima::to value)
              ;; restart with doubled precision
              (bind-fpprec (mul 2 $fpprec)
                (assoc_legendre_q-numeric n m ($bfloat x) digits))))))

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
  #$$ pochhammer(x,n)*(psi[0](x+n) - psi[0](x))$
  ;; ∂/∂n
  #$$ pochhammer(x,n)*psi[0](x+n)$)
  

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
      jacobi_p(n+1, a, b, x)
      = jacobi_p(n, a, b, x) * ((2*n + a + b + 1) * (2*n + a + b + 2)*x /(2*(n+1)*(n+a+b+1)) + (a^2-b^2)*(2*n+a+b+1)/(2*(n+1)*(n+a+b+1)*(2*n+a+b)))
      - (n+a)*(n+b)*(2*n + a + b + 2) * jacobi_p(n-1, a, b, x)/((n+1)*(n+a+b+1)*(2*n+a+b)))$)

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

(defmfun orthopoly_register_weight (name lambda_expr)
  (let* ((lname (mfuncall '$symbol name))
         (lform lambda_expr))
    (register-orthopoly-weight lname lform)
    lname))

(defmfun $orthopoly_weight (name)
  (or (gethash name *orthopoly-weight-table*)
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

(defparameter *orthopoly-normalization-table*
  (make-hash-table :test #'eq :size 128))

(defun register-orthopoly-normalization (name lambda-form)
  (setf (gethash name *orthopoly-normalization-table*) lambda-form)
  name)

(defun orthopoly_normalization (name)
  (or (gethash name *orthopoly-normalization-table*)
      (error "No normalization registered for ~A" name)))

(defmfun orthopoly_register_normalization (name lambda_expr)
  (let* ((lname (mfuncall '$symbol name))
         (lform lambda_expr))
    (register-orthopoly-normalization lname lform)
    lname))

(defmfun $orthopoly_normalization (name)
    (or (gethash name *orthopoly-normalization-table*)
        (merror "No normalization registered for ~M" name)))

(register-orthopoly-normalization
 '%hermite
 #$$ lambda([n], 2^n * factorial(n) * sqrt(%pi)) $)

(register-orthopoly-normalization
 '%legendre_p
 #$$ lambda([n],
      2/(2*n+1)) $)

(register-orthopoly-normalization
 '%chebyshev_t
 #$$ lambda([n],
      if n=0 then %pi else %pi/2) $)

(register-orthopoly-normalization
 '%chebyshev_u
 #$$ lambda([n],
      %pi/2) $)

(register-orthopoly-normalization
 '%ultraspherical
 #$$ lambda([n,lambda],
      %pi * 2^(1-2*lambda)
        * gamma(n+2*lambda)
        /( factorial(n)*(n+lambda)*gamma(lambda)^2 )) $)

(register-orthopoly-normalization
 '%laguerre
 #$$ lambda([n,a],
      gamma(n+a+1)/factorial(n)) $)

(register-orthopoly-normalization
 '%gen_laguerre
 #$$ lambda([n,a],
      gamma(n+a+1)/factorial(n)) $)

(register-orthopoly-normalization '%jacobi_p
 #$$ lambda([n,a,b],
      2^(a+b+1)/(2*n+a+b+1)
        * gamma(n+a+1)*gamma(n+b+1)
        /( factorial(n)*gamma(n+a+b+1) )) $)

(register-orthopoly-normalization
 '%spherical_bessel_j
 #$$ lambda([n],
      integrate(spherical_bessel_j(n,x)^2 * x^2, x, 0, inf)) $)

(register-orthopoly-normalization
 '%spherical_bessel_y
 #$$ lambda([n],
      integrate(spherical_bessel_y(n,x)^2 * x^2, x, 0, inf)) $)

(register-orthopoly-normalization
 '%spherical_hankel1
 #$$ lambda([n],
      integrate(spherical_hankel1(n,x)^2 * x^2, x, 0, inf)) $)

(register-orthopoly-normalization
 '%spherical_hankel2
 #$$ lambda([n],
      integrate(spherical_hankel2(n,x)^2 * x^2, x, 0, inf)) $)

(register-orthopoly-normalization
 '%spherical_harmonic
 #$$ lambda([l,m],
      1) $)

;;; Gradient definitions for orthogonal polynomials
(defgrad %jacobi_p ($n $a $b $x)
  nil nil nil
  #$$ (n*jacobi_p(n,a,b,x)*((-(2*n)-b-a)*x-b+a)
      +2*jacobi_p(n-1,a,b,x)*(n+a)*(n+b)*unit_step(n))
      /((2*n+b+a)*(1-x^2)) $)

;;; http://dlmf.nist.gov/18.9.E19 The gradient for n=0 is a special case.
(defgrad %ultraspherical ($n $a $x)
  nil 
  nil
  #$$ 2*a*ultraspherical(n-1,a+1,x)$)

;; http://dlmf.nist.gov/18.9.E21 
(defgrad %chebyshev_t ($n $x)
  nil
  #$$ n*chebyshev_u(n-1,x) $)

(defgrad %chebyshev_u ($n $x)
  nil
  #$$ (chebyshev_u(n-1,x)*(n+1)*unit_step(n)-n*chebyshev_u(n,x)*x)/(1-x^2) $)

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
  #$$ (n*assoc_legendre_p(n,m,x)*x-assoc_legendre_p(n-1,m,x)*(n+m)*unit_step(n))/(x^2-1)$)

(defgrad %assoc_legendre_q ($n $m $x)
  nil 
  nil
  #$$ (1/(1-x^2))*(-n*x*assoc_legendre_q(n,m,x) + (n+m)*assoc_legendre_q(n-1,m,x)) $)

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
  #$$ (spherical_harmonic(l,m-1,theta,phi)*sqrt((-m+l+1)*(m+l))*%e^(%i*phi))/2
 -(spherical_harmonic(l,m+1,theta,phi)*sqrt((l-m)*(m+l+1))*%e^-(%i*phi))/2$
  #$$ %i*m*spherical_harmonic(l,m,theta,phi)$)

;;; antiderivative definitions:
(defmacro def-integral (name arglist &rest entries)
  "Define integral properties for orthogonal polynomials. Here `arglist` is (x1,x2, ...,xn),
  and `entries` is a list of expressions, one per argument. For an undefined antiderivative, 
  use nil."
    `(putprop ',name
            (list ',arglist ,@entries)
            'integral))

;; antiderivative of unit_step
(def-integral %unit_step ($x)
  #$$(abs(x)+x)/2$)

;; This needs protection for n=-1, but I don't know how to get Maxima to do this gracefully
(def-integral %hermite ($n $x)
  nil
  #$$hermite(n+1,x)/(2*(n+1))$)

(def-integral %legendre_p ($n $x)
  nil
  #$$ (legendre_p(n+1,x) - legendre_p(n-1,x))/(2*n+1) $)

(def-integral %chebyshev_t ($n $x)
  nil
  #$$ chebyshev_t(n+1,x)$)

(def-integral %chebyshev_u ($n $x)
  nil
  #$$ chebyshev_u(n+1,x)/(2*(n+1)) $)

(def-integral %ultraspherical (n lambda x)
  nil 
  nil
  #$$ ultraspherical(n+1,lambda,x)/(2*(n+lambda+1))
      - ultraspherical(n-1,lambda,x)/(2*(n+lambda-1)) $)

(def-integral %laguerre (n a x)
  nil 
  nil
  #$$ -laguerre(n-1,a+1,x) $)

(def-integral %gen_laguerre (n a x)
  nil 
  nil
  #$$ -gen_laguerre(n-1,a+1,x) $)

(def-integral %jacobi_p (n a b x)
  nil 
  nil 
  nil
  #$$ jacobi_p(n+1,a,b,x)/(2*(n+1)) - jacobi_p(n-1,a,b,x)/(2*(n+a+b)) $)

;;;  Rodrigues subsystem for orthogonal polynomials in Maxima

(defmacro def-rodrigues (name lambda-form)
  "Store a Rodrigues formula as a Maxima lambda form."
  `(putprop ',name
            ,lambda-form
            'rodrigues))

(defmfun $orthopoly_rodrigues (name)
    (or (get name 'rodrigues) (merror "No Rodrigues form registered for ~M" name)))

(def-rodrigues %hermite
  #$$ lambda([n,x],
       (-1)^n * exp(x^2) * diff(exp(-x^2), x, n)) $)

(def-rodrigues %legendre_p
  #$$ lambda([n,x],
       (1/(2^n * factorial(n))) * diff((x^2 - 1)^n, x, n)) $)

(def-rodrigues %chebyshev_t
  #$$ lambda([n,x], (1-x^2)^(1/2) * diff((1-x^2)^(-1/2) * (1-x^2)^n,x,n) / ((-2)^n * pochhammer(1/2,n)))$)

(def-rodrigues %chebyshev_u
  #$$ lambda([n,x], (n+1)*(1-x^2)^(-1/2) * diff((1-x^2)^(1/2) * (1-x^2)^n,x,n) / ((-2)^n * pochhammer(3/2,n)))$)

(def-rodrigues %ultraspherical
  #$$ lambda([n,lam,x],
        (pochhammer(2*lam,n) / ((-2)^n * n!* pochhammer(lam+1/2,n)))
         * (1-x^2)^(1/2 - lam)
         * diff((1-x^2)^(n+lam-1/2), x, n)) $)

(def-rodrigues %laguerre
  #$$ lambda([n,a,x],
       x^(-a) * exp(x)/factorial(n)
         * diff(x^(n+a) * exp(-x), x, n)) $)

(def-rodrigues %gen_laguerre
  #$$ lambda([n,a,x],
       x^(-a) * exp(x)/factorial(n)
         * diff(x^(n+a) * exp(-x), x, n)) $)

(def-rodrigues %jacobi_p
  #$$ lambda([n,a,b,x],
       (-1)^n/(2^n * factorial(n))
         * (1-x)^(-a) * (1+x)^(-b)
         * diff((1-x)^(n+a) * (1+x)^(n+b), x, n)) $)

;;;  Sturm–Liouville (ODE) subsystem for orthogonal polynomials in Maxima

(defparameter *orthopoly-ode-operator-table*
  (make-hash-table :test #'eq :size 32))

(defparameter *orthopoly-ode-eigenvalue-table*
  (make-hash-table :test #'eq :size 32))

(defmacro def-ode (name operator-lambda)
  "Register Sturm–Liouville operator lambdas in hash table."
  `(progn
     (setf (gethash ',name *orthopoly-ode-operator-table*)
           ,operator-lambda)
     ',name))

(defmfun $orthopoly_ode (name)
  (or (gethash name *orthopoly-ode-operator-table*)
      (merror "No ODE operator registered for ~M" name)))

(def-ode %hermite
  #$$ lambda([n,x,y], diff(y,x,2) - 2*x*diff(y,x) + 2*n*y) $)

(def-ode %laguerre
  #$$ lambda([n,a,x,y],
       x*diff(y,x,2) + (a+1-x)*diff(y,x) + n*y) $)

(def-ode %gen_laguerre
  #$$ lambda([n,a,x,y],
       x*diff(y,x,2) + (a+1-x)*diff(y,x) + n*y) $)

(def-ode %legendre_p
  #$$ lambda([n,x,y],
       (1-x^2)*diff(y,x,2) - 2*x*diff(y,x) + n*(n+1)*y) $)

(def-ode %legendre_q
  #$$ lambda([n,x,y],
       (1-x^2)*diff(y,x,2) - 2*x*diff(y,x) + n*(n+1)*y) $)

(def-ode %assoc_legendre_q
  #$$ lambda([n,m,x,y],
       (1-x^2)*diff(y,x,2) - 2*x*diff(y,x) + (n*(n+1) - m^2/(1-x^2))*y) $)
       
(def-ode %chebyshev_t
  #$$ lambda([n,x,y],
       (1-x^2)*diff(y,x,2) - x*diff(y,x) + n^2*y) $)

(def-ode %chebyshev_u
  #$$ lambda([n,x,y],
       (1-x^2)*diff(y,x,2) - 3*x*diff(y,x) + n*(n+2)*y) $)

(def-ode %ultraspherical
  #$$ lambda([n,lambda,x,y],
       (1-x^2)*diff(y,x,2) - (2*lambda+1)*x*diff(y,x)
         + n*(n+2*lambda)*y) $)

(def-ode %jacobi_p
  #$$ lambda([n,a,b,x,y],
       (1-x^2)*diff(y,x,2)
         + (b-a - (a+b+2)*x)*diff(y,x)
         + n*(n+a+b+1)*y) $)

;;;  orthopoly-hypergeom.lisp

(defmacro def-hypergeom (name lambda-form)
  "Store hypergeometric representation as a Maxima lambda form."
  `(putprop ',name
            ,lambda-form
            'hypergeom))

(defmfun $orthopoly_hypergeom (name)
    (or (get name 'hypergeom)
        (merror "No hypergeometric form registered for ~M" name)))

(def-hypergeom %legendre_p
  #$$ lambda([n,x],  hypergeometric([ -n, n+1 ], [ 1 ], (1-x)/2)) $)

(def-hypergeom %jacobi_p
  #$$ lambda([n,a,b,x],
       pochhammer(a+1,n)/factorial(n)
         * hypergeometric([ -n, n+a+b+1 ],
                          [ a+1 ],
                          (1-x)/2)) $)

(def-hypergeom %laguerre
  #$$ lambda([n,a,x],
       pochhammer(a+1,n)/factorial(n)
         * hypergeometric([ -n ], [ a+1 ], x)) $)

(def-hypergeom %gen_laguerre
  #$$ lambda([n,a,x],
       pochhammer(a+1,n)/factorial(n)
         * hypergeometric([ -n ], [ a+1 ], x)) $)

(def-hypergeom %ultraspherical
  #$$ lambda([n,lambda,x],
       pochhammer(2*lambda,n)/factorial(n)
         * hypergeometric([ -n, n+2*lambda ],
                          [ lambda+1/2 ],
                          (1-x)/2)) $)

(def-hypergeom %chebyshev_t
  #$$ lambda([n,x],
       hypergeometric([ -n, n ], [ 1/2 ], (1-x)/2)) $)

(def-hypergeom %chebyshev_u
  #$$ lambda([n,x], (n+1) * hypergeometric([ -n, n+2 ], [ 3/2 ], (1-x)/2)) $)

;; Hermite to hypergeometric is not supported. For n ≥ 0, Hermite polynomials can be written using 1F1, but
;; this representation doesn't extend off the nonnegative integers. To do that, we need the  parabolic cylinder function,
;; that Maxima does not provide. 


;;; conjugate stuff

(defmacro define-orthopoly-conjugator (op &key (check 1))
  "Define and install a conjugate-function for orthogonal polynomial operator OP.
   CHECK is an integer: the first CHECK arguments must be self-conjugate."
  (let ((fun (intern (format nil "~A-CONJUGATE" op))))
    `(progn
       (defun ,fun (args)
         ;; Check first CHECK arguments for self-conjugacy
         (let ((ok
                (every
                 #'(lambda (v) (alike1 v (ftake '$conjugate v)))
                 (subseq args 0 ,check))))
           (if ok
               ;; push conjugation inside
               (fapply ',op
                       (mapcar #'(lambda (q) (ftake '$conjugate q)) args))
               ;; otherwise nounform
               ($funmake '$conjugate
                         (ftake 'mlist (fapply ',op args))))))
       (setf (get ',op 'conjugate-function) ',fun))))

(define-orthopoly-conjugator %ultraspherical :check 1)
(define-orthopoly-conjugator %hermite :check 1)
(define-orthopoly-conjugator %laguerre :check 1)
(define-orthopoly-conjugator %legendre_p :check 1)
(define-orthopoly-conjugator %gegenbauer :check 1)
(define-orthopoly-conjugator %chebyshev_t :check 1)
(define-orthopoly-conjugator %chebyshev_u :check 1)
(define-orthopoly-conjugator %jacobi_p :check 1)
(define-orthopoly-conjugator %assoc_legendre_p :check 2)
(define-orthopoly-conjugator %assoc_legendre_q :check 2)
(define-orthopoly-conjugator %spherical_bessel_j :check 1)


