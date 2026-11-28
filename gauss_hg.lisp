#|

Algorithmic overview

The primary method used is summation of the series DLMF 15.15.E1 using a well-chosen value of z0​. 
When convergence of this series is too slow, the code may instead:

 o apply a connection formula such as DLMF 15.8.E1,
 o dispatch to a special-case evaluation, for example 2F1(a,b;a;x), or ...
 o evaluate an exact symbolic expression numerically using nfloat.

In an effort to reduce rounding errors, the series summation uses Kahan summation. It also accumulates the sum of 
the absolute values of the terms, allowing estimation of the accuracy of the result.

For the cases of 2F1(integer,integer,integer,x), where x lies outside the unit circle, the code uses hgfred 
to find an exact symbolic formula for the hypergeometic function and dispatches nfloat on the symbolic expression.

References:

(a) Hypergeometric Functions, E Norlund, (1955), especially Eq 1-21. https://www.scribd.com/document/959992072/N-E-N%C3%B8rlund-1955-Hypergeometric-Functions

(b) An extension of hypergeometric functions, T W Chaundry, Quart J. Math, Oxford Series 14 (1943), 55-58 
    https://academic.oup.com/qjmath/article-abstract/os-14/1/55/1578280?re 

(c) DLMF http://dlmf.nist.gov/15.15.E1 and http://dlmf.nist.gov/16.10.E2

Recent papers on numerical evaluation of the Gauss hypergeometric function

(a)  https://link.springer.com/article/10.1007/s11075-026-02436-2 
|#

(in-package :maxima)

(defmvar $hg_bits nil
"Estimated number of correct bits in the result of the most recent gauss_hg computation."
 :properties ((assign 'neverset)))

(defmvar $hg_method nil
"Method used in the most recent gauss_hg computation."
 :properties ((assign 'neverset)))

(defmvar $hg_terms nil
"Number of termss summed in recent gauss_hg computation."
 :properties ((assign 'neverset)))

(defun multiplicative-identity (&rest a)
  "Return the appropriate multiplicative identity (1 for rational numbers, 1.0d0 for binary64, and 1.0b0 for bigfloats)
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

(defmfun $rate (x)
  (multiple-value-bind (z r) (bigfloat::choose-z (bigfloat::to x))
     (declare (ignore z))
    (maxima::to r)))

;; (b) needs protection against c a negative integer.
;; (b) should detect some special cases and dispatch specialized code

(defun terminating-before-pole-p (u c)
  (and (integerp u)
       (<= u 0)
       (< (- u) (- 1 c))))

(defun hg-denominator-pole-p (a b c)
  (and (integerp c)
       (<= c 0)
       (not (or (terminating-before-pole-p a c)
                (terminating-before-pole-p b c)))))

(defparameter *gauss-hg-methods*
  '(bigfloat::gauss-hg-elementary-case
    bigfloat::gauss-series-polynomial-rational-case
    bigfloat::f21-numeric
    bigfloat::gauss-hg-large-x
    gauss-hg-by-nfloat
    gauss-hg-failure-method)
  "Ordered list of methods used to evaluate the Gauss hypergeometric function 2F1(a,b;c;x).
   Each method is a function of four arguments (a b c x). A method that cannot handle
   the given arguments must return nil as its primary value. A successful method returns a 
   bigfloat numeric primary value together with the estimated precision in bits.

  Each of the four arguments to a method must be bigfloat number, and the result must
  also be a bigfloat number.")

(defun gauss-hg-dispatch (a b c x)
"Evaluate the Gauss hypergeometric function 2F1(a,b;c;x) by dispatching to the methods listed in *gauss-hg-methods*."
  (dolist (method *gauss-hg-methods*)
    (multiple-value-bind (f bits method N)
        (funcall method a b c x)
      (when f
        (return (values f bits method N))))))

(defmfun $gauss_hg (a b c x)
   ;; Check for an undefined case--not a polynomial case and a negative integer value for c.
   (when (hg-denominator-pole-p a b c)
     (maxima::merror
          (intl:gettext
            "gauss_hg(~M,~M,~M,~M) is undefined because ~M is a non positive integer.") a b c x c))

    (let* ((one (multiplicative-identity a b c x))
           (aa (bigfloat::to (orthopoly-number-coerce a one)))
           (bb (bigfloat::to (orthopoly-number-coerce b one)))
           (cc (bigfloat::to (orthopoly-number-coerce c one)))
           (xx (bigfloat::to (orthopoly-number-coerce x one)))
           (requested-bits (cond (($bfloatp (maxima::to (bigfloat::realpart xx)))
                                    fpprec)
                                 (($ratnump (maxima::to (bigfloat::realpart xx)))
                                    fpprec)
                                 (t (float-digits (maxima::to (bigfloat::realpart xx)))))))

      (declare (ignore requested-bits))

      (multiple-value-bind (f bits method N)
        (gauss-hg-dispatch aa bb cc xx)
      (setq $hg_bits (maxima::to bits))
      (setq $hg_method method)
      (setq $hg_terms N)
      (maxima::to f))))

(defun gauss-hg-failure-method (a b c x)
  "Signal an error indicating that no gauss_hg evaluation method was able to handle the arguments."
  (setq $hg_bits 0)
  (setq $hg_method 'failure)
  (maxima::merror (intl:gettext  "Internal error: no gauss_hg method could evaluate 2F1(~M,~M;~M;~M).") a b c x))

(defun bits-to-digits (bits)
  "Convert a precision in bits to the corresponding number of decimal digits."
  (floor (* bits (log 2 10))))

;; Handle recalcitrant cases such as 2F1([integer,integer],[integer], |x| > 1). It also handles polynomial cases.
;; For arguments outside the unit circle, this code works around cases that require http://dlmf.nist.gov/15.8.E8 

;; This method works by dispatching hgfred and nfloat on that result. Possibly, I should have a method that is specialized
;; for the polynomial cases. For now, let's go with this.
(defun gauss-hg-by-nfloat (a b c x)
  (let* ((aa ($rationalize (maxima::to a)))
         (bb ($rationalize (maxima::to b)))
         (cc ($rationalize (maxima::to c)))
         (xx (maxima::to x))
         (bits (if (floatp x)
                   (float-digits x)
                   fpprec))
         (dig (bits-to-digits bits)))

  ;; When aa or bb is a negative integer, it's a polynomial case.
  (cond ((or (every #'integerp (list aa bb cc)) (and (integerp aa) (< aa 0)) (and (integerp bb) (< bb 0))) 
    (let* ((g (gensym))
           (expr ($hgfred (ftake 'mlist aa bb) (ftake 'mlist cc) g))
           (f (ftake '$nfloat expr (ftake 'mlist (ftake 'mequal g xx)) dig))
           (meth 'hgfred-nfloat))

        (if (or t (complex-number-p f #'(lambda (q) (or (floatp q) ($bfloatp q)))))
            (values f bits meth)
            (values nil 0  meth))))
      (t (values nil nil nil)))))

(in-package #:bigfloat)

(defparameter *hg-debug* nil)

(defmacro hg-debug (fmt &rest args)
  `(when *hg-debug*
     (maxima::mtell ,fmt ,@args)))

(defmethod epsilon ((x cl:rational))
  0)

(defmethod epsilon ((x cl:complex))
  (epsilon (cl:realpart x)))

;; check for special cases
(defun gauss-hg-elementary-case (a b c x)
  (let ((bits (if (floatp x)
                  (float-digits x)
                  maxima::fpprec))
        (f
          (cond
            ((equal a c) (expt (- 1 x) (- b)))
            ((equal b c) (expt (- 1 x) (- a)))

            ;; Gauss theorem
            ((and (= x 1)
                  (> (realpart (- c a b)) 0))
             (gamma-quotient c (- c a b) (- c a) (- c b)))

            ((and (= x 1) (<= (realpart (- c a b)) 0))
             'maxima::$inf)

            ;; Kummer theorem
            ((and (= x -1)
                  (equal c (+ 1 a (- b))))
             (gamma-quotient
              (+ 1 a (- b))
              (+ 1 (/ a 2))
              (+ 1 a)
              (+ 1 (/ a 2) (- b))))

            ((zerop x) 1)

            (t nil))))

    (values f (if f bits 0) 'elementary)))


(defun choose-z (x)
  (flet ((rate (z)
           (if (zerop (- z 1))
               1
               (abs (/ z (- z 1))))))

    (cond ((realp x)
           (values (/ x 2) (rate (/ x 2)) t))

          (t 
    (let* ((z (cis (phase (- x 1)))) ; was  ;((z (sqrt (/ (- x 1) (conjugate (- x 1)))))
           (z1 (if (zerop (- 1 z))
                   nil
                   (/ x (- 1 z))))
           (r1 (if z1
                   (rate z1)
                   nil))
           (z2 (if (zerop (+ 1 z))
                   nil
                   (/ x (+ 1 z))))
           (r2 (if z2
                   (rate z2)
                   1)))
      (cond ((and z1 z2)
             (if (< r1 r2)
                 (values z1 r1 nil)
                 (values z2 r2 nil)))
            (z1
             (values z1 r1 nil))
            (t
             (values z2 r2 nil))))))))

#|
Here z is any complex number that allows convergence:

hg([a,b],[c],x) = (1-z)^(-a) * sum(pochhammer(a,k) * hg([-k,b],[c],x/z) * (z/(z-1))^k/k!,k,0,inf));

Define a sequence (hg = hypergeometric)

 hh = k -> hg([-k,b],[c],x/z) * (z/(z-1))^k

A recursion for h is

hh(k+1)*(-((c*z+2*z-b*x-x)/(z-1))-(k*(2*z-x))/(z-1)) +hh(k)*((k*z*(z-x))/(z-1)^2+(z*(z-x))/(z-1)^2)+(k+c+1)*hh(k+2)

 |#

(defun f21-numeric (a b c x)
  (let* ((x-pfaff (/ x (- x 1))))

    (multiple-value-bind (z expo-rate real-case)
        (choose-z (bigfloat::to x))

    (when (> expo-rate 0.9999)
       (return-from f21-numeric (values nil 0)))

      (let ((z-pfaff (choose-z (bigfloat::to x-pfaff))))

        (flet ((algebraic-growth (a b c)
                 (max (realpart (+ b (- c) a -1))
                      (realpart (+ a -1 (- b))))))

          (let* ((candidates

                   (list
                     ;; identity
                     (list a b c x z real-case :plain-1)
                     (list b a c x z real-case :plain-2)

                     ;; Pfaff (exponent -b)
                     (list b (- c a) c x-pfaff z-pfaff real-case :pfaff-b-1)
                     (list (- c a) b c x-pfaff z-pfaff real-case :pfaff-b-2)

                    ;; Pfaff (exponent -a)
                    (list a (- c b) c x-pfaff z-pfaff real-case :pfaff-a-1)
                    (list (- c b) a c x-pfaff z-pfaff real-case :pfaff-a-2)

                    ;; Euler
                    (list (- c a) (- c b) c x z real-case :euler-1)
                    (list (- c b) (- c a) c x z real-case :euler-2)))

                 (best (car (stable-sort candidates #'< :key #'(lambda (w) (algebraic-growth (first w) (second w) (third w)))))))
            (destructuring-bind
                (aa bb cc xx zz rr transform)
                best
               (hg-debug "transform = ~M ~%" transform)
              (let ((qqq
                      (case transform
                         (:plain-1 1)
                         (:plain-2 1)

                         (:pfaff-b-1 (expt (- 1 x) (- b)))
                         (:pfaff-b-2 (expt (- 1 x) (- b)))

                         (:pfaff-a-1 (expt (- 1 x) (- a)))
                         (:pfaff-a-2 (expt (- 1 x) (- a)))

                         (:euler-1 (expt (- 1 x) (- c (+ a b))))
                         (:euler-2 (expt (- 1 x) (- c (+ a b))))

                        (otherwise
                           (error "Unknown transform ~A" transform)))))
                      
                (multiple-value-bind (val bits nterms)
                    (f21-numeric-helper aa bb cc xx zz rr)

                  (values (* qqq val) bits 'maxima::$dlmf_15_15_1 nterms))))))))))

(defun map-abs-onto-complex (x)
  (complex (abs (realpart x)) (abs (imagpart x))))

(defun approx-equal (a b eps)
  (flet ((modified-relative-difference (a b)
          (< (abs (- a b)) (* eps (max 1 (abs a) (abs b))))))
    (and 
      (modified-relative-difference (realpart a) (realpart b))
      (modified-relative-difference (imagpart a) (imagpart b)))))

;; Special casing the real case (that is z = x/2) isn't necessary, but doing so reduces
;; the number of arithmetic operations and possibly keeps the rounding error smaller. The
;; special casing increases the testing burden. So be careful to check both cases.

;; Notice: real-case only depends on if x is real--it does not depend on the other
;; arguments a,b, and c being real.

;; Notes about arithmetic ordering:

;;  (a) Let's compute (x-z) phi^2/z as is (no expanding). When z/2 < x < 2 z, the subtraction x-z is done
;;      with no rounding (I think Sterbenz's Lemma)

;;  (b) Similarly we'll keep (2z -x) phi/z factored

;;  (c) Let's compute  ( (c + 2) z - (b + 1) x)) phi / z as it is, but maybe factoring out a z would be better?
;;  
;;  (d) Evaluate ((k+1) w1 h0 + (w3 + k w4) h1)/(k+cp) as is. 

;; Notes about phi

;;  A fundamental solution set (FSS) for the asymptotic solutions to the recurace for 
;;  k -> 2f1(-k,b,c,x/z) phi, where phi = z/(z-1)
;;
;;    {k -> ((z-x)/(z-1))^k k^(b-c), k -> phi k^(-b)}.
;;
;; For convergence, we need |(z-x)/z| < 1 and |phi| < 1, so both members of the FSS decreases exponentially. 
;; That makes the recursion stable.
;; we need the second member to also decrease. This requires that Re(br) > 0. When Re(br) < 0, we need to

;; One last tiny refinement: When x is real, the auxillary parameter z is x/2. For this case, the 
;; recursion simplifes considerable. So we special case z = x/2.

;; Kahan summation: This code uses Kahan summation for the main summation loop. This method does not 
;; convert an ill-conditioned sum into a well conditioned sum. A compiler that doesn't respect associativity 
;; might simplify the  compensation away.

(defun kahan-add (sum compensator term)
  (let* ((y (- term compensator))
         (new-sum (+ sum y))
         (new-compensator (- (- new-sum sum) y)))
    (values new-sum new-compensator y)))

(defun complex-max-norm (z)
"Return max(|real(z)|, |imag(z)|)."
  ;; special case the complex case--possibly it's a bit faster
  (if (complexp z)
      (max (abs (realpart z)) (abs (imagpart z)))
      (abs z)))
      
;;;;;;;;;;;;;;;;;;;;;;;
;;; ----------------------------------------------------------------------
;;; RUNERR -- value with a running absolute error estimate.
;;;
;;; A RUNERR object represents
;;;
;;;     value ± error
;;;
;;; where ERROR is a conservative absolute error bound satisfying
;;;
;;;     |true-value - value| <= error.
;;;
;;; Design choices:
;;;
;;;  1. The error estimate is an absolute error, not a relative error.
;;;     Relative errors become meaningless near zeros and during
;;;     cancellation, both of which occur naturally in the recurrences
;;;     used by the hypergeometric code.
;;;
;;;  2. Error propagation is performed using first-order forward
;;;     error analysis. This is inexpensive and sufficiently
;;;     conservative for the intended use.
;;;
;;;  3. A floating-point roundoff contribution is added at each
;;;     arithmetic operation.
;;;
;;;  4. A single scalar error bound is maintained even for complex
;;;     values. The error bound is measured using MAP-ABS-ONTO-COMPLEX,
;;;     which provides a conservative magnitude estimate for complex
;;;     quantities.
;;;
;;;  5. This machinery is intended to estimate term-generation error.
;;;     Summation error is handled separately by Kahan compensated
;;;     summation.
;;;
;;; The goal is not a rigorous interval enclosure. Instead, the goal
;;; is a lightweight, pessimistic estimate of the numerical error
;;; accumulated while constructing the terms of the hypergeometric
;;; series.
;;; ----------------------------------------------------------------------

;;; Arithmetic on RUNERR objects.
;;;
;;; The propagated error estimate is intentionally pessimistic.
;;; Since the 2F1 evaluator favors reliability over speed, false
;;; positives (unnecessary reevaluation at higher precision) are
;;; preferred to false negatives (overstated accuracy).

(defstruct (runerr
             (:constructor make-runerr (value error)))
  value
  error)

(defun runner-exact (x)
  (make-runerr x 0))

(defun runner-copy (x)
  (make-runerr (runerr-value x)
               (runerr-error x)))

(declaim (inline runner-mag runner-roundoff))

(defun runner-mag (x)
  "Magnitude used for error propagation."
  (map-abs-onto-complex x))

(defun runner-roundoff (x)
  "Bound for one floating-point rounding operation."
  (* (epsilon x)
     (runner-mag x)))

;;; ----------------------------------------------------------------------
;;; RUNERR -- value with a running absolute error estimate.
;;;
;;; A RUNERR object represents
;;;
;;;     value ± error
;;;
;;; where ERROR is a conservative absolute error bound satisfying
;;;
;;;     |true-value - value| <= error.
;;;
;;; Design choices:
;;;
;;;   1. ERROR is an absolute error, not a relative error.
;;;   2. Errors are propagated using first-order forward analysis.
;;;   3. A roundoff term is added at every arithmetic operation.
;;;   4. Complex magnitudes are measured using MAP-ABS-ONTO-COMPLEX.
;;;   5. RUNERR estimates errors in term generation. Summation errors
;;;      are handled separately by Kahan summation.
;;;
;;; Reliability is preferred over speed. Conservative error estimates
;;; are acceptable if they occasionally trigger unnecessary
;;; reevaluation at higher precision.
;;; ----------------------------------------------------------------------
#| 
(defstruct (runerr
             (:constructor make-runerr (value error)))
  value
  error)

(defun runner-exact (x)
  (make-runerr x 0))

(defun runner+ (x y)
  "Addition with propagated absolute error."
  (let* ((vx (runerr-value x))
         (vy (runerr-value y))
         (v (+ vx vy))
         (e (+ (runerr-error x)
               (runerr-error y)
               (runner-roundoff v))))
    (make-runerr v e)))

(defun runner- (x y)
  "Subtraction with propagated absolute error."
  (let* ((vx (runerr-value x))
         (vy (runerr-value y))
         (v (- vx vy))
         (e (+ (runerr-error x)
               (runerr-error y)
               (runner-roundoff v))))
    (make-runerr v e)))

(defun runner* (x y)
  "Multiplication with propagated absolute error."
  (let* ((vx (runerr-value x))
         (vy (runerr-value y))
         (ex (runerr-error x))
         (ey (runerr-error y))
         (v (* vx vy))
         (e (+ (* (runner-mag vy) ex)
               (* (runner-mag vx) ey)
               (* ex ey)
               (runner-roundoff v))))
    (make-runerr v e)))

(defun runner/ (x y)
  "Division with propagated absolute error."
  (let* ((vx (runerr-value x))
         (vy (runerr-value y))
         (ex (runerr-error x))
         (ey (runerr-error y))
         (den (- (runner-mag vy) ey)))
    (cond
      ((<= den 0)
       (error "RUNNER/: denominator uncertainty includes zero"))
      (t
       (let* ((v (/ vx vy))
              (e (+ (/ ex den)
                    (/ (* (runner-mag vx) ey)
                       (* den den))
                    (runner-roundoff v))))
         (make-runerr v e))))))

(defun runner-scale (a x)
  "Multiply by an exact scalar."
  (let* ((vx (runerr-value x))
         (ex (runerr-error x))
         (v (* a vx))
         (e (+ (* (runner-mag a) ex)
               (runner-roundoff v))))
    (make-runerr v e)))

(defun runner-negate (x)
  "Negation."
  (make-runerr (- (runerr-value x))
               (runerr-error x)))
|#
#|
(defun next-h (k q0 q1)
  (runner/
   (runner+
    (runner-scale (* (+ k 1) w1) q0)
    (runner-scale (+ w3 (* k w4)) q1))
   (runner-exact (+ k cp1))))

 |#

;;;;;;;;;;;;;;;;;;;;;;
(defconstant +max-series-iterations+ 1000000
  "Hard safety ceiling to prevent infinite loops in numerical series.")

(defun f21-numeric-helper (a b c x z real-case)
  (let* ((phi (/ z (- z 1)))
         (h0 1)
         (h1 (if real-case  
              (/ (* (- c (* 2 b)) x) (* c (- x 2)))      ;((c-2*b)*x)/(c*(x-2))
              (/ (- (* c z) (* b x)) (* c (- z 1)))))    ;(c*z-b*x)/(c*(z-1))
         
         (p1 a) 
         ;; initialize the partial sum s to (+ h0 (* p1 h1))) 
         (s (if real-case
                (/ (+ c (* a (- c (* 2 b)) phi)) c) ; equivalent to h0 + p1 * h1, but possibly better.
                (+ h0 (* p1 h1))))
         (c-comp 0)
         (repeat-count 0)
         (sum-abs 0)
         (macheps (epsilon x))
         (ap1 (+ a 1))
         (cp1 (+ c 1))

         (w1 (if real-case
              (* phi phi)                 ; phi^2
              (/ (* (- x z) phi phi) z))) ; (x-z) phi^2 / z

         ;; no w2 because w2 = w1.
         (w3 (if real-case
             (* (- c (* 2 b)) phi)                          ; (c - 2b) phi
             (/ (- (* (+ c 2) z) (* (+ b 1) x)) (- z 1))))  ; ( c z + 2 z - bx - x) phi / z
         (w4 (if real-case
             0                               ; 0
             (/ (* (- (* 2 z) x) phi) z)))   ;(2 z - x) phi/z
         
         (kk 0)
         term-val y-val  hs)
    (flet ((next-h (k h0 h1) (/ (+ (* (+ k 1) w1 h0) (* (+ w3 (* k w4)) h1)) (+ k cp1)))
           (next-cf (k q) (/ (* q (+ ap1 k)) (+ k 2)))) ;
      ;; --- Main loop ---
      (do ((k 0 (1+ k)))
          ((or (>= repeat-count 3)
               (>= k +max-series-iterations+)))
        (declare (type fixnum k)) 
        (setq kk k)

        ;; Save previous h_k
        (setf hs h1)
        (setf h1 (next-h k h0 h1))
        (setf h0 hs)
        (setf p1 (next-cf k p1))
        (setf term-val (* p1 h1))
        ;; accumulate the sum of the absolute values of the real & imaginary parts
        (setf sum-abs (+ sum-abs (map-abs-onto-complex term-val)))
        ;; Kahan accumulation
        (multiple-value-setq (s c-comp y-val)
           (kahan-add s c-comp term-val))
        ;; Convergence check--maybe this should be more closely tied to the asymptotics?
          (if (< (complex-max-norm y-val) (* macheps (max 1 (complex-max-norm s))))
             (incf repeat-count)
             (setf repeat-count 0))))

      ;; --- Compute success or failure using the Kahan summation error bound.
      (flet ((correct-bits (err f)
         (let ((denom (max (abs f) macheps)))
           (if (<= err macheps)
               (- (log macheps 2))
               (max 0 (- (log (/ err denom) 2)))))))

      (let* ((cnst (expt (- 1 z) (- a)))
             (error-bound-real (* 2 macheps  (realpart sum-abs))) ; absolute error, not relative error
             (error-bound-imag (* 2 macheps (imagpart sum-abs)))
             (bits (min 
                     (correct-bits error-bound-real (realpart s))
                      (correct-bits error-bound-imag (imagpart s)))))

        ;; Ensure we didn't bail out purely due to hitting the safety ceiling. Should never happen.
        (when (>= kk +max-series-iterations+)
         (values nil 0 nil))
        (let ((bbits (maxima::$round (maxima::to bits))))
            (values (* cnst s) bbits kk))))))

(defun bf-gamma (x)
  (bigfloat::to
    (maxima::ftake 'maxima::%gamma
                   (maxima::to x))))

(defun gamma-quotient (a b c d)
  "Compute gamma(a) gamma(b)/(gamma(c) gamma(d)) and classify pole situations.

Returns two values:

  value
    When the quotient can be evaluated return gamma(a) gamma(b)/(gamma(c) gamma(d)) else nil.

  status
      :finite The quotient was evaluated normally.
      :zero At least one denominator gamma factor has a pole and each numerator is finite.
      :exceptional  At least one numerator gamma factor has a pole"

  ;; true iff x isn't in the domain of gamma
  (flet ((gamma-pole-p (x)
           (and (integerp x) (<= x 0))))

  (let ((a-pole (gamma-pole-p a))
        (b-pole (gamma-pole-p b))
        (c-pole (gamma-pole-p c))
        (d-pole (gamma-pole-p d)))

    (cond

      ;; denominator pole(s), numerator finite, return 0
      ((and (or c-pole d-pole)
            (not a-pole)
            (not b-pole))
       (values 0 :zero))

      ;; any numerator pole or mixed pole situation
      ((or a-pole
           b-pole)
       (values nil :exceptional))

      ;; ordinary case
      (t
       (values (/ (* (bf-gamma a) (bf-gamma b)) (* (bf-gamma c) (bf-gamma d))) :finite))))))

(defun inner-product-with-error-estimate (a1 a2 x1 x2 bits1 bits2)
  "Compute a1*x1 + a2*x2."
  (let* ((term1 (* a1 x1))
         (term2 (* a2 x2))
         (value (+ term1 term2))

         (err1 (* (abs term1)
                  (expt 2 (- bits1))))

         (err2 (* (abs term2)
                  (expt 2 (- bits2))))

         (abs-error (+ err1 err2))

         (correct-bits
           (if (<= abs-error 0)
               107           ; this needs to be fixed
               (max 0
                    (floor
                     (log (/ (abs value)
                             (max abs-error
                                  (epsilon value)))
                          2))))))

    (values value correct-bits '$hg_connection_id)))

(in-package :bigfloat)
(defun hg-connection-inverse (a b c x)
  (let* ((z (/ 1 x))
         (coeff1 0)
         (coeff2 0)
         (f1 0)
         (f2 0)
         (bits1 0)
         (bits2 0))

    (multiple-value-bind (A1 A-status)
        (gamma-quotient c (- b a) b (- c a))

      (multiple-value-bind (B1 B-status)
          (gamma-quotient c (- a b) a (- c b))

        ;; Logarithmic / exceptional cases.
        (when (or (eq A-status :exceptional)
                  (eq B-status :exceptional))
          (return-from hg-connection-inverse
            (values nil 0 :exceptional)))

        ;; First contribution.
        (unless (eq A-status :zero)
          (setf coeff1 (* A1 (expt (- x) (- a))))
          (multiple-value-bind (ff bb)
              (f21-numeric a
                           (+ a 1 (- c))
                           (+ a 1 (- b))
                           z)
            (setf f1 ff
                  bits1 bb)))

        ;; Second contribution.
        (unless (eq B-status :zero)
          (setf coeff2 (* B1 (expt (- x) (- b))))
          (multiple-value-bind (ff bb)
              (f21-numeric b
                           (+ b 1 (- c))
                           (+ b 1 (- a))
                           z)
            (setf f2 ff
                  bits2 bb)))

        (inner-product-with-error-estimate
         coeff1 coeff2
         f1 f2
         bits1 bits2)))))

(defun hg-connection-reflect (a b c z)
  (let* ((w (- 1 z))
         (coeff1 0)
         (coeff2 0)
         (f1 0)
         (f2 0)
         (bits1 0)
         (bits2 0))

    (multiple-value-bind (A1 A-status)
        (gamma-quotient c (- c a b) (- c a) (- c b))

      (multiple-value-bind (B1 B-status)
          (gamma-quotient c (+ a b (- c)) a b)

        ;; Logarithmic / exceptional cases.
        (when (or (eq A-status :exceptional)
                  (eq B-status :exceptional))
          (return-from hg-connection-reflect
            (values nil 0 :exceptional)))

        ;; First contribution.
        (unless (eq A-status :zero)
          (setf coeff1 A1)
          (multiple-value-bind (ff bb)
              (f21-numeric a
                           b
                           (+ a b (- c) 1)
                           w)
            (setf f1 ff
                  bits1 bb)))

        ;; Second contribution.
        (unless (eq B-status :zero)
          (setf coeff2 (* B1 (expt w (+ c (- a) (- b)))))
          (multiple-value-bind (ff bb)
              (f21-numeric (- c a)
                           (- c b)
                           (+ (- c) a b 1)
                           w)
            (setf f2 ff
                  bits2 bb)))

        (inner-product-with-error-estimate
         coeff1 coeff2
         f1 f2
         bits1 bits2)))))

(defun hg-connection-one-minus-inverse (a b c z)
  (let* ((w (- 1 (/ 1 z)))
         (coeff1 0)
         (coeff2 0)
         (f1 0)
         (f2 0)
         (bits1 0)
         (bits2 0))

    (multiple-value-bind (A1 A-status)
        (gamma-quotient c (- c a b) (- c a) (- c b))

      (multiple-value-bind (B1 B-status)
          (gamma-quotient c (+ a b (- c)) a b)

        ;; Logarithmic / exceptional cases.
        (when (or (eq A-status :exceptional)
                  (eq B-status :exceptional))
          (return-from hg-connection-one-minus-inverse
            (values nil 0 :exceptional)))

        ;; First contribution.
        (unless (eq A-status :zero)
          (setf coeff1 (* A1 (expt z (- a))))
          (multiple-value-bind (ff bb)
              (f21-numeric a
                           (+ a 1 (- c))
                           (+ a b (- c) 1)
                           w)
            (setf f1 ff
                  bits1 bb)))

        ;; Second contribution.
        (unless (eq B-status :zero)
          (setf coeff2 (* B1 (expt z (- a c)) (expt (- 1 z) (- c a b))))
          (multiple-value-bind (ff bb)
              (f21-numeric (- c a)
                           (- 1 a)
                           (+ 1 (- c a b))
                           w)
            (setf f2 ff
                  bits2 bb)))

        (inner-product-with-error-estimate
         coeff1 coeff2
         f1 f2
         bits1 bits2)))))

(defun hg-connection-inverse-of-one-minus (a b c z)
  (let* ((w (/ 1 (- 1 z)))
         (coeff1 0)
         (coeff2 0)
         (f1 0)
         (f2 0)
         (bits1 0)
         (bits2 0))

    (multiple-value-bind (A1 A-status)
        (gamma-quotient c (- b a) b (- c a))

      (multiple-value-bind (B1 B-status)
          (gamma-quotient c (- a b) a (- c b))

        ;; Logarithmic / exceptional cases.
        (when (or (eq A-status :exceptional)
                  (eq B-status :exceptional))
          (return-from hg-connection-inverse-of-one-minus
            (values nil 0 :exceptional)))

        ;; First contribution.
        (unless (eq A-status :zero)
          (setf coeff1 (* A1 (expt (- 1 z) (- a))))
          (multiple-value-bind (ff bb)
              (f21-numeric a
                           (- c b)
                           (+ a (- b) 1)
                           w)
            (setf f1 ff
                  bits1 bb)))

        ;; Second contribution.
        (unless (eq B-status :zero)
          (setf coeff2 (* B1 (expt (- 1 z) (- b))))
          (multiple-value-bind (ff bb)
              (f21-numeric b
                           (- c a)
                           (+ b (- a) 1)
                           w)
            (setf f2 ff
                  bits2 bb)))

        (inner-product-with-error-estimate
         coeff1 coeff2
         f1 f2
         bits1 bits2)))))



;;;Power series centered at zero--I hope this isn't needed.

(defun hypergeometric-2f1-series (a b c x)
  (labels ((kahan-add (term sum comp)
             (let* ((y (- term comp))
                    (new-sum (+ sum y))
                    (new-comp (- (- new-sum sum) y)))
               (values new-sum new-comp))))

    (let ((term 1)
          (sum 1)
          (sum-abs 1)
          (comp 0)
          (repeat-count 0)
          (sum-save)
          (tol (* 128 (epsilon x))) ;; 128 is a "magic number"
          (macheps (epsilon x))
          (kk 0))

         (do ((k 0 (1+ k)))
          ((>= repeat-count 3))
          (setf kk k)
          (setf term (* term (/ (* (+ a k) (+ b k) x) (* (+ c k) (+ k 1)))))
          ;; Running absolute sum for error estimation.
          (setf sum-abs (+ sum-abs (map-abs-onto-complex term)))
          ;; Kahan summation.
          (setq sum-save sum)
          (multiple-value-setq (sum comp)
            (kahan-add term sum comp))
        ;; Require several consecutive equal
        (if (eql sum sum-save)
            (incf repeat-count)
            (setf repeat-count 0)))

          (flet ((correct-bits (err f)
               (if (<= err tol)
                     (- (log tol 2))
                     (max 0 (- (log (abs (/ err f)) 2))))))

      (let* ((error-bound-real (* 2 macheps  (realpart sum-abs))) ; absolute error, not relative error
             (error-bound-imag (* 2 macheps (imagpart sum-abs)))
             (bits (min 
                     (correct-bits error-bound-real (realpart sum))
                      (correct-bits error-bound-imag (imagpart sum)))))

        (let ((bbits (maxima::$round (maxima::to bits))))
            (values sum bbits kk)))))))


(defun exponential-rate (x)
  (multiple-value-bind (z r) (choose-z x)
    (declare (ignore z))
     r))

;; This needs work--each connection formula has a restriction; for example:
;;   (i) the 1/x formula doesn't allow a-b to be an integer
;;   (ii) the 1/(1-x) formula doesn't allow a-b to be an integer
;;   (iii) the 1-x formula doesn't allow c-a-b to be an integer
;;   (iv) the 1-1/x formulat doesn't allow c-a-b to be an integer.

(defun approx-integer-p (x)
  (let ((z (maxima::to x)))
    (eql (maxima::ftake 'maxima::$floor z) (maxima::ftake 'maxima::$ceiling z))))

(defun gauss-hg-large-x (a b c x)
   "Evaluate 2F1(a,b;c;x) using a large-|x| connection formula."

  (when (or (< (abs x) 1) (and (integerp a) (integerp b) (integerp c)))
    (return-from gauss-hg-large-x
      (values nil 0 'gauss-hg-large-x)))

  (let* ((candidates nil))

     (when (not (approx-integer-p (- a b)))
         (push (list (exponential-rate (/ 1 x)) :inverse) candidates)
         (push (list (exponential-rate (/ 1 (- 1 x))) :inverse-of-one-minus) candidates))

      (when (not (approx-integer-p (- c (+ a b))))
           (push (list (exponential-rate (- 1 x)) :reflect) candidates)
           (push (list (exponential-rate (- 1 (/ 1 x))) :one-minus-inverse) candidates))

     (let* ((best (car (stable-sort candidates #'< :key #'car)))
            (transform (cadr best)))
          
    (hg-debug "Large x transform = ~M ~%" transform)

    (case transform
      (:inverse             (hg-connection-inverse a b c x))
      (:reflect             (hg-connection-reflect a b c x))
      (:one-minus-inverse   (hg-connection-one-minus-inverse a b c x))
      (:inverse-of-one-minus (hg-connection-inverse-of-one-minus a b c x)) 
      ((otherwise (values nil 0 'gauss-hg-large-x)))))))


(in-package :maxima)

(defmfun $gauss_series (a b c x)
    (let* ((one (multiplicative-identity a b c x))
           (aa (bigfloat::to (orthopoly-number-coerce a one)))
           (bb (bigfloat::to (orthopoly-number-coerce b one)))
           (cc (bigfloat::to (orthopoly-number-coerce c one)))
           (xx (bigfloat::to (orthopoly-number-coerce x one))))
     
      (maxima::to  (bigfloat::hypergeometric-2f1-series aa bb cc xx))))


(defmfun $gauss_polynomial (a b c x)
   (cond ((maxima::hg-denominator-pole-p a b c) nil)
         ((and (or (and (integerp a) (< a 1))
                    (and (integerp b) (< b 1)))   
                (complex-number-p a #'$ratnump)
                (complex-number-p b #'$ratnump)
                (complex-number-p c #'$ratnump)
                (complex-number-p x #'$ratnump))
          (let ((aa (bigfloat::to a))
                (bb (bigfloat::to b))
                (cc (bigfloat::to c))
                (xx (bigfloat::to x)))
          (maxima::to (bigfloat::gauss-series-polynomial-rational-case aa bb cc xx))))
          (t nil)))

(defun gauss-hg-polynomial-case-p (a b c x)
  (let ((aa (maxima::to a))
        (bb (maxima::to b))
        (cc (maxima::to c))
        (xx (maxima::to x)))
    (and (or (and (integerp aa) (< aa 1)) (and (integerp bb) (< bb 1)))   
         (maxima::complex-number-p aa #'$ratnump)
         (complex-number-p bb #'$ratnump)
         (complex-number-p cc #'$ratnump)
         (complex-number-p xx #'$ratnump))))

(in-package #:bigfloat)

(defun gauss-series-polynomial-rational-case (a b c x)
        (cond
              ((maxima::gauss-hg-polynomial-case-p a b c x)
                (flet ((next-cf (q k) (/ (* q x (+ k a) (+ k b)) (* (+ k 1) (+ k c)))))
                  (let ((term 1) 
                        (s 0)
                        (n (cond ((and (integerp a) (<= a 0)
                                         (integerp b) (<= b 0))
                                         (- (max a b)))

                                        ((and (integerp a) (<= a 0))
                                          (- a))

                                        (t
                                          (- b)))))

               (dotimes (k n)
                 (setq s (+ s term))
                 (setq term (next-cf term k)))
                
                (values (+ s term) 'maxima::$inf 'maxima::$polynomial_case))))
             (t nil)))

