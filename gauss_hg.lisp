#|
Formerly bugs:

(%i57) x1 : gauss_hg(5, 2, 8, 100.1+%i*300);
(%i60) x1 : gauss_hg(5, 2, 8, 10.1 *%i);

Bugs

Super fast but not accurate:

(%i161) gauss_hg(5, 2, 400, 1.1 *%i);
terms summed = 656
error real = 21.300983803696976
error imag = 13.177664094457308
(%o161)       - 3.5633407489482256e97 %i - 1.3915927000179146e96
(%i162) time(%);
(%o162)                              [0.0]gauss_hg(5, 2, 400, 1.1 *%i);

(%i163) hypergeometric([5, 2], [400], 1.1 *%i);
(%o163)          0.027482674787230012 %i + 0.9993215451548428
(%i164) time(%);
(%o164)                           [97.421875]


This problem seems to be plagued with ill-conditioning.  The error bounds, determined only from the 
rounding error from the accumulated sum are too low. 

(%i43) gauss_hg(5, 2, 4000, 0.9);
sigma = 0.9999999999999991
Maxima encountered a Lisp error:

 arithmetic error FLOATING-POINT-OVERFLOW signalled
Operation was (* 1.0201699566444049e305 -18787.500000000004).

Plus hypergeometric([5, 2], [4000], 0.9) is slow.  Ahh, I thought that large 'c' gives good 
converence.  Do I have something backwards?

Automatically continuing.


 |#

(in-package :maxima)

;; For many other possibilities, see  https://link.springer.com/article/10.1007/s11075-026-02436-2 

(defun multiplicative-identity (&rest a)
  "Return the appropriate multiplicative identity (1 for rational numbers, 1.0d0 for binary64, and 1.0b0 for bigfloats)
  for the numbers in the list a."
  (flet ((local-one (s) 
           (cond ((complex-number-p s #'$ratnump) 1.0d0)
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

(defmfun $gauss_hg (a b c x)
   ;; Check for an undefined case--not a polynomial case and a negative integer value for c.
   (when (hg-denominator-pole-p a b c)
     (maxima::merror
          (intl:gettext
            "gauss_hg(~M,~M,~M,~M) is undefined because ~M is a nonpositive integer.") a b c x c))

    (let* ((one (multiplicative-identity a b c x))
           (aa (bigfloat::to (orthopoly-number-coerce a one)))
           (bb (bigfloat::to (orthopoly-number-coerce b one)))
           (cc (bigfloat::to (orthopoly-number-coerce c one)))
           (xx (bigfloat::to (orthopoly-number-coerce x one)))
           (hg-elem (bigfloat::gauss-hg-elementary-case aa bb cc xx))
           (requested-bits (if ($bfloatp (maxima::to (bigfloat::realpart xx)))
                               fpprec
                               (float-digits (maxima::to (bigfloat::realpart xx))))))

      (declare (ignore requested-bits))

      (if hg-elem
          (maxima::to hg-elem)
      (multiple-value-bind (f bits)
          (bigfloat::f21-numeric aa bb cc xx)
        (declare (ignore bits))
        (maxima::to f)))))

(in-package #:bigfloat)

(defparameter *hg-debug* t)

(defmacro hg-debug (fmt &rest args)
  `(when *hg-debug*
     (maxima::mtell ,fmt ,@args)))


;; check for special cases
(defun gauss-hg-elementary-case (a b c x)
  (cond
    ((equal a c) (expt (- 1 x) (- b)))
    ((equal b c) (expt (- 1 x) (- a)))
    (t nil)))

(defun choose-z (x)
  (flet ((rate (z)
           (if (zerop (- z 1))
               1
               (abs (/ z (- z 1))))))

    (cond ((realp x)
           (values (/ x 2) (rate (/ x 2)) t))

          (t 
    (let* ((z (sqrt (/ (- x 1) (- (conjugate x) 1))))
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
      (maxima::merror (intl:gettext "Exponential rate = ~M ; series converges too slowly") expo-rate))

      (let ((z-pfaff (choose-z (bigfloat::to x-pfaff))))

        (flet ((algebraic-growth (a b c)
                 (max (realpart (+ b (- c) a -1))
                      (realpart (+ a -1 (- b))))))

          (let* ((candidates
                   (list
                     ;; plain-1 & plain-2
                     (list a b c x z real-case :plain-1)
                     (list b a c x z real-case :plain-2)

                     ;; pfaff-1 & pfaff-2
                     (list b (- c a) c x-pfaff z-pfaff real-case :pfaff-1)
                     (list (- c a) b c x-pfaff z-pfaff real-case :pfaff-2)

                     ;; euler-1 * euler-2
                     (list (- c a) (- c b) c x z real-case :euler-1) 
                     (list (- c b) (- c a) c x z real-case :euler-2)))
                 (best
                   (reduce
                     (lambda (best candidate)
                       (if (< (algebraic-growth (first candidate)
                                     (second candidate)
                                     (third candidate))
                              (algebraic-growth (first best)
                                     (second best)
                                     (third best)))
                           candidate
                           best))
                     (rest candidates)
                     :initial-value (first candidates))))
            (destructuring-bind
                (aa bb cc xx zz rr transform)
                best
               (hg-debug "transform = ~M ~%" transform)
              (let ((qqq
                      (case transform
                        (:plain-1 1)
                        (:plain-2 1)
                        (:pfaff-1 (expt (- 1 x) (- b)))
                        (:pfaff-2 (expt (- 1 x) (- b)))
                        (:euler-1 (expt (- 1 x) (- c (+ a b))))
                        (:euler-2 (expt (- 1 x ) (- c (+ a b))))
                        (otherwise (error "Unknown transform ~A" transform)))))

                (multiple-value-bind (val bits)
                    (f21-numeric-helper aa bb cc xx zz rr)

                  (values (* qqq val) bits))))))))))

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
;;  (d) Evaluate ((k+1) w1 h0 + (w3 + k w4) h1)/(k+cp) as is. Some would partially factor the
;;      numerator with respect to k.

;; Notes about phi

;;  A fundamental solution set (FSS) for the asymptotic solutions to the recreance for k -> 2f1(-k,b,c,x/z) is
;;
;;    {k -> ((z-x)/z)^k k^(b-c), k -> k^(-b)}.
;;
;; For convergence, we need |(z-x)/z| < 1, so the first member of the FSS decreases exponentially. For stability,
;; we need the second member to also decrease. This requires that Re(br) > 0. When Re(br) < 0, we need to
;; use a trick. For this case, we recursively compute k -> phi 2F1(-k,b,c,x/z), where phi is a nonzero 
;; complex number. Now a FSS is
;;
;;    {k -> phi^k ((z-x)/z)^k k^(b-c), k -> phi^k k^(-b)}.
;;
;; For convergence we already have |(z-x)/z|< 1, so we only need to choose |phi| < 1.  Of course, to 
;; compensate for phi in the hypergeometric term, the term pochhammer(a,k) * (z/(z-1))^k / k! needs
;; a factor of 1/phi.  The value of phi does not affect convergence, just the stability of the recursion
;; for the hypergeometric term.

;; Conjecture: Making |phi| << 1 could possibly make the term k -> phi 2f1(-k,b,c,x/z) decrease very
;; fast and the other factor k -> pochhammer(a,k) (z/(z-1))^k / (phi^k k!) grow very fast. This could
;; cause problems with overflow or underflow. We'll take |phi| to be very close to one.

;; One last tiny refinement: Including phi, for the real case (including all arguments real)
;; the recursion for the hypergeometric term is
;; 
;;  hh(k+2)=((k+1)*hh(k)*phi^2+(c-2*b)*hh(k+1)*phi)/(k+c+1)
;;
;; To avoid subtractive cancellation in the numerator, its best to require that
;;  
;;   sign((k+1) phi^2) = (sign((c-2b) phi)
;;
;; So we would like sign(phi) = sign(c-2b). We'll include this tiny refinement. But I don't
;; have an example where all this matters.

;; The refinement in the value of phi is done according to asymptotics, but the bulk of the 
;; ill conditioning happens long before the asymptotic solution settles in.  So no, altering phi 
;; is fun, but it doesn't fix this problem.

;; Last observation:  When c = 2 b, z = x/2, the recursion is simply
;;
;;    hh(k+2)=((k+1)*hh(k)*phi^2)/(k+2*b+1)
;; 
;; Kahan summation: This code uses Kahan summation for the main summation loop. This method does not 
;; convert an ill-conditioned sum into a well conditioned sum. A compiler that doesn't respect associativity 
;; might simplify the  compensation away.

(defun kahan-add (sum compensator term)
  (let* ((y (- term compensator))
         (new-sum (+ sum y))
         (new-compensator (- (- new-sum sum) y)))
    (values new-sum new-compensator)))

(defun complex-max-norm (z)
"Return max(|real(z)|, |imag(z)|)."
  ;; special case the complex case--possibly it's a bit faster
  (if (complexp z)
      (max (abs (realpart z)) (abs (imagpart z)))
      (abs z)))
      
(defun f21-numeric-helper (a b c x z real-case)
  (let* ((phi (* 
               (if (> (realpart b) 0)
                  1 
                  (- 1 (* 8 (epsilon x)))) ; the "8" is a magic number

              (if (and real-case (realp c) (realp b) (< (realpart (- c (* 2 b))) 0))
                  -1
                  1)))
        
         (h0 1)
         (h1 (if real-case  
              (* (- 1 (/ (* 2 b) c)) phi) ; (1-2b/c) phi
              (* (- 1 (/ (*  b x) (* c z))) phi))) ; (1 - bx/(cz)) phi
         
         (p1 (if real-case
              (/ (* a x) (- x 2))
              (/ (* a z) (- z 1))))

         (s (+ h0 (* p1 h1)))
         (c-comp 0)
         (repeat-count 0)
         (sum-abs 0)
         (macheps (epsilon x))
         (zm1 (- z 1))
         (ap1 (+ a 1))
         (cp1 (+ c 1))

         (w1 (if real-case
              (* phi phi)                 ; phi^2
              (/ (* (- x z) phi phi) z))) ; (x-z) phi^2 / z

         ;; no w2 because w2 = w1.
         (w3 (if real-case
             (* (- c (* 2 b)) phi)                          ; (c - 2b) phi
            (/ (* (- (* (+ c 2) z) (+ (* b x) x)) phi) z))) ; ( c z + 2 z - bx - x) phi / z
         (w4 (if real-case
             0                               ; 0
             (/ (* (- (* 2 z) x) phi) z)))   ;(2 z -x) phi/z
         
         (kk 0)
         term-val y-val t-val hs ssave)
    (flet ((next-h (k h0 h1) (/ (+ (* (+ k 1) w1 h0) (* (+ w3 (* k w4)) h1)) (+ k cp1)))
           (next-cf (k q) (/ (* z (+ ap1 k) q) (* zm1 phi (+ k 2)))))
      ;; --- Main loop ---
      (do ((k 0 (1+ k)))
          ((>= repeat-count 3))
        (setq kk k)

        ;; Save previous h_k
        (setf hs h1)
        (setf h1 (next-h k h0 h1))
        (setf h0 hs)
        (setf p1 (next-cf k p1))
        (setf ssave s)
        (setf term-val (* p1 h1))

        ;; accumulate the sum of the absolute values of the real & imaginary parts
        (setf sum-abs (+ sum-abs (map-abs-onto-complex term-val)))
        ;; Kahan accumulation
        (setf y-val (- term-val c-comp))
        (setf t-val (+ s y-val))
        (setf c-comp (- (- t-val s) y-val))
        (setf s t-val)

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

        (hg-debug "s = ~M ~%" (maxima::$float (maxima::to s)))
        (hg-debug "sum-abs = ~M ~%" (maxima::$float (maxima::to sum-abs)))
        (hg-debug "terms summed = ~M ~%" kk)
       
        (let ((bbits (maxima::$round (maxima::to bits))))
            (hg-debug "bits = ~M ~%" bbits)
            (values (* cnst s) bbits))))))

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

    (values value correct-bits)))

#|
(%i2)	hg_1_over_x(a,b,c,x) :=
	block(
	  [A,B],
	
	  A : gamma(c)*gamma(b-a)/(gamma(b)*gamma(c-a)),
	  B : gamma(c)*gamma(a-b)/(gamma(a)*gamma(c-b)),
	
	  print( [hypergeometric([a, a-c+1], [a-b+1], 1/x),  gauss_hg(a, a-c+1, a-b+1, 1/x)]),
	  A*(-x)^(-a)
	    * hypergeometric([a, a-c+1], [a-b+1], 1/x)
	
	+ B*(-x)^(-b)
	    * hypergeometric([b, b-c+1], [b-a+1], 1/x)
	)$


 |#
(defun hg-connection-1/x (a b c x)
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
          (return-from hg-connection-1/x
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


#| 
(defun hg-connection-1/(1-z) (a b c z)

  (let* ((w (/ (- 1 z)))

         (A (/ (* (gamma c)
                  (gamma (- b a)))
               (* (gamma b)
                  (gamma (- c a)))))

         (B (/ (* (gamma c)
                  (gamma (- a b)))
               (* (gamma a)
                  (gamma (- c b))))))

    (multiple-value-bind (f1 bits1)
        (f21-numeric a
                     (- c b)
                     (+ a 1 (- b))
                     w)

      (multiple-value-bind (f2 bits2)
          (f21-numeric b
                       (- c a)
                       (+ b 1 (- a))
                       w)

        (let* ((term1 (* A
                         (expt (- 1 z) (- a))
                         f1))

               (term2 (* B
                         (expt (- 1 z) (- b))
                         f2))

               (result (+ term1 term2))

               (err1 (* (abs term1)
                        (expt 2 (- bits1))))

               (err2 (* (abs term2)
                        (expt 2 (- bits2))))

               (relerr (/ (+ err1 err2)
                          (max *macheps*
                               (abs result))))

               (bits (max 0
                          (floor (- (log relerr 2))))))

          (values result bits))))))

|#
#| 

Power series centered at zero--I hope this isn't needed.

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
|#
(in-package :maxima)

(defmfun $gauss_hg_large_x (a b c x)
   (let* ((one (multiplicative-identity a b c x))
           (aa (bigfloat::to (orthopoly-number-coerce a one)))
           (bb (bigfloat::to (orthopoly-number-coerce b one)))
           (cc (bigfloat::to (orthopoly-number-coerce c one)))
           (xx (bigfloat::to (orthopoly-number-coerce x one))))
      (maxima::to (bigfloat::hg-connection-1/x aa bb cc xx))))

      