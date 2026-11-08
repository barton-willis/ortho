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
(%o162)                              [0.0]

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
           (requested-bits (if ($bfloatp xx)
                               fpprec
                               (float-digits (realpart xx)))))

      (if hg-elem
          (maxima::to hg-elem)
      (multiple-value-bind (f bits)
          (bigfloat::f21-numeric aa bb cc xx)
        (declare (ignore bits))
        (maxima::to f)))))

(in-package #:bigfloat)

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

    (print `(z = ,z))

    (when (> expo-rate 0.9999)
      (maxima::merror (intl:gettext "Exponential rate = ~M ; series converges too slowly") expo-rate))

      (let ((z-pfaff (choose-z (bigfloat::to x-pfaff))))

        (flet ((score (a b c)
                 (max (realpart (+ b (- c) a -1))
                      (realpart (+ a -1 (- b))))))

          (let* ((candidates
                   (list
                     ;; plain
                     (list a b c x z real-case :plain)

                     ;; swap
                     (list b a c x z real-case :plain)

                     ;; Pfaff
                     (list (- c a) b c x-pfaff z-pfaff real-case :pfaff-b)

                     ;; swapped Pfaff
                     (list a (- c b) c x-pfaff z-pfaff real-case :pfaff-a)

                     ;; Euler
                     (list (- c a) (- c b) c x z real-case :euler)

                     ;; swapped Euler
                     (list (- c b) (- c a) c x z real-case :euler)))

                 (best
                   (reduce
                     (lambda (best candidate)
                       (if (> (score (first candidate)
                                     (second candidate)
                                     (third candidate))
                              (score (first best)
                                     (second best)
                                     (third best)))
                           candidate
                           best))
                     (rest candidates)
                     :initial-value (first candidates))))
            (destructuring-bind
                (aa bb cc xx zz rr transform)
                best
               (maxima::mtell "transform = ~M ~%" transform)
              (let ((qqq
                      (case transform
                        (:plain 1)

                        (:pfaff-a (expt (- 1 x) (- a)))

                        (:pfaff-b (expt (- 1 x) (- b)))

                        (:euler (expt (- 1 x) (- c (+ a b))))

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

;; Notes about arithmeatic ordering:
;;  (a) Let's compute (x-z) phi^2/z as is (no expanding). When z/2 < x < 2 z, the subtraction x-z is done
;;      with no rounding (I think Sterbenz's Lemma)

;;  (b) Similarly we'll keep (2z -x) phi/z factored

;;  (c) Let's compute  ( (c z + 2 z) - (b x + x)) phi / z as it is, not as ( (c + 2) z - (b+1) x) phi /z or ...
;;      I should think about this more.
;;  
;;  (d) Evaluate ((k+1) w1 h0 + (w3 + k w4) h1)/(k+cp)as is. Some would partially factor the
;;      numerator with respect to k.

(defun f21-numeric-helper (a b c x z real-case)
  (let* ((sigma (- 1 (* 8 (epsilon x)))); number just a bit less than one
         (phi (* (max 1 (abs (/ z (- z x)))) sigma))
        
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
         (tol (* 128 (epsilon x))) ;; 128 is a "magic number"
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
             (* (- c (* 2 b)) phi)                                  ; (c - 2b) phi
            (/ (* (- (+ (* c z) (* 2 z)) (+ (* b x) x)) phi) z)))  ; ( c z + 2 z - bx - x) phi / z
       
         (w4 (if real-case
             0                               ; 0
             (/ (* (- (* 2 z) x) phi) z)))   ;(2 z -x) phi/z
         
         (kk 0)
         term-val y-val t-val hs ssave)
    (flet ((next-h (k h0 h1) (/ (+ (* (+ k 1) w1 h0) (* (+ w3 (* k w4)) h1)) (+ k cp1)))
           (next-cf (k q) (/ (* z (+ ap1 k) q) (* zm1 phi (+ k 2)))))
   ;;;  (maxima::mtell "sigma = ~M ~%" sigma)
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

       ;;; (maxima::mtell "h1 = ~M ~%" h1)
        ;; accumulate the sum of the absolute values of the real & imaginary parts
        (setf sum-abs (+ sum-abs (map-abs-onto-complex term-val)))
        ;; Kahan accumulation
        (setf y-val (- term-val c-comp))
        (setf t-val (+ s y-val))
        (setf c-comp (- (- t-val s) y-val))
        (setf s t-val)

        ;; Convergence check--maybe this should be more closely tied to the asymptotics?
        (if (approx-equal s ssave macheps)
            (incf repeat-count)
            (setf repeat-count 0)))

      ;; --- Compute success or failure using the Kahan summation error bound.
      (flet ((correct-bits (err f)
               (if (<= err tol)
                     (- (log tol 2))
                     (max 0 (- (log (abs (/ err f)) 2))))))

      (let* ((cnst (expt (- 1 z) (- a)))
             (error-bound-real (* 2 macheps  (realpart sum-abs))) ; absolute error, not relative error
             (error-bound-imag (* 2 macheps (imagpart sum-abs)))
             (bits (min 
                     (correct-bits error-bound-real (realpart s))
                      (correct-bits error-bound-imag (imagpart s)))))

        (maxima::mtell "s = ~M ~%" (maxima::$float (maxima::to s)))
        (maxima::mtell "sum-abs = ~M ~%" (maxima::$float (maxima::to sum-abs)))
        (maxima::mtell "terms summed = ~M ~%" kk)
       
        (let ((bbits (maxima::$round (maxima::to bits))))
            (maxima::mtell "bits = ~M ~%" bbits)
            (values (* cnst s) bbits)))))))

