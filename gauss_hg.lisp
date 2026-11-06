#|
Bugs:

To enable the Lisp debugger set *debugger-hook* to nil.
(%i57) x1 : gauss_hg(5, 2, 8, 100.1+%i*300);

Maxima encountered a Lisp error:

 arithmetic error FLOATING-POINT-OVERFLOW signalled
Operation was (+ 1.6690773232185854e308 1.07237848571282e308).

Another example:

(%i60) x1 : gauss_hg(5, 2, 8, 10.1 *%i);

Maxima encountered a Lisp error:

 arithmetic error FLOATING-POINT-OVERFLOW signalled
Operation was (+ 1.733359062034563e308 6.881829313606321e307).

Also, I notice that  hypergeometric([5, 2], [400], 1.1 *%i) is terribly slow.

-------------------

This problem seems to be plagued with ill-conditioning.  The error bounds, determined only from the 
rounding error from the accumulated sum are too low. 


(%i2) fpprec : 16$

(%i3) x16 : gauss_hg(5, 2, 200, 1.1b0 *%i);
terms summed = 594
error real = +3.964391636638096b1
error imag = +5.312288254652886b1
(%o3)           4.032341784251565b33 %i - 1.045616972502348b34
(%i4) fpprec : 32$

(%i5) x32 : gauss_hg(5, 2, 200, 1.1b0 *%i);
terms summed = 828
error real = +6.5402944902941044264667118802256b1
error imag = +7.6296680660155295964748721884006b0
(%o5) 3.2703079633940393576064191971749b18 %i
                                         + 4.0701663393033246057998071736287b18
(%i6) fpprec : 16$

(%i7) x16 : float(gauss_hg(5, 2, 200, 1.1b0 *%i));
terms summed = 594
error real = +3.964391636638096b1
error imag = +5.312288254652886b1
(%o7)           4.032341784251565e33 %i - 1.0456169725023476e34
(%i8) fpprec : 32$

(%i9) x32 : float(gauss_hg(5, 2, 200, 1.1b0 *%i));
terms summed = 828
error real = +6.5402944902941044264667118802256b1
error imag = +7.6296680660155295964748721884006b0
(%o9)          3.2703079633940393e18 %i + 4.0701663393033247e18
(%i10) fpprec : 64$

(%i11) x64 : float(gauss_hg(5, 2, 200, 1.1b0 *%i));
terms summed = 1132
error real =
        +1.636614337823691036448489113237187224569684257966264544478455207b-16
error imag =
        +4.030680430582487471372204432375245898011500395967579183879851287b-16
(%o11)            1875.9977507270698 %i - 2607.4902414326107
(%i12) fpprec : 128$

(%i13) x128 : float(gauss_hg(5, 2, 200, 1.1b0 *%i));
terms summed = 1550
error real = +1.24324658547893373088564084699391615124239097144670068498622428\
11290083950305609927557321397122280255771235870791940346613358634b-80
error imag = +3.06188792720834245851115513538429116676912076352760661469296845\
83725950715725925504995457939311043682446483974316974395722485281b-80
(%o13)             1875.9977507270698 %i - 2607.490241432611

Standard Maxima is slow and gets a far different answer

(%i14) hypergeometric([5,2],[200],1.1*%i);
(%o14)            0.05486274978439613 %i + 0.9972984783558563
(%i15) time(%);
(%o15)                             [10.5625]

mma gives

N[Hypergeometric2F1[5, 2, 200, 1.1 I], 30] 
0.997298 + 0.0548627 I

-----
I suspect that I've messed up the recursion coefficients for the nonreal case:

(%i95) xe : hypergeometric([2,5],[20], -8.0 + %i*1.0e-8);
(%o95)          2.004953631830538e-10 %i + 0.13526398783340826
(%i96) x1 : gauss_hg(2,5,20,-8.0+%i * 1.0e-8);
terms summed = 292
error real = 7.933410941903656e-8
error imag = 2.2841420516612794e-7
(%o96)         2.0373312686368585e-13 %i + 3.311512399789028e-5
(%i97) x1-xe;
(%o97)         - 2.002916300561901e-10 %i - 0.13523087270941037
(%i98)

I think this has been repaired (sign errors)

(%i102) x1 : gauss_hg(2,5,20,-8.0+%i);
terms summed = 391
error real = 1.0036208410074297e-7
error imag = 1.508782267245387e-7
(%o102)          0.019810773711150982 %i + 0.13298570780108468
(%i103) xe : hypergeometric([2,5],[20], -8.0 + %i);
(%o103)          0.019810775353817225 %i + 0.1329857085454371
(%i104) x1-xe;
(%o104)        - 1.642666242612778e-9 %i - 7.443524130401613e-10
(%i105)
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
           (hg-elem (bigfloat::gauss-hg-elementary-case aa bb cc xx)))

      (if hg-elem
          (maxima::to hg-elem)
      (multiple-value-bind (f e1 e2)
          (bigfloat::f21-numeric aa bb cc xx)
        (declare (ignore e1 e2))
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
               ;(maxima::mtell "transform = ~M ~%" transform)
              (let ((qqq
                      (case transform
                        (:plain 1)

                        (:pfaff-a (expt (- 1 x) (- a)))

                        (:pfaff-b (expt (- 1 x) (- b)))

                        (:euler (expt (- 1 x) (- c (+ a b))))

                        (otherwise (error "Unknown transform ~A" transform)))))

                (multiple-value-bind (val er ei)
                    (f21-numeric-helper aa bb cc xx zz rr)

                  (values (* qqq val)
                          (* (abs qqq) er)
                          (* (abs qqq) ei)))))))))))
          
(defun map-abs-onto-complex (x)
  (complex (abs (realpart x)) (abs (imagpart x))))

(defun approx-equal (a b eps)
  (< (abs (- a b)) (* eps (max 1 (abs a) (abs b)))))

;; Special casing the real case (that is z = x/2) isn't necessary, but doing so reduces
;; the number of arithmetic operations and possibly keeps the rounding error smaller. The
;; special casing increases the testing burden. So be careful to check both cases.

;; Notice: real-case only depends on if x is real--it does not depend on the other
;; arguments a,b, and c being real.
(defun f21-numeric-helper (a b c x z real-case)
  (let* ((sigma (- 1 (epsilon x))); number just a bit less than one
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
         ;;(tol (epsilon x)) need to hook into this
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
             (/ (* (+ (* c z) (* 2 z) (* (- b) x) (- x)) phi) z)))  ; ( c z + 2 z - bx - x) phi
       
         (w4 (if real-case
             0                               ; 0
             (/ (* (- (* 2 z) x) phi) z)))   ;(2 z -x) phi/z
         
         (kk 0)
         term-val y-val t-val hs ssave)
    (flet ((next-h (k h0 h1) (/ (+ (* (+ k 1) w1 h0) (* (+ w3 (* k w4)) h1)) (+ k cp1)))
           (next-cf (k q) (/ (* z (+ ap1 k) q) (* zm1 phi (+ k 2)))))

      ;; --- Main loop ---
      (do ((k 0 (1+ k)))
          ((>= repeat-count 5))
        (setq kk k)

        ;; Save previous h_k
        (setf hs h1)
        (setf h1 (next-h k h0 h1))
        (setf h0 hs)
        (setf p1 (next-cf k p1))
        (setf ssave s)
        (setf term-val (* p1 h1))

        ;(maxima::mtell "k = ~M ; h1 = ~M ~%" k h1)
        ;(maxima::mtell "p1 = ~M ~%" p1)
        ;; accumulate the sum of the absolute values of the real & imaginary parts
        (setf sum-abs (+ sum-abs (map-abs-onto-complex term-val)))
        ;; Kahan accumulation
        (setf y-val (- term-val c-comp))
        (setf t-val (+ s y-val))
        (setf c-comp (- (- t-val s) y-val))
        (setf s t-val)

        ;; Convergence check
        (if (approx-equal s ssave macheps)
            (incf repeat-count)
            (setf repeat-count 0)))

      ;; --- Compute error bounds ---
      (let* ((error-bound-real
               (/ (* 2 macheps
                     (realpart sum-abs))
                  (max macheps
                       (abs (realpart s)))))
             (error-bound-imag
               (/ (* 2 macheps
                     (imagpart sum-abs))
                  (max macheps
                       (abs (imagpart s)))))
             (cnst (expt (- 1 z) (- a))))

        ;;
        (maxima::mtell "terms summed = ~M ~%" kk)
        (maxima::mtell "error real = ~M ~%" error-bound-real)
        (maxima::mtell "error imag = ~M ~%" error-bound-imag)
        ;;ahh, I haven't blended in cnst with the error bounds
        (values (* cnst s)
                error-bound-real
                error-bound-imag)))))

