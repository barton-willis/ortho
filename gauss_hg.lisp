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
(defmfun $gauss_hg (a b c x)
    (let ((one (multiplicative-identity  a b c x)))
      (setq a (orthopoly-number-coerce a one)
            b  (orthopoly-number-coerce b one)
            c  (orthopoly-number-coerce c one)
            x  (orthopoly-number-coerce x one))

     ;(mtell "a = ~M ; b = ~M ; c = ~M ; x = ~M ~%" a b c x)

    (multiple-value-bind (f e1 e2)
      (bigfloat::f21-numeric (bigfloat::to a) (bigfloat::to b) (bigfloat::to c) (bigfloat::to x))
      ;(mtell "e1 = ~M ; e2 = ~M ~%" e1 e2)
      (maxima::to f))))

(in-package #:bigfloat)

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
                 (values z2 r2 nil)
            (z1
             (values z1 r1 nil)
            (t
             (values z2 r2 nil)))))))))))

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
(defun f21-numeric-helper (a b c x z real-case)
  (maxima::mtell "a = ~M ; b = ~M ; c = ~M ; x = ~M z = ~M ; real =  ~%" a b c x real-case)

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
         (tol (epsilon x))
         (sum-abs 0)
         (macheps (epsilon x))
         (zm1 (- z 1))
         (ap1 (+ a 1))
         (cp1 (+ c 1))

         (w1 (if real-case
              (* phi phi)                 ; phi^2
              (/ (* (- z x) phi phi) z))) ; (z-x) phi^2 / z

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
        ;(maxima::mtell "k = ~M ~%" kk)
        ;(maxima::mtell "error real = ~M ~%" error-bound-real)
        ;(maxima::mtell "error imag = ~M ~%" error-bound-imag)
        ;;ahh, I haven't blended in cnst with the error bounds
        (values (* cnst s)
                error-bound-real
                error-bound-imag)))))

