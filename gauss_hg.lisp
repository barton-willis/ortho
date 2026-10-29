(in-package :maxima)

(defmfun $gauss_hg (a b c x)
    (multiple-value-bind (f e1 e2)
      (bigfloat::f21-numeric (bigfloat::to a) (bigfloat::to b) (bigfloat::to c) (bigfloat::to x))
      (maxima::to f)))

(in-package #:bigfloat)

(defun choose-z (x)
  (flet ((rate (z) (if (zerop (- z 1))
                        1
                       (abs (/ z (- z 1))))))
  (let* ((xb (conjugate x))
         (mag (abs (- x 1)))
         (im (- x xb))
         (z1 (if (zerop im) 
               (/ x -2) 
               (/ (* x (+ xb mag -1)) im)))
         (r1 (rate z1))

         (z2 (if (zerop im)
              (/ x -2)
              (/ (* x (- xb (+ mag) 1) im))))
         (r2 (rate z2)))
    (if (< r1 r2)
        (values z1 r1)
        (values z2 r2)))))

#|
Here z is any complex number that allows convergence:

hg([a,b],[c],x) = (1-z)^(-a) * sum(pochhammer(a,k) * hg([-k,b],[c],x/z) * (z/(z-1))^k/k!,k,0,inf));

Define a sequence (hg = hypergeometric)

 hh = k -> hg([-k,b],[c],x/z) * (z/(z-1))^k

A recursion for h is

hh(k+1)*(-((c*z+2*z-b*x-x)/(z-1))-(k*(2*z-x))/(z-1)) +hh(k)*((k*z*(z-x))/(z-1)^2+(z*(z-x))/(z-1)^2)+(k+c+1)*hh(k+2)

 |#

(defun f21-numeric (a b c x)

  (multiple-value-bind (z1 r1)
      (choose-z (bigfloat::to x))
      (multiple-value-bind (z2 r2)
         (choose-z (bigfloat::to (/ x (- x 1))))

  (maxima::mtell "r1 = ~M ; r2 = ~M ~%" r1 r2)
  
  (cond ((< r1 r2) ; no pfaff transformation
         ;(when (< (realpart b) (realpart a))
          ; (rotatef a b))
           (maxima::mtell "z1 = ~M ~%" z1)
           (f21-numeric-helper a b c x z1))
        (t ;;pfaff transform
           (let* ((aa a)
                  (bb (- c b))
                  (cc c)
                  (xx (/ x (- x 1))))
            ;(when (< (realpart bb) (realpart aa))
             ;   (rotatef aa bb))    
           (* (expt (- 1 x) (- aa)) (f21-numeric-helper aa bb cc xx z2))))))))
          
(defun map-abs-onto-complex (x)
  (complex (abs (realpart x)) (abs (imagpart x))))

(defun f21-numeric-helper (a b c x z)
  (let* ((h0 1)
         (h1 (/ (* (- 1 (/ (* b x) (* c z))) z) (- z 1))) ; (1 - bx/(c z)) z /(z-1)
         (p1 a)
         (s (+ h0 (* p1 h1)))
         (c-comp 0)
         (repeat-count 0)
         (tol (epsilon x))
         (sum-abs 0)
         (macheps (epsilon x))
         (zm1 (- z 1))
         (ap1 (+ a 1))
         (alpha (/ (- (* 2 z) x) zm1))
         (beta (/ (- (* (+ c 2) z)
                      (* (+ b 1) x))
                  zm1))
         (gamma (/ (* z (- z x))
                   (* zm1 zm1)))

         term-val y-val t-val hs ssave)

    (flet ((next-h (k h0 h1)
             (/ (- (* h1 (+ (* k alpha) beta))
                   (* h0 gamma (+ k 1)))
                (+ k c 1)))
           (next-cf (k p0) (/ (* (+ ap1 k) p0) (+ k 2))))

      ;; --- Main loop ---
      (do ((k 0 (1+ k)))
          ((>= repeat-count 5))

        ;; Save previous h_k
        (setf hs h1)
        (setf h1 (next-h k h0 h1))
        (setf h0 hs)

        ;; p1 <-- (a+k+1)/(k+2) * p1
        (setf p1 (next-cf k p1))

        (setf ssave s)

        (setf term-val (* p1 h1))

        ;; accumulate the sum of the absolute values
        ;; of the real & imaginary parts
        (setf sum-abs
              (+ sum-abs
                 (map-abs-onto-complex term-val)))

        ;; Kahan accumulation
        (setf y-val (- term-val c-comp))
        (setf t-val (+ s y-val))
        (setf c-comp (- (- t-val s) y-val))
        (setf s t-val)

        ;; Convergence check
        (if (or (= s ssave)
                (< (abs (- s ssave)) tol))
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

        (values (* cnst s)
                error-bound-real
                error-bound-imag)))))