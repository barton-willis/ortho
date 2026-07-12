
(defprop $unit_step "\\Theta" texword)
;; TeX a function with subscripts and superscripts.  The string fn is the
;; function name, the list sub holds the positions of the subscripts, the list
;; sup holds the positions of the superscripts, and i is the position of the 
;; function argument.  When b1 is true, the subscript is surrounded by parens;
;; when b2 is true, the superscript is surrounded by parens.  The lists sub and
;; sup may be nil, but the function must have at least on argument.

(defun tex-sub-and-super-scripted-function (fn sub b1 sup b2 i x l r)
  (setq x (cdr x))
  (let ((lo) (hi) (s1) (s2))
    (setq s1 (if b1 `("\\left(")  nil))
    (setq s2 (if b1 `("\\right)") nil))
    (dolist (i sub)
      (setq lo (cons (nth i x) lo)))
    (setq lo (if lo (tex-list (nreverse lo) s1 s2 ",") nil))
    (setq s1 (if b2 `("\\left(")  nil))
    (setq s2 (if b2 `("\\right)") nil))
    (dolist (i sup)
      (setq hi (cons (nth i x) hi)))
    (setq hi (if hi (tex-list (nreverse hi) s1 s2 ",") nil))
    (append l `(,fn)
	    (if lo `("_{",@lo "}") nil)
	    (if hi `("^{" ,@hi "}") nil)	   
	    `(,@(tex-list (nthcdr i x) `("\\left(") `("\\right)") ","))
	    r)))
	    
(defun dimension-sub-and-super-scripted-function (fn sub sup b2 k x)
  (let ((lo) (hi) (form))
    (dolist (i sub)
      (setq lo (cons (nth i x) lo)))
    (setq lo (nreverse lo))
    (dolist (i sup)
      (setq hi (cons (nth i x) hi)))
    (setq hi (nreverse hi))
    (cond ((null hi)
	   (setq form `((,fn simp array) ,@lo)))
	  (b2
	   (setq form `((mexpt) ((,fn simp array) ,@lo) ((mprogn) ,@hi))))
	  (t
	   (setq form `((mexpt) ((,fn simp array) ,@lo) ,@hi))))
    `((,form simp) ,@(nthcdr k x))))

(defprop $pochhammer tex-pochhammer tex)

(defun tex-pochhammer (x l r)
  (setq x (mapcar #'(lambda (s) (tex s nil nil nil nil)) (cdr x)))
  (append l 
	  `("\\left(")
	  (nth 0 x)
	  `("\\right)_{")
	  (nth 1 x)
	  `("}")
	  r))

(setf (get '$pochhammer 'dimension) 'dimension-pochhammer)

(defun dimension-pochhammer (form result)
  (setq form `(( ((mprogn) ,(nth 1 form)) simp array) ,(nth 2 form)))
  (dimension-array form result))

(defprop $jacobi_p tex-jacobi-poly tex)

(defun tex-jacobi-poly (x l r)
  (tex-sub-and-super-scripted-function "P" `(0) nil `(1 2) t 3 x l r))

(setf (get '$jacobi_p 'dimension) 'dimension-jacobi-p)

(defun dimension-jacobi-p (form result)
  (dimension-function
   (dimension-sub-and-super-scripted-function '|$p| `(1) `(2 3) t 4 form)
   result))
   
(defprop $ultraspherical tex-ultraspherical tex)

(defun tex-ultraspherical (x l r)
  (tex-sub-and-super-scripted-function "C" `(0) nil `(1) t 2 x l r))

(setf (get '$ultraspherical 'dimension) 'dimension-ultraspherical)

(defun dimension-ultraspherical (form result)
    (dimension-function
     (dimension-sub-and-super-scripted-function '|$c| `(1) `(2) t 3 form)
     result))

(defprop $chebyshev_t tex-chebyshev-t tex)

(defun tex-chebyshev-t (x l r)
  (tex-sub-and-super-scripted-function "T" `(0) nil nil nil 1 x l r))

(setf (get '$chebyshev_t 'dimension) 'dimension-chebyshev-t)

(defun dimension-chebyshev-t (form result)
  (dimension-function
   (dimension-sub-and-super-scripted-function '|$t| `(1) nil nil 2 form)
   result))

(defprop $chebyshev_u tex-chebyshev-u tex)

(defun tex-chebyshev-u (x l r)
  (tex-sub-and-super-scripted-function "U" `(0) nil nil nil 1 x l r))

(setf (get '$chebyshev_u 'dimension) 'dimension-chebyshev-u)

(defun dimension-chebyshev-u (form result)
  (dimension-function
   (dimension-sub-and-super-scripted-function '|$u| `(1) nil nil 2 form)
   result))

(defprop $legendre_p tex-legendre-p tex)

(defun tex-legendre-p (x l r)
  (tex-sub-and-super-scripted-function "P" `(0) nil nil nil 1 x l r))

(setf (get '$legendre_p 'dimension) 'dimension-legendre-p)

(defun dimension-legendre-p (form result)
  (dimension-function
   (dimension-sub-and-super-scripted-function '|$p| `(1) nil nil 2 form)
   result))

(defprop $legendre_q tex-legendre-q tex)

(defun tex-legendre-q (x l r)
  (tex-sub-and-super-scripted-function "Q" `(0) nil nil nil 1 x l r))

(setf (get '$legendre_q 'dimension) 'dimension-legendre-q)

(defun dimension-legendre-q (form result)
 (dimension-function
   (dimension-sub-and-super-scripted-function '|$q| `(1) nil nil 2 form)
   result))

(defprop $assoc_legendre_q tex-assoc-legendre-q tex)

(defun tex-assoc-legendre-q (x l r)
  (tex-sub-and-super-scripted-function "Q" `(0) nil `(1) nil 2 x l r))

(setf (get '$assoc_legendre_q 'dimension) 'dimension-assoc-legendre-q)

(defun dimension-assoc-legendre-q (form result)
 (dimension-function
   (dimension-sub-and-super-scripted-function '|$q| `(1) `(2) nil 3 form)
   result))

(defprop $assoc_legendre_p tex-assoc-legendre-p tex)

(defun tex-assoc-legendre-p (x l r)
  (tex-sub-and-super-scripted-function "P" `(0) nil `(1) nil 2 x l r))

(setf (get '$assoc_legendre_p 'dimension) 'dimension-assoc-legendre-p)

(defun dimension-assoc-legendre-p (form result)
  (dimension-function
   (dimension-sub-and-super-scripted-function '|$p| `(1) `(2) nil 3 form)
   result))

(defprop $gen_laguerre tex-gen-laguerre tex)

(defun tex-gen-laguerre (x l r)
  (tex-sub-and-super-scripted-function "L" `(0) nil `(1) t 2 x l r))

(setf (get '$gen_laguerre 'dimension) 'dimension-gen-laguerre)

(defun dimension-gen-laguerre (form result)
  (dimension-function
   (dimension-sub-and-super-scripted-function '|$l| `(1) `(2) t 3 form)
   result))

(defprop $laguerre tex-laguerre tex)

(defun tex-laguerre (x l r)
  (tex-sub-and-super-scripted-function "L" `(0) nil nil nil 1 x l r))

(setf (get '$laguerre 'dimension) 'dimension-laguerre)

(defun dimension-laguerre (form result)
  (dimension-function
   (dimension-sub-and-super-scripted-function '|$l| `(1) nil nil 2 form)
   result))

(defprop $spherical_hankel1 tex-spherical-hankel-1 tex)

(defun tex-spherical-hankel-1 (x l r)
  (tex-sub-and-super-scripted-function "h^{(1)}" `(0) nil nil nil 1 x l r))

(setf (get '$spherical_hankel1 'dimension) 'dimension-spherical-hankel-1)

(defun dimension-spherical-hankel-1 (form result)
  (let ((form1 `((mexpt) (($\h simp array) ,(nth 1 form)) 
		 (1))))
    (dimension-function `((,form1 simp) ,(nth 2 form)) result)))

(defprop $spherical_hankel2 tex-spherical-hankel-2 tex)

(defun tex-spherical-hankel-2 (x l r)
  (tex-sub-and-super-scripted-function "h^{(2)}" `(0) nil nil nil 1 x l r))

(setf (get '$spherical_hankel2 'dimension) 'dimension-spherical-hankel-2)

(defun dimension-spherical-hankel-2 (form result)
  (let ((form1 `((mexpt) (($\h simp array) ,(nth 1 form))  (2))))
    (dimension-function `((,form1 simp) ,(nth 2 form)) result)))
  
(defprop $spherical_bessel_j tex-spherical-bessel-j tex)

(defun tex-spherical-bessel-j (x l r)
  (tex-sub-and-super-scripted-function "j^{(2)}" `(0) nil nil nil 1 x l r))

(setf (get '$spherical_bessel_j 'dimension) 'dimension-spherical-bessel-j)

(defun dimension-spherical-bessel-j (form result)
  (let ((form1 `(($\j simp array) ,(nth 1 form)))) 
    (dimension-function `((,form1 simp) ,(nth 2 form)) result)))

(defprop $spherical_bessel_y tex-spherical-bessel-y tex)

(defun tex-spherical-bessel-y (x l r)
  (tex-sub-and-super-scripted-function "y^{(2)}" `(0) nil nil nil 1 x l r))

 (setf (get '$spherical_bessel_y 'dimension) 'dimension-spherical-bessel-y)

(defun dimension-spherical-bessel-y (form result)
  (let ((form1 `(($\y simp array) ,(nth 1 form)))) 
    (dimension-function `((,form1 simp) ,(nth 2 form)) result)))

(defprop $spherical_harmonic tex-spherical-harmonic tex)

(defun tex-spherical-harmonic (x l r)
  (tex-sub-and-super-scripted-function "Y" `(0) nil `(1) nil 2 x l r))

(setf (get '$spherical_harmonic 'dimension) 'dimension-spherical-harmonic)

(defun dimension-spherical-harmonic (form result)
 (dimension-function
  (dimension-sub-and-super-scripted-function '|$y| `(1) `(2) nil 3 form)
  result))
  
(defprop $hermite tex-hermite tex)

(defun tex-hermite (x l r)
  (tex-sub-and-super-scripted-function "H" `(0) nil nil nil 1 x l r))

(setf (get '$hermite 'dimension) 'dimension-hermite)

(defun dimension-hermite (form result)
 (dimension-function
   (dimension-sub-and-super-scripted-function '|$h| `(1) nil nil 2 form)
   result))