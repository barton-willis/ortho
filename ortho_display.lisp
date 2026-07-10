(defprop $hermite tex-hermite tex)

(defun tex-hermite (x l r)
  (tex-sub-and-super-scripted-function "H" `(0) nil nil nil 1 x l r))

(setf (get '$hermite 'dimension) 'dimension-hermite)

(defun dimension-hermite (form result)
 (dimension-function
   (dimension-sub-and-super-scripted-function '|$h| `(1) nil nil 2 form)
   result))