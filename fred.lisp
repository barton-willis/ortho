(defmacro def-integral (name arglist &rest entries)
  "Define integral properties for a function `name`. Here `arglist` is (x1,x2, ... ,xn),
  and `entries` is a list of expressions, one per argument. For an undefined antiderivative, 
  use nil."
    `(putprop ',name
            (list ',arglist ,@entries)
            'integral))

(def-simplifier fred (n x)
    (give-up))

(def-integral %fred ($n $x)
  nil
  #$$ fred(n+1,x)/(2*(n+1)) - fred(n-1,x)/(2*n) $)