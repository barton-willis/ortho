
## A new orthogonal polynomial package for Maxima

This is a new version of Maxima's package for orthogonal polynomials.  New features:

- The orthogonal polynomials are now simplifying functions. This gives the orthogonal polynomials noun/verb correctness.

- Each function has basic simplifications built in, a gradient property, an antiderivative property, and a 
  conjugate property.

- Numerical evaluation is based on the recursion relations, not the hypergeometric series. The package no longer returns intervals.

- New user-level functions for the function Rodrigues formuula, recursion relation, normalizations, differential equation, and hypergeometric representation. 

- Comprehensive test suite, one file per family, verifying every property and every simplifier behavior.

## Installation Guide

1. **Copy the package directory**  
   Copy the folder containing the `ortho` package files to a location where you normally keep Maxima source files.

2. **Add the package directory to Maxima’s search path**  
   If your package is in `C:/LarryB/maxima/ortho`, for example, append the following lines to your `maxima-init.mac` file:

   ```maxima
   push("C:/LarryB/maxima/ortho/*.lisp", file_search_lisp);
   push("C:/LarryB/maxima/ortho/*.mac", file_search_maxima);
   ```
   If you don't know the location of your `maxima-init.mac` file, enter this line at a Maxima prompt:
   `load("maxima-init.mac");`.  Maxima will print the location of the file.


3. **Remove the autoload property for the old package.** To do this place the following in your file `maxima-init.lisp` file

  ```maxima 
   (dolist (f
         '($assoc_legendre_p
           $assoc_legendre_q
           $chebyshev_t
           $chebyshev_u
           $gen_laguerre
           $hermite
           $intervalp
           $jacobi_p
           $laguerre
           $legendre_p
           $legendre_q
           $orthopoly_recur
           $orthopoly_weight
           $pochhammer
           $spherical_bessel_j
           $spherical_bessel_y
           $spherical_hankel1
           $spherical_hankel2
           $spherical_harmonic
           $ultraspherical))
  (remprop f 'autoload))

  ;; Turn off old orthopoly operator/simplifier hooks
(dolist (pair
         '(( $unit_step     simp-unit-step )
           ( $pochhammer    simp-pochhammer )))
  (let ((f   (first pair))
        (simp (second pair)))
    ;; Remove operator property
    (remprop f 'operators)
    ;; Remove autoload created by (autof 'simp-unit-step "orthopoly")
    (remprop simp 'autoload)))

($load "ortho.lisp")
```

The last line will load the package.


## Basic usage

For rational input, Maxima returns values in rectangular form:

```maxima
(%i1) hermite(5,2/3);
                                     8944
(%o1)                                ────
                                     243
(%i2) hermite(5,2/3 + %i);
                                89584   968 %i
(%o2)                           ───── - ──────
                                 243      81
(%i3) hermite(5,1/(1+%i));
(%o3)                             96 - 16 %i
```

The polynomial `hermite(50,x)` has a zero near `-9.182406958129317`, so maintaining a strict relative error bound for 
numerical evaluation near this zero isn't possible, but Maxima does pretty well:

```maxima 
(%i1) hermite(50,-9.182406958129317);
(%o1)                       - 1.917927837463344e43

(%i2) float(hermite(50,rationalize(-9.182406958129317)));
(%o2)                       - 1.917927837463344e43
```

Another example: Again, Maxima does pretty well:

```maxima

(%i4) hermite(5, 2.0201828704560856);
(%o4)                      - 4.5687075073857527e-14

(%i5) float(hermite(5,rationalize(2.0201828704560856)));
(%o5)                      - 4.5687075073857527e-14
```

The recursion relation for the next case suffers from subtractive cancellation. Internally, the 
method uses a running error to track the error. When it is too large, it starts over using 
higher precision numbers. Example

```maxima 
(%i7) gen_laguerre(300,-200.0, -90.0);
(%o7)                        1.3580967293566024e31

(%i8) gen_laguerre(300,-200, -90);
(%o8) 150013039689886802313558039803109929536431509136849950948615015767238196\
862927143960003975040075670597827319246646656426638870611580086400289989096148\
877386639833546526739589319390999675157616695497669224250245235338829969671962\
956755541685484156213861676816393615026980918230422193777215101738451556176052\
816685125618993318955267070721640284043829459765722899901201689396141798737126\
486372375072653184702176076825708150863647460937500/11045828801970194973975419\
622920458408364890956641665928725865023851943341071601228067030179754210530784\
615700432258710797455664939811738893475593379268102559272262217433136645113354\
951021847436712249376101010161256703732125717837171551822315282435538627769340\
359072795129039200045906217039923058370449043301194174891854876976554384761310\
921530743164605576397929203535643218727071395988737355843524795459

(%i9) float(%);
(%o9)                        1.3580967293566024e31
```
