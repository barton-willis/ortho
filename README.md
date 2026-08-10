
## A new orthogonal polynomial package for Maxima

This is a new version of Maxima's package for orthogonal polynomials.  New features:

- The orthogonal polynomials are now simplifying functions. This gives the orthogonal polynomials noun/verb correctness.

- Each function has basic simplifications built in, a gradient property, an antiderivative property, and a 
  conjugate property.

- Numerical evaluation is based on the recursion relations, not the hypergeometric series. The package no longer returns intervals.

- New user-level functions for the function Rodrigues formuula, recursion relation, normalizations, differential equation, and hypergeometric representation. 

- Comprehensive test suite, one file per family, verifying every property and every simplifier behavior.

## Current status

With the `ortho` package loaded, Maxima’s core testsuite and the share testsuites now run to completion with thirty failures. Of
these 20 syntactic mismatches. I am currently reviewing the remaining ten failures. Most appear to be syntactic as well.

All new `ortho` test files run to completion. Some pass cleanly; others expose missing conjugate or gradient properties, and the like.

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

The last line will load the package--you might need to give the full patch to the package `ortho`. Doing so is the safest route.


## Basic usage

Symbolic and numerical evaluation of the Jacobi polynomials:

```maxima
(%i6) jacobi_p(5,-2,-2,x);
                                  5      3
                               3 x  - 6 x  + 3 x
(%o6)                          ─────────────────
                                      16
(%i7) jacobi_p(5,-2,-2,1/2);
                                      27
(%o7)                                 ───
                                      512
(%i8) jacobi_p(5,-2,-2,0.5);
(%o8)                             0.052734375
(%i9)
```

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
The same for binary64 and bigfloat evaluation:

```maxima
(%i1) ultraspherical(5,-3, 0.23);
(%o1)                               - 1.38

(%i2) ultraspherical(5,-3, 0.23+%i);
(%o2)                    - 6.0 %i - 1.3800000000000001

(%i3) ultraspherical(5,-3, 0.23b0+%i);
(%o3)                         - 6.0b0 %i - 1.38b0

(%i4) gen_laguerre(3,0.4, 5.0);
(%o4)                          3.170666666666667

(%i5) gen_laguerre(3,0.4, 5.0 + 4.0*%i);
(%o5)             12.346666666666668 %i + 15.970666666666666

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
