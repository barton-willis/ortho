
## A new orthogonal polynomial package for Maxima

This is a new version of Maxima's package for orthogonal polynomials. New features:

- The orthogonal polynomials are now simplifying functions.

- Each function has basic simplifications built in, a gradient property, an antiderivative property, and a 
  conjugate property.

- Numerical evaluation is based on the recursion relations, not the hypergeometric series. 

- The package no longer returns intervals for numerical evaluation.

- New user-level functions for the Rodrigues formula, recursion relation, normalizations, differential equation, and hypergeometric representation
  for the orthogonal polynomials.

- Comprehensive test suite, one file per family, verifying every property and every special value.

## Current status

With the `ortho` package loaded, Maxima’s core testsuite and the share testsuites now run to completion with thirty failures. Of
these 20 syntactic mismatches. I am currently reviewing the remaining ten failures. Most appear to be syntactic as well.

Here is a typical syntactic failure:
```maxima
********************* rtesthyp.mac: Problem 85 (line 357) *********************
Input:
hgfred([- 2, - 4], [], z)

Result:
    2
12 z  + 8 z + 1
This differed from the expected result:
     2      1         2
12 (─── + ───── + 1) z
    3 z       2
          12 z
```
Arguably, the new value is better - it doesn't have the spurious singularity at zero.

All new `ortho` test files run to completion. Some pass cleanly; others expose missing conjugate or gradient properties, and the like.

## Installation Guide

Maxima's `orthopoly` package resides in the share library, but it autoloads. Installing the new package requires
deactivating the autoload property for the old package.  Alternatively, you could simply replace the files in your
share library, but doing so is not easily reversed.  Here is how to install the new package by deactivating the autoload property:

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

($load "<full path to ortho.lisp>")
```

The last line will load the package. 


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
### Status

The `ortho` package is not ready for serious work. Here are the results of the tests: 

❌ (some failures) ✔️ (no failures) ⏳ (not yet done)
 
| Function               | Test Results            | Runtime        | Comment(s)            |
|------------------------|-------------------------|----------------|------------------------|
| chebyshev_t            | ✔️ (51/51 pass)         | 2.5 seconds    |                        |
| chebyshev_u            | ❌ (45/51 pass)         | 2.6 seconds    |                        |
| hermite                | ✔️ (67/67 pass)         | 9.1 seconds   |                        |
| jacobi_p               | ✔️ (40/40 pass)         | 2.0 seconds    |                        |
| laguerre               | ✔️ (41/41 pass)         | 13.6 seconds   |                        |
| legendre               | ⏳                      |                |                        |
| assoc_legendre_p       | ❌ (21/34 pass)         |  0.02 seconds  |                        |
| legendre_q             | ⏳                      |                |                        |
| assoc_legendre_q       | ❌ (28/35 pass)         | 0.4 seconds    |                        |
| spherical_bessel_j     | ✔️ (29/29 pass)         | 3.3 seconds    |                        |
| spherical_bessel_y     | ✔️ (24/24 pass)         | 0.4 seconds    |  need more tests       |
| spherical_hankel1      | ✔️ (27/27 pass)         | 0.8 seconds    |                        |
| spherical_hankel2      | ❌ (4/29 pass)          |                |                        |
| spherical_harmonic     | ⏳                      |                |                        |
| ultraspherical         | ✔️ (45/45 pass)         | 4.0 seconds    |                        |
| pochhammer             | ✔️ (35/35) pass         | 0.1 second     |                        |
|------------------------|-------------------------|----------------|------------------------|
### Controlling subtractive cancellation

Computing the orthogonal polynomials using the recursion relation is algorithmically simple. But 
to avoid subtractive cancellation, we must be vigilant. Here is an example: Let's compute the 
Laguerre polynomials using recursion and binary64 numbers.  In Maxima, a simple why to do this
is to use a memoizing function; for example

```maxima
(%i1)	a : -200.0$

(%i2)	x : -90.0$

(%i3)	L[n] := if n = 0 then 1.0 elseif n = 1 then a+1-x else ((2*n+a-1)/n  - x/n) * L[n-1] - (n-1+a) * L[n-2]/n$

(%i4)	L[50];
(%o4)	6.163505607863041*10^35

(%i5)	gen_laguerre(50,-200,-90);
(%o5)	17385421159024287119634798567925009237310328534245553393384246091596/28207033894550201495240534048951

(%i6)	float(%);
(%o6)	6.163505607863035*10^35

(%i7)	L[150];
(%o7)	6.743887046036587*10^38

(%i8)	float(gen_laguerre(150,-200,-90));
(%o8)	1.512947155869013*10^16 
```

The value of the 50-th degree polynomial is okay, but value of the 150-th degree case is off by a factor of 10^22.


To mitigate subtractive cancellation, the `orth` package uses a running error to track the error. When it is too large, it starts over using 
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


