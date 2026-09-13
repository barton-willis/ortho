
## A new orthogonal polynomial package for Maxima

This release provides a redesigned and expanded implementation of orthogonal polynomial families in Maxima. Key improvements include:

- The orthogonal polynomials are now simplifying functions, including built‑in simplifications, derivative and antiderivative rules, and correct handling of complex conjugation.

- Numerical evaluation no longer returns interval objects, providing accurate floating‑point values instead.

- New user-level functions for the Rodrigues formula, recursion relation, normalizations, differential equation, and hypergeometric representation for the orthogonal polynomials.

- Comprehensive test suite, one file per family, covering symbolic identities, recurrence relations, differential equations, and special values.

## Current status

With the `ortho` package loaded, Maxima’s testsuite runs with twenty-eight failures. Of these
failures, all but seven are syntactic mismatches.

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
The new value is better because it doesn't have the spurious singularity at zero.

One testsuite failure that is actually a success is:

```maxima
******************* rtest_hypgeo.mac: Problem 43 (line 324) *******************

Input:
                                       - s t
(assume(i1 > 0), niceindices(specint(%e      laguerre(n, t), t)))


Result:
     1 n
(1 - ─)
     s
────────
   s

This differed from the expected result:
 n
____                                   - i - 1
╲     gamma(i + 1) pochhammer(- n, i) s
 ⟩    ────────────────────────────────────────
╱                         2
‾‾‾‾                    i!
i = 0

```

## Installation Guide

This guide explains how to install the new **ortho** package without modifying Maxima’s share library. The key requirement is to prevent Maxima from autoloading the old `orthopoly` package from the share library, since its functions would otherwise override the new ones. The steps below show how to install the new package by adding it to Maxima’s search path and removing the autoload properties associated with the old package.

1. **Copy the package directory**  
   Copy the folder containing the `ortho` package files to a location where you normally keep Maxima source files.
   Actually, any readable directory is fine.

2. **Add the package directory to Maxima’s search path**  
   If your package is in `C:/LarryB/maxima/ortho`, for example, append the following lines to your `maxima-init.mac` file:

   ```maxima
   push("C:/LarryB/maxima/ortho/*.lisp", file_search_lisp);
   push("C:/LarryB/maxima/ortho/*.mac", file_search_maxima);
   ```
   If you don't know the location of your `maxima-init.mac` file, enter this line at a Maxima prompt:
   `load("maxima-init.mac");`.  Maxima will print the location of the file.


3. **Remove the autoload property for the old package.** To do this place the following in your file `maxima-init.lisp` file



  ```lisp
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

For rational input, including complex rationals, Maxima returns values in rectangular form

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


### Status

The `ortho` package is almost ready for serious work. Here are the results of the tests: 

❌ (some failures) ✔️ (no failures) ⏳ (not yet done)
 
| Function               | Test Results            | Runtime        | Comment(s)            |
|------------------------|-------------------------|----------------|------------------------|
| chebyshev_t            | ✔️ (51/51 pass)         | 2.5 seconds    |                        |
| chebyshev_u            | ✔️ (52/52 pass)         | 6.4 seconds    |                        |
| hermite                | ✔️ (67/67 pass)         | 9.1 seconds    |                        |
| jacobi_p               | ✔️ (40/40 pass)         | 2.0 seconds    |                        |
| laguerre               | ✔️ (41/41 pass)         | 13.6 seconds   |                        |
| legendre_p             | ✔️ (55/55 pass)         |  0.3 seconds   |                        |
| assoc_legendre_p       | ✔️ (30/30 pass)         |  0.2 seconds   |                        |
| legendre_q             | ✔️ (43/43 pass)         |  0.4 seconds   |                        |
| assoc_legendre_q       | ✔️ (35/35 pass)         | 0.4 seconds    |                        |
| spherical_bessel_j     | ✔️ (28/28 pass)         | 10.3 seconds   |                        |
| spherical_bessel_y     | ✔️ (23/23 pass)         | 0.7 seconds    |  need more tests       |
| spherical_hankel1      | ✔️ (26/26 pass)         | 5.4 seconds    |                        |
| spherical_hankel2      | ✔️ (26/26 pass)         | 5.2 seconds   |                         |
| spherical_harmonic     | ✔️ (29/29 pass)         |26.0 seconds    |                        |
| ultraspherical         | ✔️ (45/45 pass)         | 4.0 seconds    |                        |
| pochhammer             | ✔️ (35/35) pass         | 0.1 second     |                        |

All the functions need more tests, not just `spherical_bessel_y`.

### Controlling subtractive cancellation

Computing orthogonal polynomials through their three‑term recurrence is straightforward, but avoiding the loss of accuracy caused by subtractive cancellation requires a safeguard.  In the `ortho` package, the safeguard is a running error estimate that approximately bounds the rounding error. When the estimated error becomes too large, the computation is automatically retried at higher precision. Specifically, for a machine epsilon of $\epsilon$, we require that the running error bound satisfy the modified relative error condition

```math
|\text{error bound}| < \epsilon \max(\epsilon, |x|)
```
A comment in the source code describes the mechanism in detail.

The polynomial `hermite(50,x)` has a zero near `-9.182406958129317`, so maintaining a strict relative error bound for 
numerical evaluation near this zero isn't possible, but the modified relative error condition does pretty well:

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

To illustrate how loss of accuracy arises, consider computing the Laguerre polynomials using forward recursion in binary64 arithmetic. In Maxima, one simple way to experiment with this behavior is to implement the recurrence as a memoizing function; for example

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
The huge discrepancy is due to subtractive cancellation.

## Related Software

The following packages may be of interest for comparison, experimentation, or further study:

- **orthopolynom (R package)**  
  A comprehensive collection of classical orthogonal polynomials, including recurrence relations, derivatives, integrals, values, and roots.  
  https://cran.r-project.org/package=orthopolynom

- **ClassicalOrthogonalPolynomials.jl (Julia)**  
  A Julia package providing classical orthogonal polynomials using operator-based abstractions and three-term recurrences.  
  https://github.com/JuliaApproximation/ClassicalOrthogonalPolynomials.jl

- **MATLAB Symbolic Math Toolbox**  
  Provides classical orthogonal polynomials such as Legendre, Jacobi, Chebyshev, Laguerre, Hermite, and Gegenbauer.  
  https://www.mathworks.com/help/symbolic/polynomials.html

- **SymPy / mpmath (Python)**  
  Provides orthogonal polynomials through mpmath, including Legendre, Chebyshev, Laguerre, Hermite, and others.  
  https://omz-software.com/pythonista/sympy/modules/mpmath/functions/orthogonal.html

- **SciPy (Python)**  
  Provides orthogonal polynomials in `scipy.special`, including Legendre, Chebyshev, Laguerre, Hermite, Gegenbauer, and Jacobi families.  
  https://docs.scipy.org/doc/scipy/reference/special.html

- **Maple**  
  Provides symbolic and numeric orthogonal polynomials through functions such as `orthopoly`, `LegendreP`, `ChebyshevT`, `LaguerreL`, and others.  
  https://www.maplesoft.com/support/help/Maple/view.aspx?path=orthopoly

- **Mathematica / Wolfram Language**  
  Provides extensive support for orthogonal polynomials, including Legendre, Jacobi, Chebyshev, Laguerre, Hermite, Gegenbauer, and many others.  
  https://reference.wolfram.com/language/guide/SpecialFunctions.html

- **Chebfun (MATLAB/Python)**  
  Provides numerical computing with functions, including orthogonal polynomial expansions and Chebyshev-based spectral methods.  
  https://www.chebfun.org/

- **A Toolbox for Real Orthogonal Polynomials (SoftwareX, 2026)**  
  A published software toolbox covering real orthogonal polynomials.  
  https://www.sciencedirect.com/science/article/pii/S2352711026000397

If you know of other such packages, let me know and I will append them to this list.


