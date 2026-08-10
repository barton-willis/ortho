
## A new orthogonal polynomial package for Maxima

This is a new version of Maxima's package for orthogonal polynomials.  New features:

- Adherence to the Digital Library of Functions.

- The functions are now simplifying functions. This gives the orthogonal polynomials complete noun/verb correctness.

- Each function has basic simplifications built in, a gradient property, an antiderivative property, and a 
  conjugate property.

- Numerical evaluation is based on the recursion relations--the package no longer returns intervals.

- New user-level functions for the function Rodrigues formuula, recursion relation, normalizations, differential equation, and hypergeometric representation. 

- Comprehensive test suite, one file per family, verifying every property and every simplifier behavior.
