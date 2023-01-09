# Arrow polynomial calculator

This is a program written in [Lean 4](https://github.com/leanprover/lean4) to calculate polynomial
invariants of virtual knots, in particular the cabled arrow polynomials, which are generalizations
of the cabled virtual Jones polynomials. It was create as part of the work that went toward the paper

> Kyle A. Miller, *The homological arrow polynomial for virtual links*, (2022). [arXiv:2207.02427 [math.GT]](https://arxiv.org/abs/2207.02427) https://doi.org/10.1142/S0218216523500050

This program is meant to be reasonably efficient, and it's meant to be independent verification
of calculations made by Virtual KnotFolio, a version of
[KnotFolio](https://kmill.github.io/knotfolio/) for virtual knots (to be released sometime soon).
While Lean 4 is a language designed for formal verification of programs, these features are only
lightly used in this program -- for now, it's used as a fancier (and more fun) version of Haskell,
using dependent types here and there to encode program invariants.

The data source for this is Jeremy Green's
[table of virtual knots](https://www.math.toronto.edu/drorbn/Students/GreenJ/index.html).
The `unoriented-6.txt` file contains all the virtual knots up to six crossings, modulo all
symmetries.

I ran this program for all virtual knots up to five crossings, computing the first, second, and
third cabled arrow polynomials. The 2565 knots took 2.83 days of computer time, which over 12
threads took only 6 hours 17 minutes.  This invariants are sufficient to distinguish all
virtual knots up to five crossings except for nine pairs of 5-crossing virtual knots (four of which
are distinguishable by Alexander polynomials).

As an experiment, I also ran this program on just 5.196 and 5.1662 for up to the fourth cabled
arrow polynomials, the calculation of which took 16.2 hours (or, across two threads, 10.58 hours).
This was a pair that was not distinguishable by the first through third cabled polynomials, but this
computation distinguishes them.

To compare, a reasonably efficient JavaScript implementation of the cabled arrow polynomials took
9.5 days of computer time (done in parallel over 1.5 days) to calculate only the first through third
cabled arrow polynomials of virtual knots up to four crossings along with the first and second
cabled arrow polynomials of virtual knots with five crossings.

The algorithm is inherently exponential in the number of crossings, with the kth cabled arrow
polynomial of an n-crossing knot effectively being the arrow polynomial of an n * k^2 crossing knot.
So, for 4th cabled arrow polynomials of 5-crossing knots we are effectively handling 80-crossing
knots. This requires some caching of intermediate computations that are reused multiple times.
