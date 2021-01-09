# Decision procedures for linear integer arithmetic.
This project is a study into decision procedures for linear integer arithmetic, 
also known as weak integer arithmetic and Presburger arithmetic.

## The improved Presburger-Cooper algorithm.
This algorithm is based on the description by Reddy and Loveland [1], which is a 
small but significant improvement over the algorithm given by Cooper, which in 
turn is a big improvement over the original procedure by Presburger.

The algorithm gives an effective decision procedure for formulas in the 
structure `(Z, <, +, 0, 1)`, although the language is enriched with extra 
relations to enable quantifier elimination. The procedure also produces a 
constructive proof of the formula or its negation.

[1]: https://dl.acm.org/doi/10.1145/800133.804361
