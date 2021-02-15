# A theoretical decision procedure for linear integer arithmetic.
This project is a study into decision procedures for linear integer arithmetic, 
also known as weak integer arithmetic and Presburger arithmetic. A useful 
introduction is given by [1].

The algorithm I actually ended up implementing is the naive version of the
second (automata based) algorithm described in the next section. Along with
this, I implemented and verified several other interesting parts:

+ Matrix transposition on vectors.
+ Generic definitions for model theory.
+ Several classic automaton constructions.
+ A depth-first search algorithm that remembers visited nodes.

I also revised a merge sort implementation that was written by Hugo Herbelin,
and started working on a left-leaning red-black tree implementation that could
be used to make depth-first search more efficient.

# Algorithms

## 1. The Presburger-Cooper algorithm.
This algorithm is based on the description by Reddy and Loveland [2], which 
constitutes an improvement over the algorithm given by Cooper, which in 
turn is a big improvement over the original procedure by Presburger.
The algorithm gives an effective decision procedure for formulae in the 
structure `(Z, ≤, +, 0, 1)` using existential quantifier elimination (supported 
by a divisibility predicate). The procedure should be capable of producing a 
constructive proof of any closed formula or its negation.

## 2. Solutions in a regular language.
This algorithm uses results from automata theory together with the observation 
that the elementary relations in weak arithmetic can be decided using automata.
For reference, see for example [3]. I believe this approach is easier to prove 
formally, and I find it more elegant. Furthermore, there already exist several 
optimizations and extensions that make this a more efficient and powerful 
approach than quantifier elimination.

### 2.1. A naive approach.
I first construct a decision procedure using a naive approach: translating
formulae into a language with an addition relation `A(x, y, z) <-> x + y = z`
and the usual equality and inequality relations. It should be straightforward to
apply the automata-based decision method to these formulae.

### 2.2. A generalization.
Presburger arithmetic can be generalized to the so-called "Weak Monadic Logic of
One Successor". A course at EPFL from 2008 explains the details quite well [3].
The construction presented there also covers some of the subtle proof details.

### 2.3. Basic optimizations.
The most important optimization is using more sophisticated automata that 
represent Diophantine equations, as shown in [4]. It is still unclear if a 
verified implementation of this algorithm in Coq will be efficient enough to 
compute actual examples (the theoretical nature of Coq is a severe limitation 
for computation efficiency).


[1]: https://dl.acm.org/doi/10.1145/3242953.3242964
[2]: https://dl.acm.org/doi/10.1145/800133.804361
[3]: https://lara.epfl.ch/w/sav08/using_automata_to_decide_ws1s
[4]: https://link.springer.com/chapter/10.1007/3-540-61064-2_27
