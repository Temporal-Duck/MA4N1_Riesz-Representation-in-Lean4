# MA4N1 Riesz representation theorem in Lean4

Our project for MA4N1 is formalising Riesz Representation Theorem as taught in the Warwick maths module MA3G7 : Functional Analysis 1. Riesz representation theorem states the following:
**Theorem 6.11 (Riesz representation).** Let $H$ be a Hilbert space. For every bounded linear operator $G \in H^*$, there exists unique $y \in H$ such that $G = F_y$. That is, for all $x \in H$, we have

$$
G(x) = \langle x, y \rangle = F_y(x)
$$

and $\|G\|_{H^*} = \|F_y\|_{H^*} = \|y\|$.<br>
In MA3G7, we work with complex inner product spaces and Hilbert spaces, so we do the same here. Here is the outline of the formalisation:

## Inner product spaces

Firstly we define things such as orthogonality, orthogonal complements of sets, the operator norm, and convexity of sets. Then we prove a few useful inequalities that will be used for bigger results later on. These include the Cauchy-Schwarz inequality, parallelogram law, and the fact that the operator norm is a bound for functionals.

## Hilbert spaces and Riesz representation theorem

Recall that a Hilbert space is a complete inner product space. In this section, our main results are closest_point, orthogonal_decompose, and Riesz representation theorem. The former two are as follows:
**Proposition 5.16.** Let $A$ be a non-empty closed convex subset of a Hilbert space $H$. Then for every $x \in H$ there is a unique $a^* \in A$ such that

$$
\|x - a^*\| = \inf_{a \in A} \|x - a\|.
$$

**Theorem 5.20.** Let $U$ be a closed linear subspace of $H$. Then every $x \in H$ can be uniquely written as

$$
x = u + u^* \text{ for } u \in U \text{ and } u^* \in U^{\perp},
$$

i.e., $H = U \oplus U^{\perp}$.<br>
These are used directly in the proof of Riesz representation theorem.

## Methodology

In terms of the formalisations, we haven't deviated too far from the proofs provided in the MA3G8 notes. One thing we realised was that complex inner products in LEAN, by convention, are conjugate linear in the first entry. This is different to the notes which doesn't change the proofs that much but it was something to be careful of when formalising. For example, OrthogonalComplement was initially defined as $X^{\perp} = \{ y \in H : \forall x \in X \ \langle x, y \rangle = 0 \} $, which is wrong (should be $\langle x, y \rangle = 0$).<br>
As we practiced with LEAN, we became more familiar with how to use certain tools to look for tactics and theorems. One of these was [LeanSearch](https://leansearch.net/), which is an AI powered lean search engine. Where we had to look for theorems like Cauchy Schwarz inequality, the Mathlib docs wouldn't be helpful because its name, 'inner_mul_inner_self_le' is entirely different. LeanSearch can search this theorem with the query 'Cauchy Schwarz'. 