# Pairwise-independent designs, entropy, and repair

This project connects probability laws on sign vectors with Hadamard matrices. It studies exact entropy bounds, near-optimal designs, and obstructions to repairing them by small changes.

A law on $`d`$ sign variables (each taking values $`+1`$ or $`-1`$) is unbiased and pairwise independent when every variable has mean zero and every pair has zero correlation. Its collision probability is $`C(\mu)=\sum_x\mu(x)^2`$. A Hadamard law is the uniform law on rows of a sign Hadamard matrix with an all-ones column, after deleting that column; a Hadamard mixture is a convex combination of such laws.

## Main results

### 1. Nearly optimal entropy can coexist with maximal distance from Hadamard mixtures

There are dimensions $`n_j-1`$ and exactly unbiased pairwise-independent laws $`\mu_j`$ for which 

$$
n_jC(\mu_j)\longrightarrow1,\qquad\inf_{\nu\in\mathcal H_{n_j}}\|\mu_j-\nu\|_{\rm TV}\longrightarrow1,
$$

 where $`\mathcal H_n`$ is the set of Hadamard mixtures and total variation is half the sum of absolute probability differences. The laws can be strict local maxima of collision probability, while their excess above the minimum entropy tends to zero for all positive orders of Rényi entropy, a family that includes Shannon entropy and the entropy determined by the largest atom as limits.

### 2. Sharp entropy bounds with Hadamard equality cases

For $`d\ge2`$, put $`N=4\lceil(d+1)/4\rceil`$. Every unbiased pairwise-independent law on $`d`$ signs satisfies 

$$
C(\mu)\le1/N,\qquad H_2(\mu)\ge\log N,\qquad H(\mu)\ge\log N,
$$

 where $`H_2=-\log C`$ and $`H`$ is Shannon entropy. Equality in the collision bound forces a uniform law on $`N`$ atoms whose augmented rows extend to a Hadamard matrix. Attainment of either entropy bound is equivalent to Hadamard existence at order $`N`$.

### 3. No fixed-size collection of observations suffices for local repair

For every fixed $`R`$, infinitely many known Hadamard orders $`n\equiv4\pmod8`$ have this property: every $`n`$-observation sign array on $`n-1`$ variables with zero means and zero pairwise correlations is isolated under any nonzero replacement of at most $`R`$ observations that preserves those moments. Thus a uniform bound on the number of observations changed cannot connect all such designs.

Read the [paper](paper/main.pdf) for proofs and citations, or [further results](RESULTS.md) for the rest of the mathematical development. The [technical guide](TECHNICAL.md) covers building the Lean proofs, dependencies, formalization coverage, and submission checks.

Joshua Mark · [ORCID](https://orcid.org/0009-0003-5905-2382)
