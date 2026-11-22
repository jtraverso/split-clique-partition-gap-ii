# Additive Gaps for Edge-Clique Partitions of Split Graphs II. Stability of Host Transfer

**Juan Pablo Traverso Gianini**<br>
Independent researcher, Santiago, Chile<br>
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)<br>
[ORCID 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

*Draft v0.1 for private review · November 22, 2026*

## Abstract

A host assignment on a split graph can realize the difference between two packing optima on its clique as the additive gap between its integral and fractional clique partition numbers. We study incomplete assignments. If the host neighborhoods are independent in the residual graph and a proper assignment misses $L$ of its required pairs, the two gaps differ by at most $2L$. The estimate holds in both directions on the original graph. In particular, deleting $q$ crossing edges from the split graphs with nearly quadratic gap constructed in the first paper changes their gap by at most $2q$. We also bound $L$ from the lists of available hosts. The bound counts a matching at each positive level of list deficiency. It gives a linear upper bound on the gap when the largest deficiencies are confined to a small set of core vertices, even if the total number of missing crossing edges is quadratic.

## 1. Partial host assignments

In a clique partition of a finite simple graph $G$, each edge belongs to exactly one of the chosen cliques. Write $\operatorname{cp}(G)$ for the least number of cliques in such a partition. A fractional clique partition assigns a nonnegative weight to each clique so that the weights at each edge sum to one. Its minimum total weight is $\operatorname{cp}^*(G)$. Throughout, the cliques used as pieces have at least two vertices and may have arbitrary order. We write

$$
\Delta(G)=\operatorname{cp}(G)-\operatorname{cp}^*(G).
$$

Every integral partition is feasible for the fractional problem, so $\Delta(G)\ge0$. The split graphs in the first paper [1] have a clique $V$, called the core, and an independent set $H$. A vertex $h\in H$ is a *host*, with neighborhood $N_h\subseteq V$. In that construction, a graph $B$ on $V$ determines which core pairs require a host. Every such pair $uv$ has a designated host $h$ for which $huv$ is a triangle. If the edge $hu$ is deleted, the pair $uv$ is still present in the core, but the designated triangle is gone. The question is how much of the original gap survives.

Fix a graph $B$ on $V$ and put $J=\binom{V}{2}\setminus E(B)$. All pairs of $V$ are edges of the split graph $G$, including the pairs in $J$. For $Q\subseteq V$ with $|Q|\ge2$, let $e_B(Q)$ be the number of edges of $B$ with both ends in $Q$, and give $Q$ the score

$$
w(Q)=2e_B(Q)-\binom{|Q|}{2}-1.
$$

A *residual packing* is a collection of such sets in which each pair of $V$ occurs at most once. Write $I(B)$ for its maximum total score, allowing the empty collection. In a fractional residual packing, the variables $y_Q\ge0$ satisfy

$$
\sum_{Q\supseteq e}y_Q\le1 \qquad \left(e\in\binom{V}{2}\right).
$$

Write $F(B)$ for the maximum of $\sum_Q y_Qw(Q)$. The maximum exists: every $Q$ contains a pair, so $y_Q\le1$, and the feasible set is a closed subset of a finite-dimensional unit cube. The empty packing is feasible in both problems.

A *proper host assignment* on $J_0\subseteq J$ chooses, for each $uv\in J_0$, a host $h$ with $u,v\in N_h$. The pairs assigned to any one host must form a matching. Thus the assigned triangles are edge-disjoint. Their core edges are distinct, and two triangles using the same host have disjoint sets of core endpoints. We use host assignments in the sense of [3, §5].

**Theorem 1 (stability of host transfer).** Suppose that each $N_h$ is independent in $B$. If $J_0\subseteq J$ admits a proper host assignment and $L=|J\setminus J_0|$, then

$$
\big|\Delta(G)-(F(B)-I(B))\big|\le 2L. \tag{1}
$$

When $J_0=J$, this is the exact transfer of [1, Lemma 2.1]. For general $J_0$, we shall keep every original host and its neighborhood. Each unassigned pair will receive a new host adjacent just to its two ends. To return from that graph to $G$, we need to compare the two partition numbers under an induced restriction.

## 2. The proof of stability

We first give the count for a complete assignment. It identifies the common term in the two partition numbers and explains why the same residual problem can be used after the extra hosts are introduced.

**Exact transfer ([1, Lemma 2.1]).** Under the hypotheses of Theorem 1, if $J_0=J$, then

$$
\begin{aligned}
\operatorname{cp}(G)   &= |E(G)|-2|J|-I(B),\\
\operatorname{cp}^*(G) &= |E(G)|-2|J|-F(B).
\end{aligned} \tag{2}
$$

*Proof.* Use the partition into individual edges as a reference. A clique $K$ saves $\binom{|K|}{2}-1$ pieces. The same count holds for fractional partitions. Indeed, if $x_K$ denotes the weight of $K$, summing the unit loads over the edges gives

$$
|E(G)|=\sum_{e\in E(G)}\sum_{K\supseteq e}x_K
       =\sum_K x_K\binom{|K|}{2}.
$$

Subtracting the cost $\sum_Kx_K$ gives the total saving. An integral partition is the case in which the chosen cliques have weight one.

Put $j(Q)=|J\cap\binom{Q}{2}|$. Since $e_B(Q)+j(Q)=\binom{|Q|}{2}$, the saving on a clique contained in the core is

$$
\binom{|Q|}{2}-1=w(Q)+2j(Q). \tag{3}
$$

Every other clique consists of one host and $u\ge1$ of its neighbors. These $u$ vertices span only pairs of $J$, because the host neighborhood is independent in $B$. Its saving can be charged to those pairs at two units per pair. In fact,

$$
2\binom u2-\left(\binom{u+1}{2}-1\right)
=\frac{(u-1)(u-2)}2\ge0
$$

for every integer $u\ge1$. Now take any clique partition. Its core cliques form a residual packing, so their total score is at most $I(B)$. The additional charges from (3) and from the cliques containing hosts sum to at most $2|J|$, since each pair of $J$ is covered once. With fractional weights, the core cliques satisfy the same pair capacities, and the total weight at each pair of $J$ is still one. The saving is therefore at most $I(B)+2|J|$ in the integral case and $F(B)+2|J|$ in the fractional case.

For the reverse bounds, start with an optimal residual packing. Write $y_Q$ for its coefficients, using zero and one in the integral case, and set $\ell_e=\sum_{Q\supseteq e}y_Q$ for each core pair $e$. Keep the core cliques at weights $y_Q$. For each $e=uv\in J$ with assigned host $h$, give $huv$ weight $1-\ell_e$. This fills $e$ to weight one. The matching condition ensures that the crossing edges $hu$ and $hv$ occur in no other assigned triangle, so their loads also remain at most one. Give each edge of $G$ its remaining weight as an individual edge. This is an exact fractional partition. If the starting coefficients are integral, every remaining weight is zero or one, and the same construction is an integral partition.

By (3), the core cliques save $\sum_Q y_Qw(Q)+2\sum_{e\in J}\ell_e$. The assigned triangles save $2\sum_{e\in J}(1-\ell_e)$, and the individual edges contribute zero saving. Addition gives the residual score plus $2|J|$ in each case. Subtracting these savings from $|E(G)|$ proves (2).

**Lemma 2 (induced restriction).** Let $K$ be an induced subgraph of a finite simple graph $X$. Suppose that the graph with edge set $E(X)\setminus E(K)$ admits a clique partition with $p$ pieces. Then

$$
|\Delta(X)-\Delta(K)|\le p. \tag{4}
$$

*Proof.* Intersect each clique of a partition of $X$ with $V(K)$ and discard intersections of size less than two. Every remaining set is a clique of $K$. Each edge of $K$ still belongs to the restriction of its unique original piece. Hence $\operatorname{cp}(K)\le\operatorname{cp}(X)$.

For a fractional partition, add the weights of all cliques with the same surviving intersection. For any edge $ab$ of $K$, the cliques contributing at $ab$ are precisely the original cliques containing $a$ and $b$. Their total weight remains one. Discarding the smaller intersections can only decrease the cost. Thus $\operatorname{cp}^*(K)\le\operatorname{cp}^*(X)$ as well.

Conversely, adjoin the $p$ given cliques to an optimal partition of $K$. Their edges are disjoint from $E(K)$ and cover all the remaining edges of $X$. This increases the integral cost by $p$, and assigning weight one to the same $p$ cliques gives the corresponding fractional extension. The increments $\operatorname{cp}(X)-\operatorname{cp}(K)$ and $\operatorname{cp}^*(X)-\operatorname{cp}^*(K)$ both lie in $[0,p]$. Their difference lies in $[-p,p]$, which proves (4).

*Proof of Theorem 1.* For each $e=uv\in J\setminus J_0$, add a distinct vertex $h_e$ with neighborhood $\{u,v\}$. Call the resulting graph $G^+$. Since $uv\notin E(B)$, the new neighborhood is independent in $B$. Assign $e$ to $h_e$ and retain the old assignment on $J_0$. The pairs at an old host still form the same matching, and a new host receives only one pair. Formula (2) therefore gives $\Delta(G^+)=F(B)-I(B)$.

The original vertices induce $G$ in $G^+$. The edges outside $G$ are exactly $h_eu,h_ev$ for the $L$ new hosts. Taking these $2L$ edges individually in Lemma 2 gives (1).

## 3. Deleting crossing edges from a witness

**Corollary 3.** Let $G$ have a complete assignment as in (2). If $G'$ is obtained from $G$ by deleting $q$ edges between $V$ and $H$, then

$$
|\Delta(G')-\Delta(G)|\le 2q. \tag{5}
$$

*Proof.* Retain the designated host of a pair whenever both crossing edges of its triangle survive. Each lost pair has at least one deleted edge in its designated triangle. Choose one such edge for each lost pair. These choices are distinct: an edge $hu$ could witness two losses only if two pairs at $u$ had been assigned to $h$. This would violate the matching condition. At most $q$ pairs are lost, even if both crossing edges of some triangles were deleted.

The remaining pairs keep a proper assignment in $G'$. Shrinking a host neighborhood preserves its independence in $B$, and the core and $B$ are unchanged. Apply Theorem 1 to $G'$ and substitute $F(B)-I(B)=\Delta(G)$ from (2).

For the witnesses of [1, Theorem 1.1], there are absolute constants $k>0$ and $n_0$ such that for each $n\ge n_0$ the original gap is at least

$$
f(n)=\frac{k n^2}{(\log n)^{5/2}}
      \exp\!\left(-2\sqrt{\log(24/7)\log n}\right),
$$

where logarithms are natural. After any $q_n$ crossing-edge deletions, (5) gives $\Delta(G'_n)\ge f(n)-2q_n$. If $q_n=o(f(n))$, division by $f(n)$ gives $\Delta(G'_n)\ge(1-o(1))f(n)$. The order is still $n$, including any hosts that have become isolated.

## 4. Reading the loss from the host lists

In Corollary 3 we knew the original assignment and counted its surviving pairs. Suppose instead that we are given just the neighborhoods $N_h$. Put $c=|V|$. For $e=uv\in J$ let

$$
L_e=\{h\in H:u,v\in N_h\},\qquad d(e)=\max\{0,c-|L_e|\}.
$$

For $1\le t\le c$, let $D_t(J)$ be the graph on $V$ with edge set $\{e\in J:d(e)\ge t\}$. Write $\nu(D)$ for the maximum number of edges in a matching of $D$, with value zero if $D$ has no edges.

**Corollary 4.** If each $N_h$ is independent in $B$, then

$$
\big|\Delta(G)-(F(B)-I(B))\big|
\le 2\sum_{t=1}^{c}\nu(D_t(J)). \tag{6}
$$

*Proof.* We use the list edge-coloring theorem of Häggkvist and Janssen [2, Theorem 1.1]: given a list of at least $c$ colors on each edge of $K_c$, one can choose a color from each list so that edges sharing an endpoint have distinct colors. For $c\le1$ there are no pairs to assign and (6) follows from Theorem 1 with $L=0$. Assume $c\ge2$.

Treat the hosts as colors. Introduce two further sets of colors, $\{\alpha_1,\ldots,\alpha_c\}$ and $\{\beta_1,\ldots,\beta_c\}$, disjoint from each other and from $H$. Give an edge $e\in J$ the list

$$
L_e\ \cup\ \{\alpha_t:1\le t\le d(e)\}.
$$

If $|L_e|\ge c$, its original list already suffices. If $|L_e|<c$, the added colors bring its list up to exactly $c$. Give every core pair outside $J$ the list $\{\beta_1,\ldots,\beta_c\}$. All edges of $K_c$ now meet the hypothesis of [2].

Fix one proper coloring from these lists. Retain the pairs of $J$ colored by hosts. A retained pair has both endpoints in its host's neighborhood, and each host color class is a matching. Every discarded pair of $J$ has exactly one color $\alpha_t$. The edges of that color form a matching in $D_t(J)$: they are disjoint by properness, and $\alpha_t$ was available on $e$ only when $d(e)\ge t$. There are consequently at most $\nu(D_t(J))$ discarded pairs of color $\alpha_t$. Summing over the colors counts each discarded pair once, even if its edge belongs to several of the nested graphs $D_t(J)$. Substitution in (1) gives (6).

**Corollary 5.** For every split presentation with core $V$, put $J=\binom{V}{2}$ and form the graphs $D_t(J)$ from the given neighborhoods. Then

$$
\Delta(G)\le 2\sum_{t=1}^{c}\nu(D_t(J)). \tag{7}
$$

In particular, suppose $|H|\ge2c$. Let $r$ be a nonnegative integer. Suppose at most $r$ core vertices miss more than $\lfloor c/2\rfloor$ hosts, and every core vertex misses at most $\lfloor c/2\rfloor+r$. Then $\Delta(G)\le4r^2$. If $r^2\le c$, this gives $\Delta(G)\le4c$.

*Proof.* Take $B$ to be the edgeless graph on $V$. Every host neighborhood is independent in $B$. Each residual set $Q$ has score $-\binom{|Q|}{2}-1<0$, so the empty packing attains both optima at zero. This gives (7) from (6).

For a core vertex $u$, let $M_u=\{h\in H:u\notin N_h\}$. If $u$ and $v$ each miss at most $\lfloor c/2\rfloor$ hosts, then

$$
|L_{uv}|=|H|-|M_u\cup M_v|
\ge 2c-2\lfloor c/2\rfloor\ge c.
$$

Thus every edge of every positive deficiency level has an endpoint among the at most $r$ exceptional vertices. The edges in a matching have disjoint endpoints, so $\nu(D_t(J))\le r$ at each level. For arbitrary $u,v$ the same calculation gives $|L_{uv}|\ge 2c-2\lfloor c/2\rfloor-2r\ge c-2r$. Hence $d(uv)\le2r$, and at most $2r$ levels are nonempty. The sum in (7) is at most $2r\cdot r$, proving the stated bounds.

For instance, take $2c$ hosts and let each core vertex miss exactly $\lfloor c/2\rfloor$ of them. The omitted sets may differ from vertex to vertex. There are $c\lfloor c/2\rfloor$ missing crossing edges, yet the first inequality in the proof gives at least $c$ common hosts for every pair. All deficiency levels are empty and $\Delta(G)=0$. More generally, (7) gives a necessary condition on **every** split presentation of a graph with gap $d$: its positive deficiency levels must have matching numbers with sum at least $d/2$.

## Formalization

The finite inequalities (1), (5), and (6) are statements about the original split graph in Lean. Their declarations in the namespace $\,\mathtt{QuadraticExteriorPalomar}\,$ are respectively `gap_stability_of_partial_assignment`, `gap_stability_after_cross_deletions`, and `gap_stability_of_marked_lists`. The last accepts any upper bounds for the matching numbers by level. Taking the maximum matching sizes gives (6). In the formal proof the fractional residual value is a supremum. The compactness observation in Section 1 identifies it with the maximum used here. The asymptotic conclusion in Section 3 follows from the finite inequality (5).

The Lean snapshot uses Lean 4.35.0-rc3 and Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e`. It imports the gap definition of [1], the host-assignment formalization of [3], and the list-coloring library used in [4]. The recorded build of `SplitGapII` and `SplitGapIIAudit` compiled 41 project modules. The axiom report for the 18 audited declarations lists only `propext`, `Classical.choice`, and `Quot.sound`.

## Acknowledgments

The author is deeply grateful to his wife María Paz and his children Lucas, Juan Cristóbal, Francisca, Raimundo and Benjamín for their love, patience and support.

## Use of artificial intelligence and computational tools

Claude, by Anthropic, and ChatGPT/Codex, by OpenAI, were used to explore and check arguments and to prepare the manuscript.

The author remains responsible for the arguments, citations, code and presentation. No AI system is listed as an author.

## References

[1] J. P. Traverso Gianini, *Nearly Quadratic Additive Gaps for Edge-Clique Partitions of Split Graphs*, preprint 1.0 (2026), Theorem 1.1 and Lemma 2.1. <https://github.com/jtraverso/split-clique-partition-gap/tree/ab463d8f4841101ba5c28047def8553b0c23249f>

[2] R. Häggkvist and J. Janssen, *New bounds on the list-chromatic index of the complete graph and other simple graphs*, Combinatorics, Probability and Computing **6** (1997), 295–313, Theorem 1.1. <https://doi.org/10.1017/S0963548397002927>

[3] J. P. Traverso Gianini, *Colorability and Realizability Defects in Resource-Dominated Packing Relaxations*, Paper V in the Erdős 81 series, §5. <https://github.com/jtraverso/erdos81-colorability-realizability-defects/tree/0c2f7dff52e5c578f39191c4905dd12248e7bb9a>

[4] J. P. Traverso Gianini, *Optimal Clique Partitions under Local Perturbations*, Paper VI in the Erdős 81 series, Lean formalization. <https://github.com/jtraverso/erdos81-optimal-clique-partitions/tree/719e39baf9d0e356a13f6bfe36b60b4ad5e910d6>
