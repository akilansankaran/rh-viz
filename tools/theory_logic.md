### The logical skeleton as a derivation

Lean's logic is dependent type theory, in which a theorem is a closed term whose type is the proposition it proves and an implication $A \to B$ is proved by a function from proofs of $A$ to proofs of $B$. Above the deep layers, however, the development uses only a fragment that reads naturally as first-order natural deduction: implication elimination, conjunction and structure introduction, universal instantiation, and definitional unfolding. The top of the proof can therefore be written out as an explicit derivation whose every line is a Lean declaration.

Write $G$ for `UpperTheory.Gal.Int.Geo.GeoOne`, $T$ for `UpperTheory.TP.TLiftK`, $R(\rho)$ for `UpperTheory.GalStar.Row0b` $\rho$ with $\rho$ a local Langlands notion, $L$ for `UpperTheory.Zero.LLC.RecTExists`, $B$ for `PositivityTheory.Rg.BcN.BaseChangeIsobaricN`, $V$ for `UpperTheory.Top.VWin`, $O$ for `UpperTheory.LiteratureTheorems.OpenImageCondition`, $\Omega$ for `UpperTheory.LiteratureTheorems.OpenLiteratureStatements`, $C$ for `UpperTheory.EveryCharacter`, $Z$ for the proposition $\forall s\,(\operatorname{Re} s > \tfrac12 \wedge s \neq 1 \to \zeta(s) \neq 0)$, and $H$ for `RiemannHypothesis`. The premises are theorems proved deeper in the development:

| | Premise | Proved by |
| --- | --- | --- |
| $\mathrm{A}_1$ | $\vdash G$ | `UpperTheory.Gal.Int.Geo.geoOne_holds` |
| $\mathrm{A}_2$ | $\vdash T$ | `UpperTheory.TP.K.tLiftK`, itself `UpperTheory.TP.tLift_holds_k` |
| $\mathrm{A}_3$ | $\vdash G \to T \to R(\mathrm{recT})$ | `UpperTheory.Gal.Int.galoisLocalGlobalStrong_of_geometry_lift` |
| $\mathrm{A}_4$ | $\vdash L$ | `UpperTheory.Zero.LLC.recTExists` |
| $\mathrm{A}_5$ | $\vdash B$ | `UpperTheory.BaseChangeIdentities.baseChangeN` |
| $\mathrm{A}_6$ | $\vdash O \to B \to R(\mathrm{IsRecT}) \to V$ | `UpperTheory.One.Join.automorphic_window_of_inputs` |
| $\mathrm{A}_7$ | $\vdash \Omega \to V \to C$ | `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin` |
| $\mathrm{A}_8$ | $\vdash Z \to H$ | `Formalism.VW.rh_of_right` |

Two of the steps below are not inferences. The structures $O$ and $\Omega$ are conjunctions with named fields, so they are introduced by their constructors, and $\mathrm{recT}$ is defined as $\lambda h\, rc.\ \mathrm{IsRecT}\,h\,rc$, so $R(\mathrm{recT})$ and $R(\mathrm{IsRecT})$ are the same proposition after one $\delta$-unfolding and one $\eta$-contraction. The derivation is then:

| Line | Formula | Justification | Lean |
| --- | --- | --- | --- |
| 1 | $R(\mathrm{recT})$ | $\to$E on $\mathrm{A}_3$, $\mathrm{A}_1$, $\mathrm{A}_2$ | `galoisLocalGlobalStrong_recParameter` |
| 2 | $R(\mathrm{IsRecT})$ | conversion from 1 ($\delta\eta$) | definitional |
| 3 | $O$ | constructor on 2 | `OpenImageCondition.mk` |
| 4 | $V$ | $\to$E on $\mathrm{A}_6$, 3, $\mathrm{A}_5$, 2 | `UpperTheory.One.vwin_of_row` |
| 5 | $\Omega$ | constructor on 2, $\mathrm{A}_4$, 2 | `OpenLiteratureStatements.mk` |
| 6 | $C$ | $\to$E on $\mathrm{A}_7$, 5, 4 | `UpperTheory.FinalTheorems.everyCharacter` |
| 7 | $Z$ | $\forall$E at $N := 1$, $\chi := 1$, then rewriting by $L(s,1) = \zeta(s)$ | `Formalism.VW.rh_of_every` |
| 8 | $H$ | $\to$E on $\mathrm{A}_8$, 7 | `rhOfAll`, `riemannHypothesis` |

Read as a single proof term, lines 1 to 8 are
$$\mathrm{rh\_of\_right}\;\Big(\lambda\, s\, h_s\, h_1.\ \mathrm{modOne}\triangleright\, \mathrm{everyCharacter\_of\_row}\big(\mathrm{galoisRepresentations\_of\_thetaLift}\ \mathrm{tLiftK}\big)\ 1\ 1\ s\ h_s\ (\mathrm{inr}\ h_1)\Big),$$
in which $\mathrm{everyCharacter\_of\_row}\,h$ unfolds to $\mathrm{every\_character\_of\_literature\_of\_vWin}\ \langle h, \mathrm{recTExists}, h\rangle\ (\mathrm{vwin\_of\_row}\ h)$. Two features of this form matter for assessment. First, the derivation has no open assumptions: every premise is a closed theorem, so the top-level statement depends on nothing beyond the axioms of Lean itself, which `#print axioms riemannHypothesis` would list after a build. Second, the single proof of $R(\mathrm{recT})$ is used three times, once to prove $V$ and twice inside $\Omega$; in the terminology of the pillar analysis above, the Galois representations are the one premise on which both remaining pillars depend.

### Quantifier structure

The statements differ sharply in logical complexity. The Riemann Hypothesis and EveryCharacter are universal statements with a quantifier-free matrix over $\mathbb{C}$:
$$H \equiv \forall s \in \mathbb{C}\; \big(\zeta(s) = 0 \wedge \neg\exists n\,(s = -2(n+1)) \wedge s \neq 1 \to \operatorname{Re} s = \tfrac12\big),$$
$$C \equiv \forall N \geq 1\; \forall \chi \bmod N\; \forall s \in \mathbb{C}\; \big(\operatorname{Re} s > \tfrac12 \wedge (\chi \neq 1 \vee s \neq 1) \to L(s,\chi) \neq 0\big).$$
The Selmer bound $V$ has a much deeper prefix. Writing $\mathrm{WP}$ for `WinPair`, $\mathrm{CF}$ for `IsChiField` and $\mathrm{VV}$ for `VVle`, its definition (`UpperTheory.Top.VWin`, `UpperTheory.Top.VWinAt`) is, after moving quantifiers outward,
$$\begin{aligned}
V \;\equiv\; \forall \psi\; \forall \varepsilon\; \forall e\; \Big[\, &\Phi(\varepsilon, e) \;\to\; \exists J\; \exists X_0\; \forall X\; \forall q\; \forall d\; \Big( X \geq X_0 \wedge \mathrm{WP}(\varepsilon, X^{1/J}, q, d) \;\to \\
&\exists Y\; \big( X^{1/J} \leq Y \wedge Y^2 \leq X \;\wedge\; \forall x\; \forall E\; ( Y \leq x \leq Y^2 \wedge \mathrm{CF}(\psi, e(x), q, d, E) \\
&\qquad\qquad \to\; \mathrm{VV}(E, \lfloor x^{401} \rfloor, \sqrt{\exp(x^{\varepsilon})}) ) \big) \Big) \Big],
\end{aligned}$$
where $\Phi(\varepsilon, e)$ is $0 < \varepsilon < \tfrac{1}{52} \wedge \forall x \geq 1\; x^{2+8\varepsilon} \leq 2^{e(x)} \leq 2x^{2+8\varepsilon}$. The prefix alternates five times, $\forall\exists\forall\exists\forall$, and it is not first order in the strict sense: $e$ ranges over functions $\mathbb{R} \to \mathbb{N}$, $E$ ranges over number fields, which in Lean are types, and $\mathrm{VV}$ itself quantifies over all choices of local Galois-cohomological data $\mathrm{LData}$ and over all finite sets of primes. The first-order reading is accurate for the derivation above, which manipulates these statements only as wholes, and it becomes an approximation as soon as one looks inside them.

The asymmetry is the shape of the argument. The deep arithmetic of the development produces a statement of high quantifier complexity, uniform in the character, the scale and the auxiliary primes, and the nonvanishing bridge converts it into a statement of the simplest universal form. Assessing the development therefore comes down to two questions of different kinds: whether the arithmetic genuinely establishes $V$ with the stated uniformity, and whether the bridge from $V$ to $C$ uses that uniformity correctly.
