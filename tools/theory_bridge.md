## The nonvanishing bridge: from a Tate–Shafarevich length bound to zero-free half-planes

This note describes how the development proves `UpperTheory.EveryCharacter` from the length hypothesis `UpperTheory.Top.VWin` and the other inputs. Every claim cites the Lean declaration it was read from. Sentences marked (interpretation) give our reading of the code and are not statements found in it.

### 1. The target statement and the top-level assembly

The target is
$$\texttt{EveryCharacter} :\iff \forall N\ge 1,\ \forall \chi \bmod N,\ \forall s,\ \ \operatorname{Re}s>\tfrac12,\ (\chi\neq 1 \lor s\neq 1)\ \Longrightarrow\ L(s,\chi)\neq 0,$$
which is `UpperTheory.EveryCharacter` (in `CharacterBoxes/EveryCharacter.lean`). For $\chi=1$, $N=1$ this is the Riemann hypothesis, and in general it is GRH for Dirichlet $L$-functions.

The most outer wrapper is `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin (O : OpenLiteratureStatements) (hV : VWin)`. It calls `UpperTheory.Lit.every_character_of_theta_integrals_local_matching P F hA hM hX hL hV`. The arguments are the following:

- `P : GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses`, a `Prop`-structure with about 65 fields, each naming a published theorem (Clozel, Green, Jacquet–Shalika, Siegel–Weil, Casselman–Wallach, local Tate duality, and others).
- `F : ThetaLocalInputs`, `hA : ThetaIntegralsAgree`, `hM : LocalMatching`.
- `hX : GlobalTheory.CovTop.CovolumeBoundOfX`, which the wrapper supplies from `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt`.
- `hL : UpperTheory.Zero.LLC.RecTExists`.

The theorem then applies `UpperTheory.Top.every_character_of_green_v_win` to three inputs: Green's theorem, obtained as `GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters`; the hypothesis `hV`; and a witness of `Nonempty (GlobalTheory.Fc.HypsAlt …)`, built by `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound`.

### 2. Logical skeleton

Write $\mathrm{PChar}$ for primitive characters. The chain below is read from the proof terms.

**(S1) Reduction to primitive characters.** `UpperTheory.Top.imprimitive : ZeroFreeAll → EveryCharacter`. Here `Formalism.HC.ZeroFreeAll := ZeroFreeOn (fun _ => True)` and `ZeroFreeOn Q := ∀ ψ, Q ψ → ψ.ZeroFreeAbove (1/2)` (file `ExplicitFormulaErrorOfHostConditions.lean`). The proof writes $L(s,\chi)=L(s,\chi^{*})\prod_{p\mid N}(1-\chi^{*}(p)p^{-s})$ and notes that each Euler factor is nonzero when $\operatorname{Re}s>0$. It is complete and elementary.

**(S2) Assembly.** `UpperTheory.Top.zero_free_all_of_green_v_win` is `zeroFreeAll_of_topG (la := 3/2)` applied to two inputs. The first is `TopG`, obtained from the shape theorem `shape_closed_link_n_of_green hG` together with the hypothesis structure. The second is, for each $\psi$, `HostExW (3/2) (GChi ψ).req`, obtained as `supplyChi ψ (hV ψ)`. The predicate `UpperTheory.Top.TopG` (file `ZeroFreeAllOfTopG.lean`) says: for every $\lambda>1$ and every family requirement $G$, if suitable hosts exist on windows (`HostExW λ G.req`) and every family in `G.cls λ` satisfies `HypV`, then `FamilyClassConnected (G.cls λ)`. In other words, for all small $\varepsilon$ some family in the class carries the tie data `ChainTied` at every large window point $x$.

**(S3) Level-wise reduction.** `UpperTheory.Top.zeroFreeAll_of_topG` invokes `Formalism.HC.zeroFreeOn_of_tiedWin_cyc` with the level $\Lambda=$ `Level.cyc ψ`, the cyclic group $\langle\psi\rangle$ pushed to primitive characters. It needs three inputs:
1. `ChebyshevInequalityOnWindows`, supplied by `UpperTheory.Comparison₂.level_gm_le_on_family_scales`;
2. `Λ.FormB`, supplied by `UpperTheory.Comparison₂.formB`;
3. `ChebyshevInequalityAtWindowScale (3/2) Λ`, supplied from `TopG` through `hypV_of_cls` and `eFamC_of_cls`.

**(S4) Windowed Landau step.** `Formalism.HC.level_of_tiedWin` takes $\operatorname{Re}s>1/2$ and picks $\varepsilon$ with $(e_D+e_L+7)\varepsilon\le\frac12\min(\operatorname{Re}s-\frac12,\frac12)$ (`exists_small_eps`). It then shows that $\Lambda.\mathrm{Gm}(y)\le y^{\theta}$ with $\theta<\operatorname{Re}s$ holds on windows $[Y,Y^{3/2}]$ for arbitrarily large $Y$, and concludes through `FormBAt`.

### 3. The analytic mechanism

**The test function.** For a level $\Lambda$ (`Formalism.HC.Level.Gm`),
$$\mathrm{Gm}_\Lambda(y)=G_\zeta(y)+\sum_{\psi'\in\Lambda\setminus\{1\}} w(\psi')\,\operatorname{Re} g_{\psi'}(y),\qquad w(\psi')=\begin{cases}1&\psi'=\psi_K\\ (3o+1)^{-1}&\text{otherwise},\end{cases}$$
with $o=\Lambda.o$ (for `Level.cyc` this is the order of $\langle\psi\rangle$, see `Level.ofSub`). By `Formalism.Gz`,
$$G_\zeta(y)=\sum_{n\le y}\Lambda(n)\Big(\frac yn-1\Big)-y\log y+(1+\gamma)y,$$
and by `Formalism.HC.An.gChi`, for $\chi\neq 1$,
$$g_\chi(y)=\sum_{n\le y}\Lambda(n)\chi(n)\Big(\frac yn-1\Big)+y\,\frac{L'}{L}(1,\chi).$$
These are Cesàro-weighted (Riesz-mean) Chebyshev functions with their main terms removed. Their Mellin transforms are $-\frac{1}{s(s-1)}\frac{L'}{L}(s)$ up to polar terms (`Landau.mellin_Gchi'`).

**Landau's principle.** `Formalism.HC.Landau.zero_free_of_Chebyshev_growth` proves `Level.ChebyshevGrowthImpliesZeroFree`: if $\mathrm{Gm}_\Lambda(y)\le y^\theta$ for all large $y$, then $\zeta$ and every $L(s,\psi')$ with $\psi'\in\Lambda$ are zero-free on $\operatorname{Re}s>\theta$. The proof passes through `landau_family`, which applies `landau_entire` to $P=\zeta_1^{R}\prod_{\xi}L(s,\xi)$. The Dirichlet coefficients of $-P'/P$ are $\Lambda(n)\big(R+\sum_\xi \xi(n)\big)$, and these are nonnegative because $\Lambda$ is closed under inversion and the weights are chosen to match (`hki`, `hkw`). This is the classical Landau theorem on Dirichlet integrals with nonnegative coefficients.

**Windowed form.** The bridge needs the bound only on windows. `Formalism.HC.Level.FormBAt λ` states: if $\{x:\mathrm{Gm}_\Lambda(x)\le x^\theta\}$ contains intervals $[Y,Y^{\lambda}]$ for arbitrarily large $Y$ (`HasWindows`), then $\Lambda$ is zero-free above $\theta$. `UpperTheory.Comparison₂.formB` proves this for every $\lambda>1$ through `Deduction.zeroFree_of_rpow_window` and `Deduction.lemmaL`. Underneath sits `Deduction.landau_window`. With $u=\log y$, that argument bounds high-order Taylor coefficients $\Phi^{(k)}(\sigma)/k!$ of the Laplace transform of $g(u)=\mathrm{Gm}(e^u)$. The weight $u^k e^{-\sigma u}$ concentrates on $[U,(1+\delta)U]$ (`landau_window_key`, `landau_tails`), and the resulting coefficient growth is set against the pole of $\Phi$ at the rightmost zero (`landau_window_contra`, `landau_dichotomy`, `landau_nearest`). (interpretation) This is a Pólya–Landau "Taylor coefficient" argument. It replaces the global one-sided bound of Landau's theorem by a bound on a sparse set of long logarithmic windows.

**What is contradicted.** Suppose $L(\rho,\psi)=0$ with $\operatorname{Re}\rho>1/2$. The contradiction is with the inequality
$$\mathrm{Gm}_{\langle\psi\rangle}(x)\le x^{1/2+(e_D+e_L+7)\varepsilon}\quad\text{for all large } x \text{ in the window set of a family}, \tag{$\ast$}$$
which is `ChebyshevInequalityOnWindows` (`TopWin.lean`). Through `FormB`, inequality $(\ast)$ forces zero-freeness above $1/2+(e_D+e_L+7)\varepsilon<\operatorname{Re}\rho$.

### 4. Host fields, the family, and the parameters

**Character fields.** `UpperTheory.Top.IsChiField ψ e q d E` says that $E$ embeds in $\mathbb{Q}(\zeta_N)$ with $2^{e+2}$, $N_\psi$, $q$, $d$ dividing $N$, and that $\tau_a\in\operatorname{Gal}(\mathbb{Q}(\zeta_N)/\mathbb{Q})$ fixes $E$ exactly when
$$a\equiv\pm1 \pmod{2^{e+2}},\qquad \psi(a)=1,\qquad \Big(\frac aq\Big)=\Big(\frac ad\Big)=1 .$$
`UpperTheory.Top.isChiField` derives this from `KerChi ψ H` (file `TwistForm.lean`), which states the same condition for the Artin map of a host $H$ of conductor `QS·q·d`.

**Parameters.** `UpperTheory.Top.PageN ε x e` is the condition $x^{2+8\varepsilon}\le 2^e\le 2x^{2+8\varepsilon}$, and `exists_pageN` produces such an $e(x)$. In `UpperTheory.T3.supplyOfAdmOf` the frame order satisfies $x^{2+8\varepsilon}\le \mathrm{ord}\,\varphi\le 2x^{2+8\varepsilon}$. (interpretation) Since $2^{e+2}>x^2+1$, no prime power $n\le x$ satisfies $n\equiv\pm1\bmod 2^{e+2}$, so no prime $p\le x$ splits completely in $E$. The identity behind $(\ast)$ therefore involves only primes with nontrivial Frobenius, and this explains the exponent $2+8\varepsilon$.

`UpperTheory.Top.WinPair ε Y q d` requires all of the following:
- $q$ prime, $q\equiv 3\pmod 8$, and $\tfrac12Y^{\varepsilon/5}<\log q\le Y^{\varepsilon/5}$;
- $d$ prime, $d\equiv 7\pmod{16}$, and $\tfrac12Y^{\varepsilon/5}\log^2Y<\log d\le Y^{\varepsilon/5}\log^2Y$;
- $q\mid d+1$, and every odd prime $p\le Y^{\varepsilon/5}$ divides $d+1$.

So $\big(\frac{-d}{p}\big)=1$ for all small odd $p$, which `supplyOfAdmOf` extracts as `hjacb` via `pairHyp`.

`UpperTheory.Top.VWinAt ψ Ct` quantifies over $0<\varepsilon<1/52$ and over page functions $e$. It asks for $J\ge1$ and $X_0$ such that for $X\ge X_0$ and every WinPair $(q,d)$ at scale $X^{1/J}$, there is $Y\in[X^{1/J},X^{1/2}]$ such that `VAt ψ ε Ct q d (e x) x` holds for every $x\in[Y,Y^2]$. Then `VWin := ∀ ψ, VWinAt ψ 401`. The constant $401$ is consumed in `UpperTheory.Top.winPairs`: rescaling $x=kx'$ with $k^{400}\le x'$ turns $\lfloor x'^{401}\rfloor$ into a bound $\lfloor x^{400}\rfloor$, which is the field `WinDatum.bound`. The bound $\varepsilon<1/52$ is the admissible range in `HostExW` and `admissibleClassesTwistedChar`. The window exponent $3/2$ is `la` in `zero_free_all_of_green_v_win`, and `winPairs` produces windows $[Z,Z^{3/2}]$ inside $[W,W^2]$.

### 5. Where the upper bound $(\ast)$ comes from

`UpperTheory.Comparison₂.core_gm` proves $(\ast)$ for every host $H$ satisfying two conditions: `EAtH Λ H TT x ε C` and `CoreAtH H TT …`. The proof has three parts.

1. **Character decomposition.** `gmA_eq` rewrites $\mathrm{Gm}_\Lambda(x)$ as `Deduction.CH.GmA`, a weighted sum of $\operatorname{Re}G_\psi(x)$ over a set $K_p$ of additive characters of $E_0\times A$. Here $E_0=(\mathbb Z/2)^2$, $A$ is the frame group, and $G_\psi$ is `GPsi`, built from `primVal`, the Frobenius/inertia data of `arithOf H`.

2. **The main inequality.** `Deduction.ch_core` gives
$$\mathrm{GmA}(x)\le x^{1/2+(C+3)\varepsilon}+\mathrm{SigA}(x),\qquad \mathrm{SigA}(x)=\sum_{\psi\in\Psi_{A_0}\setminus K_p}\|G_\psi(x)\|.$$
It assumes that for every $u\in A_0$ the gap $\mathrm{gapA}(u)=\sum_{t,j}\big(\mathrm{ASK}-\operatorname{Re}\mathrm{MAIN}\big)$ is at most $x^{C\varepsilon}\cdot$`errorBracketSizeWindows`. In `FirstPrimeNeSecondPrime.lean`, `ASK` is a weighted count of inert primes (Frobenius outside `PhiSet`) with ramp weights $\max(a/p^i-w,0)$, plus a term at $d$. `MAIN` is $a\big(\log a-1-\gamma+\ell(\chi_C)-\overline{\log w}\big)$. The orthogonality identities `AskExpansion` and `AskMainBalance` express $\mathrm{ASK}-\mathrm{MAIN}$ as a character sum `De`.

3. **The two pieces.** `sigA_le` bounds SigA by $4o\,x^{1/2+\varepsilon}$ using `EAtH.bdG`. `Deduction.ch_top` bounds the gap using `each_unit_bound_statement`. That lemma is pure real-number algebra applied to a record `Formalism.RankGapBounds.Data`, whose fields are ranks, slopes $\mu$, maximal slopes, heights $h$ and dual slopes. Its hypotheses `SizeData₂` (`HidaSetting`, `DIV`, `Slopes`, `SlopeIneq`, `LossBounds`, …) are inequalities among those fields.

**The square-root input.** `EAtH.bdG` is `HostRaw.BoundedCharsPointwise`, which reads $\|g_\chi(x)\|\le x^{1/2+\varepsilon}$ for every primitive $\chi$ attached to a "bounded" character of the host. `UpperTheory.Top.boundedTw_key` shows that these $\chi$ are exactly the twists $\xi\cdot(\cdot/q)^i(\cdot/d)^j$ with $\xi\in\langle\psi\rangle$ and $(i,j)\neq(0,0)$. `UpperTheory.Top.boundedTw` then supplies the bound from `PairGood.bounds`. The pairs come from `QH.pairEx : PairEx`, which is a theorem. Built on `QH.pair_exists` and about 4300 lines in `MeanSquareBounds/`, it produces, for every large $Y$, a WinPair $(q,d)$ with three properties:
- $\|g_\chi(y)\|\le y^{1/2+\varepsilon/2}$ and $|L'/L(1,\chi)|\le 4\log y$ for all twists and all $y\in[Y,Y^A]$;
- the zero-free boxes `ZeroBox`, meaning no zeros with $\operatorname{Re}s>1-1/400$ and $|\operatorname{Im}s|\le 8M e^{Y^{\varepsilon/5}}(\ldots)$;
- the predicates `GoodQ` and `GoodD` (`BoxAll`).

(interpretation) This is a "most quadratic twists are good" mean-square statement. The kept characters $\langle\psi\rangle$ are never assumed to satisfy square-root bounds. Their contribution is controlled only through the gap inequality, which is where the arithmetic data enter.

### 6. How the Tate–Shafarevich lengths enter

**The groups.** In `Formalism.GaloisCohomology`, an `LData E Ω l` consists of three pieces of data:
- the set $S$ of places of $E$ above $l$;
- decomposition data at those places;
- a character of $G_{E,S}$ to $\mathbb{Z}_l^\times$ that restricts to the cyclotomic character (`hchi`).

The groups are
$$\text{Ш}(D,e)=\ker\Big(H^1\big(G_{E,S},\mathbb{Q}_l/\mathbb{Z}_l(-e)\big)\to\textstyle\prod_{v\in S}H^1(G_v,\cdot)\Big),\qquad \texttt{shaLen}(D,e)=\operatorname{length}_{\mathbb{Z}_l}\text{Ш}(D,e)\in\mathbb{N}_\infty,$$
(`Sha`, `qzTw` uses $\chi^{-e}$). `VFormula` and `PTShaAt` record the Poitou–Tate relation with $H^2(G_{E,S},\mathbb{Z}_l(e+1))$.

**The bound.** `UpperTheory.Top.VVle E t B` says that every such Ш with $1\le e<t$ is finite, and that for every finite set of primes $S$,
$$\sum_{l\in S}\log l\sum_{e=1}^{t-1}\texttt{shaLen}_l(e)\ \le\ B .$$
`VAt` applies this with $t=\lfloor x^{Ct}\rfloor$ and $B=\sqrt{\exp(x^\varepsilon)}$ to every `IsChiField` $E$. (interpretation) The left side is $\sum_e\log\#\text{Ш}^1(E,\mathbb{Q}/\mathbb{Z}(-e))$ over all $l$, a quantity of the kind that Lichtenbaum-type formulas relate to $\zeta_E$ at negative integers. The code does not invoke such a formula.

**The route.** No class number formula, Chebotarev density or height formula for Ш appears on this route. The bound reaches the analytic inequality as follows.
1. `supplyOfAdmOf` places `VVle H.E R.t (√b)` into `GChi ψ`, with $b=$`Scale.b`$=\exp(x^\varepsilon)$.
2. `UpperTheory.Top.hypV_of_cls` extracts `HypV`.
3. `UpperTheory.Top.vvRecord` converts `HypV` into `ShaFinOdd`, summability of `vvTerm`, and $\sum_l$`vvTerm`$\,\le b$.
4. In `UpperTheory.Top.divinN_of_hypV` and `divinN_at`, the bound is fed into `LinkN_at`:
$$\texttt{etaSum}(L,j)\le D_{Z0}(j)\Big(C\big(f m\, b\, L^2+\log^2 x\cdot N_c\big)+\sum_l\texttt{vvTerm}(l)\Big),$$
which yields `DIVinN`, a bound $\texttt{etaSum}\le D_0\,C\,x^\varepsilon(B_0+N_c)$ on a ramification-weighted sum `etaSum`.
5. `UpperTheory.Top.topDesWin` combines `DIVinN` with the other link conditions into `LinkDIV` and `LinkMu`, and `LinkGLOBAL` then produces `ChainTied`.

`LinkN` itself, which is the relation between `etaSum` and the Ш lengths, is not proved inside the bridge itself; it is supplied as a hypothesis at this level and discharged further down. It is the parameter `N` of `HypsAlt`, and its supply goes through `UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink`, with `P.nLink : GlobalTheory.NLink.Hypotheses₂` (Fontaine $B_{\mathrm{cris}}$, Bloch–Kato local, local Tate duality, Bhatt–Scholze).

### 7. Arithmetic geometry and Green's theorem

**Covolume bound.** `GlobalTheory.CovTop.CovolumeBoundOfX` asserts an eventual lattice bound `(p.S false).L3 (p.N C CH)` at all points of every family in `FamHyp`. It is used in `linked_bundles_l3_of_open_alt` inside the construction of `HypsAlt`. `SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt` derives it from the following hypotheses:
- `ResolutionCharZero`, `PrincipalisationCharZero` and `PoincareLelongInv`;
- `HSUse` (arithmetic Hilbert–Samuel) and `MoriwakiBigStatement`;
- `FarguesExact`, `ZarhinStatement` and `NefRR`;
- toroidal and Siegel compactification statements, `ArDegree`, `PublishedHodgeBundleTheorems` and `GrothendieckDeformation`.

The derivation passes through `topCovolG_alt_alt`, which chains Gram, size, height-lower-bound (`height_lower_bound_general_alt`), cover-degree and flatness steps into `covolX_of_truncation_badSet_lambda_lowBound`. In the outer wrapper, `HSUse` and `MoriwakiBigStatement` are supplied by theorems `PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright` and `moriwakiBig_outright`. These are built from a resolution theorem `resK`, a Poincaré–Lelong theorem and `DenseCurves.main`. (interpretation) The geometry supplies Arakelov-degree and slope control for the Hermitian lattices whose ranks, slopes and heights fill the `Data` record of §5. The slope inequalities there are what bound the inert-prime count `ASK` by `MAIN` plus error.

**Green's theorem.** `GlobalTheory.GLq.Green` states that the cuspidal characters of $GL_d(\mathbb{F}_g)$ are parametrised injectively by degree-$d$ prime labels, with degree $\prod_{i=1}^{d-1}(g^i-1)$. `green_of_regular` derives it from `GreenRegularCharacters`, the form with regular characters of $\mathbb{F}_{g^d}^\times$ and the character formula on elliptic elements. That form is also proved as `GlobalTheory.greenRegularCharacters_holds`. Green enters `shapeWin` and `shape_closed_link_n_of_green` only through `GlobalTheory.Top.Irr.link_irr hGreen …`, which yields `LinkIRR`: $\delta_p\ge0$ and $\delta_p\le\exp(-x^{e_z/7})$ for an irreducibility defect of the local data.

### 8. Points a referee would check first

1. **`VWin` is the central premise of the bridge, and it is of exceptional strength.** Within the bridge it is a hypothesis; it is discharged elsewhere, by `UpperTheory.One.vwin_of_row` from the Galois representations (see the arithmetic section). It bounds Ш lengths for twists $e$ up to $x^{400}$ over fields of degree at least about $x^{2+8\varepsilon}$, by $\exp(x^\varepsilon/2)$. Its plausibility, and whether it already encodes zero-free information, is the first question.
2. **The link between Ш and the analytic data enters as a hypothesis bundle.** The inequality relating `etaSum` to the Ш lengths is `LinkN`, a parameter of `HypsAlt`. Its supply rests on `P.nLink`. The Ш bound only feeds a summability and size condition (`vvRecord`, `divinN_at`).
3. **`HypsAlt` is a large `Type`-valued hypothesis structure.** It has about 45 fields, including `hn4` (a class number formula), `hU`, `hG`, `tie` and `rRows`. `nonempty_hyps_definite_side_of_closed_bound` builds it from `P`, `F`, `hA`, `hM`, `hX` and `hL`. Each field should be matched with the published result it is said to encode.
4. **Placeholder field.** `UnitaryGroupThirdPlaceHypotheses.siegelEisensteinSimplePole` has type `GlobalTheory.Published.UnusedSlot72`, defined as `True`. The field carries no content despite its name.
5. **The windowed Landau theorem.** `Deduction.zeroFree_of_rpow_window` (18-line file) and `UpperTheory.Comparison₂.formB` claim zero-freeness from a one-sided bound on windows $[Y,Y^{1+\delta}]$ for every $\delta>0$. The substance lies in `lemmaL`, `landau_window` and `poleData`, and these deserve independent verification.
6. **`each_unit_bound_statement` is pure algebra.** It turns the `SizeData₂` inequalities into the gap bound, so the whole weight of $(\ast)$ for the kept characters rests on `ChainTied`. `ChainTied` comes from `GlobalTheory.Top.link_gl` (a 33-line file) and the `Closed` conditions in `HypsAlt`.
7. **`EAtH` presupposes square-root bounds.** `BoundedCharsPointwise` gives $|g_\chi(x)|\le x^{1/2+\varepsilon}$ for the twisted characters, so the mean-square theorem `QH.pairEx` must be checked carefully. Its zero boxes reach height about $e^{Y^{\varepsilon/5}\log^2Y}$ and its square-root bounds hold uniformly on $[Y,Y^A]$.
8. **Name versus content.** The final `ZeroFreeOn` statement quantifies over all $\psi$, including the trivial character, through `Level.cyc`. This should be confirmed against `PChar.one` handling in `zero_free_of_Chebyshev_growth`, which reads $L(\cdot,1_{\bmod 1})=\zeta$ via `LFunction_modOne_eq`.
