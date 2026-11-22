import html
import json
import sys

S = json.load(open(sys.argv[1]))
T = json.load(open(sys.argv[2]))
files = sys.argv[3:]
TOTAL = T[0]['size']

rows = []
for t in T:
    short = t['name'].split('.')[-1]
    w = max(2, 520 * t['size'] / TOTAL)
    rows.append(
        f'<div class="dt" title="{html.escape(t["name"])}">'
        f'<span class="dtn" style="padding-left:{t["depth"] * 14}px">{html.escape(short)}</span>'
        f'<span class="dtb" style="width:{w:.0f}px"></span><span class="dts">{t["size"]:,}</span></div>')

SECTION = r'''<!--logic-start-->
<h2 class="tnr" id="s-logic">Logical structure of the dependency graph</h2>
<div id="logic" class="tnr">
<p>For a declaration $v$ write $\varphi_v$ for its statement, $T(v)$ for the theorems of the development and $D(v)$ for the definitions of the development that its statement or proof refers to. When the kernel accepts $v$, it has checked
$$\vdash\; \Big(\bigwedge_{u \in T(v)} \varphi_u\Big) \;\to\; \varphi_v ,$$
with the definitions in $D(v)$ entering as definitional equations and not as premises. Read in this way, the 101,067 theorems reached from riemannHypothesis form a propositional Horn theory with one clause for each theorem, and the main theorem holds because forward chaining from the clauses with empty bodies reaches it; checking the declarations in dependency order is exactly that forward chaining. Each lemma is a cut in the proof-theoretic sense, proved once and invoked by reference wherever it is used.</p>
<table class="lt">
<tr><th>Quantity</th><th>Definition</th><th>Value</th></tr>
<tr><td>Clause length</td><td>$|T(v)|$, the theorems a theorem cites</td><td>median 1, mean 1.82; with median 2 and mean 3.04 definitions besides</td></tr>
<tr><td>Base clauses</td><td>theorems with $T(v) = \varnothing$</td><td>36,582 (36%), of which 12,631 cite nothing in the development at all</td></tr>
<tr><td>Depth</td><td>length of the shortest chain from riemannHypothesis to $v$</td><td>at most 56; the longest chain has about 139 steps</td></tr>
<tr><td>Multiplicity</td><td>$\pi(v)$, the number of chains from riemannHypothesis to $v$</td><td>median $10^{2.4}$, 90th percentile $10^{5.5}$, maximum $10^{17.9}$</td></tr>
<tr><td>Cut-free size</td><td>$\sum_v \pi(v)$, the theorem occurrences if every lemma were inlined at each use</td><td>$10^{18.7}$, against $10^{5.0}$ distinct theorems</td></tr>
<tr><td>Dominance</td><td>$d$ dominates $v$ when every chain from riemannHypothesis to $v$ passes through $d$</td><td>see the tree below</td></tr>
</table>
<p>The clauses are short and the base is broad: a typical theorem combines one earlier theorem with a few definitions, and more than a third of all theorems rest on Mathlib and the development's definitions alone. Depth comes from chaining, and sharing is what keeps the chains finite in practice. Inlining every lemma at each of its uses would produce about $10^{18.7}$ theorem occurrences, so the lemma structure compresses the argument by a factor near $10^{13.7}$; the most heavily shared statements are elementary facts about monomials in Rees algebras from the functorial resolution of singularities, each used along about $10^{17.9}$ distinct chains.</p>
<p>Dominance locates the logical bottlenecks. If $d$ dominates $v$, then every route by which $\varphi_v$ contributes to the main theorem passes through $\varphi_d$, so the set dominated by $d$ is exactly the part of the formalization that would become irrelevant to riemannHypothesis if $\varphi_d$ were adopted as an axiom. The dominator tree has a narrow top. EveryCharacter dominates everything; beneath it the proof of the Galois representations dominates 78,804 declarations, and beneath that the geometric seed and its weight-one realization dominate 57,456 and 54,819. Below the Kodaira–Spencer step the tree becomes a single chain of about fifteen statements, through integral models of Harris–Taylor type, potentially good reduction, semistable reduction, semi-abelian models and Zarhin's projective models, each dominating about 6,000 declarations. Every link of that chain is a point through which a large block of the argument reaches the conclusion, and each is therefore a natural unit for independent checking.</p>
<div class="dtree">__ROWS__</div>
<p class="dcap">Dominator tree of the dependency graph, showing every declaration that dominates at least 4,000 others; bar length is proportional to the number of declarations dominated. Hover for the full name. All values are computed on the name-resolved graph described above and are approximate.</p>
</div>
<!--logic-end-->
'''
CSS = '''#logic{max-width:1100px}
#logic p,#logic td{font-family:"Times New Roman",Times,serif;font-size:16px;line-height:1.6}
#logic table.lt{border-collapse:collapse;width:100%;margin:12px 0}
#logic table.lt th,#logic table.lt td{border-bottom:1px solid var(--rule);padding:6px 9px;vertical-align:top;text-align:left}
#logic table.lt th{font-family:"Times New Roman",Times,serif;font-size:15px;color:var(--text-secondary)}
.dtree{margin:14px 0 4px;font-family:"Times New Roman",Times,serif;font-size:14.5px}
.dt{display:flex;align-items:center;gap:10px;height:22px}
.dtn{display:inline-block;box-sizing:border-box;min-width:560px;max-width:560px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;color:var(--text-primary)}
.dtb{display:inline-block;height:9px;border-radius:3px;background:#2a78d6;opacity:.75}
.dts{color:var(--text-muted);font-size:13px;font-variant-numeric:tabular-nums}
.dcap{color:var(--text-muted);font-size:14px !important;font-style:italic}
'''
block = SECTION.replace('__ROWS__', ''.join(rows))
ANCHOR = '<h2 class="tnr" id="s-docs">Documents</h2>'
for p in files:
    s = open(p, encoding='utf-8').read()
    for a0, b0 in (('<!--theory-start-->', '<!--theory-end-->'), ('<!--logic-start-->', '<!--logic-end-->')):
        if a0 in s:
            a = s.index(a0)
            b = s.index(b0) + len(b0) + 1
            s = s[:a] + s[b:]
    assert s.count(ANCHOR) == 1, p
    s = s.replace(ANCHOR, block + ANCHOR)
    if '#logic{' not in s:
        s = s.replace('</style>', CSS + '</style>', 1)
    s = s.replace("['gnote','excltext','exclmatrix','theory'].forEach", "['gnote','excltext','exclmatrix','logic'].forEach")
    s = s.replace("['gnote','excltext','exclmatrix'].forEach", "['gnote','excltext','exclmatrix','logic'].forEach")
    s = s.replace('<a href="#s-theory">Mathematical architecture</a>', '<a href="#s-logic">Logical structure</a>')
    if 'href="#s-logic"' not in s:
        s = s.replace('<a href="#s-docs">Documents</a>', '<a href="#s-logic">Logical structure</a><a href="#s-docs">Documents</a>')
    open(p, 'w', encoding='utf-8').write(s)
    print(p.split('/')[-1], 'ok', 'theory' in s and '<!--theory-start-->' in s)
