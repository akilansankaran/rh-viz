import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from md2html import convert

D = sys.argv[1]
files = sys.argv[2:]

PARTS = [
    ('t-statements', 'Statements and the analytic reduction', 'theory_intro.md'),
    ('t-logic', 'The logical skeleton and its quantifier structure', 'theory_logic.md'),
    ('t-meta', 'Metatheory', 'theory_meta.md'),
    ('t-bridge', 'The nonvanishing bridge', 'theory_bridge.md'),
    ('t-arith', 'The arithmetic side: the Selmer bound and the Galois representations', 'theory_arith.md'),
]

CSS = '''#theory{max-width:1100px}
#theory p,#theory li,#theory td{font-family:"Times New Roman",Times,serif;font-size:16px;line-height:1.6}
#theory h3.th{font-family:"Times New Roman",Times,serif;font-size:18px;margin:22px 0 6px}
#theory h4.th{font-family:"Times New Roman",Times,serif;font-size:16.5px;margin:16px 0 4px;font-style:italic}
#theory .part{font-family:"Times New Roman",Times,serif;font-size:21px;margin:34px 0 4px;padding-top:10px;border-top:1px solid var(--rule)}
#theory .eq{overflow-x:auto;margin:8px 0}
#theory code{font-size:12.5px;background:var(--surface-2);padding:0 3px;border-radius:3px}
#theory table.tt{border-collapse:collapse;margin:10px 0;width:100%}
#theory table.tt th,#theory table.tt td{border-bottom:1px solid var(--rule);padding:5px 8px;vertical-align:top;font-size:15px}
#theory table.tt th{font-family:"Times New Roman",Times,serif;color:var(--text-secondary)}
#theory .toc2 a{color:var(--text-secondary);text-decoration:none;border-bottom:1px dotted var(--text-muted)}
'''


def body(fname):
    md = open(os.path.join(D, fname), encoding='utf-8').read()
    md = re.sub(r'^##\s+[^\n]*\n', '', md, count=1)
    return convert(md)


intro = ('<p>This section gives a technical account of the development as mathematics and as logic. The first part states the theorems and the classical reduction to nonvanishing; the second writes the top of the proof as an explicit derivation and analyses the quantifier structure of its key statements; the third places the proof in its metatheory, its axioms, its consistency strength and the logical form of its conclusion; and the last two trace the two deep halves of the argument from the source. Every claim cites the Lean declaration it was read from, and sentences marked (interpretation) record a reading of the code that the code does not itself state.</p>')
toc = '<p class="toc2">' + ' · '.join(f'<a href="#{a}">{t}</a>' for a, t, _ in PARTS) + '</p>'
sec = ['<!--theory-start-->', '<h2 class="tnr" id="s-theory">Mathematical architecture</h2>', '<div id="theory">', intro, toc]
for a, t, f in PARTS:
    sec.append(f'<div class="part" id="{a}">{t}</div>')
    sec.append(body(f))
sec += ['</div>', '<!--theory-end-->']
block = '\n'.join(sec) + '\n'
ANCHOR = '<h2 class="tnr" id="s-docs">Documents</h2>'
for p in files:
    s = open(p, encoding='utf-8').read()
    if '<!--theory-start-->' in s:
        a = s.index('<!--theory-start-->')
        b = s.index('<!--theory-end-->') + len('<!--theory-end-->\n')
        s = s[:a] + s[b:]
    assert s.count(ANCHOR) == 1, p
    s = s.replace(ANCHOR, block + ANCHOR)
    if '#theory{' not in s:
        s = s.replace('</style>', CSS + '</style>', 1)
    s = s.replace("['gnote','excltext','exclmatrix'].forEach", "['gnote','excltext','exclmatrix','theory'].forEach")
    if 'href="#s-theory"' not in s:
        s = s.replace('<a href="#s-docs">Documents</a>', '<a href="#s-theory">Mathematical architecture</a><a href="#s-docs">Documents</a>')
    open(p, 'w', encoding='utf-8').write(s)
    print(p.split('/')[-1], 'ok', len(block))
