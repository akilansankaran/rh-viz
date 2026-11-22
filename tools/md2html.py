import html
import re


def inline(t):
    parts = re.split(r'(\$\$.*?\$\$|\$[^$\n]+?\$)', t)
    out = []
    for p in parts:
        if p.startswith('$'):
            out.append(html.escape(p, quote=False))
            continue
        p = html.escape(p, quote=False)
        p = re.sub(r'`([^`]+)`', r'<code>\1</code>', p)
        p = re.sub(r'\*\*([^*]+)\*\*', r'<b>\1</b>', p)
        p = re.sub(r'(?<![\w*])\*([^*\n]+)\*(?![\w*])', r'<i>\1</i>', p)
        out.append(p)
    return ''.join(out)


def convert(md):
    lines = md.split('\n')
    out, i = [], 0
    while i < len(lines):
        l = lines[i]
        if not l.strip():
            i += 1
            continue
        m = re.match(r'^(#{2,4})\s+(.*)', l)
        if m:
            lvl = {2: 'h3', 3: 'h3', 4: 'h4'}[len(m.group(1))]
            out.append(f'<{lvl} class="tnr th">{inline(m.group(2))}</{lvl}>')
            i += 1
            continue
        if l.strip().startswith('$$') and not (l.strip().endswith('$$') and len(l.strip()) > 4):
            blk = [l]
            i += 1
            while i < len(lines) and not lines[i].strip().endswith('$$'):
                blk.append(lines[i])
                i += 1
            if i < len(lines):
                blk.append(lines[i])
                i += 1
            out.append('<div class="eq">' + html.escape('\n'.join(blk), quote=False) + '</div>')
            continue
        if l.lstrip().startswith('|'):
            rows = []
            while i < len(lines) and lines[i].lstrip().startswith('|'):
                rows.append(lines[i].strip().strip('|'))
                i += 1
            rows = [r for r in rows if not re.match(r'^[\s:|-]+$', r)]
            if rows:
                h = ''.join(f'<th>{inline(c.strip())}</th>' for c in rows[0].split('|'))
                b = ''.join('<tr>' + ''.join(f'<td>{inline(c.strip())}</td>' for c in r.split('|')) + '</tr>' for r in rows[1:])
                out.append(f'<table class="tt"><tr>{h}</tr>{b}</table>')
            continue
        if re.match(r'^\s*([-*]|\d+\.)\s+', l):
            tag = 'ol' if re.match(r'^\s*\d+\.', l) else 'ul'
            items = []
            while i < len(lines) and lines[i].strip() and (re.match(r'^\s*([-*]|\d+\.)\s+', lines[i]) or lines[i].startswith('  ')):
                if re.match(r'^\s*([-*]|\d+\.)\s+', lines[i]):
                    items.append(re.sub(r'^\s*([-*]|\d+\.)\s+', '', lines[i]))
                else:
                    items[-1] += ' ' + lines[i].strip()
                i += 1
            out.append(f'<{tag}>' + ''.join(f'<li>{inline(x)}</li>' for x in items) + f'</{tag}>')
            continue
        para = [l]
        i += 1
        while i < len(lines) and lines[i].strip() and not re.match(r'^(#{2,4}\s|\||\s*([-*]|\d+\.)\s)', lines[i]):
            para.append(lines[i])
            i += 1
        txt = '\n'.join(para)
        pieces = re.split(r'(\$\$[\s\S]*?\$\$)', txt)
        buf = ''
        for pc in pieces:
            if pc.startswith('$$'):
                if buf.strip():
                    out.append(f'<p>{inline(buf.strip())}</p>')
                buf = ''
                out.append('<div class="eq">' + html.escape(pc, quote=False) + '</div>')
            else:
                buf += pc
        if buf.strip():
            out.append(f'<p>{inline(buf.strip())}</p>')
    return '\n'.join(out)
