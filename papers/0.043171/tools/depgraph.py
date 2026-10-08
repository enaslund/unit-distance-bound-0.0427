#!/usr/bin/env python3
"""Dependency graph of the manuscript's numbered statements.

    python3 tools/depgraph.py            # write sections/proof-structure.tex and
                                         # sections/dependency-index.tex
    python3 tools/depgraph.py --check    # exit 1 if either file is out of date

A *statement* is a definition, lemma, proposition, theorem, corollary or remark with a
\\label. Its *dependencies* are the labelled statements cited (by \\ref or \\eqref of their
labels) inside it or inside its proof: the first proof environment before the next statement,
or a proof headed "Proof of ... \\ref{label}" anywhere in the paper. A citation of an equation
or item labelled inside a statement or its proof counts as a citation of that statement, and a
range "\\ref{X}--\\ref{Y}" cites every statement from X to Y. Two kinds of citation are
pointers, not dependencies: \\fref (defined in main.tex), and a citation of a later statement
inside a definition or a remark. Uses that the text does not cite by a label are not seen.

* sections/dependency-index.tex: an appendix listing, for every statement, the statements
  it uses and the statements that use it.
* sections/proof-structure.tex: the figure of the introduction. It shows the statements of
  FIGURE below, and draws an arrow A -> B when B uses A directly or through statements that
  are not shown (the reduction of the dependency graph to the shown statements). The
  positions and short captions are chosen by hand in FIGURE.
"""
import re
import sys
from pathlib import Path

PAPER = Path(__file__).resolve().parents[1]
KINDS = "definition|lemma|proposition|theorem|corollary|remark"
ENV = re.compile(r"\\begin\{(" + KINDS + r")\}(\[[^\]]*\])?(.*?)\\end\{\1\}", re.S)
REF = re.compile(r"\\(?:ref|eqref)\{([^}]*)\}")

# label: (short caption, column, row, part). Columns are XSTEP apart and rows YSTEP, rows
# growing downward; an arrow points from a statement to the statements that use it.
FIGURE = {
    # (I) the fields: the top row
    "tw:GB-presentation": (r"presentation of $G_B$", 0, 0, "I"),
    "tw:quadratic-layer": (r"$\dim\operatorname{gr}_2G_B=15$", 1, 0, "I"),
    "tw:retained-quotient": (r"the quotient $G_B/D_4G_B$", 2, 0, "I"),
    "tw:infinite": (r"$G_B$ is infinite", 3, 0, "I"),
    "tw:field-family": (r"the fields $K\supset F$", 4, 0, "I"),
    # (II) the relative zeta value: below, on the left
    "dh:detection": (r"detection by dihedral fields", 1, 1, "II"),
    "gf:factorization": (r"factorization of $\zeta_E$", 2, 1, "II"),
    "an:limit": (r"the limit lemma", 3, 1, "II"),
    "dh:census": (r"the census to $4\cdot10^{13}$", 0, 2, "II"),
    "dh:EW": (r"the field $E_{W''}$", 1, 2, "II"),
    "lv:values": (r"the $576$ $L$-values", 2, 2, "II"),
    "an:signed": (r"signed kernel inequality", 3, 2, "II"),
    "dh:floors-valid": (r"the floors are valid", 0, 3, "II"),
    "ce:values": (r"the kernel values", 2, 3, "II"),
    "ce:kernel": (r"the kernel conditions", 3, 3, "II"),
    "an:ceiling": (r"$d^{-1}\log L_F(1)<C_{\rm eff}$", 2, 4, "II"),
    # (III) the planar sets: on the right
    "geo:mass": (r"mass formula", 4, 1, "III"),
    "geo:selection": (r"class selection", 5, 1, "III"),
    "geo:transfer": (r"transfer, product profiles", 4, 2, "III"),
    "fw:shell-lemma": (r"shell profiles", 5, 2, "III"),
    "fw:transfer": (r"transfer, shell profiles", 4, 3, "III"),
    "pf:mass": (r"masses of the profiles", 3, 4, "III"),
    # (IV) the certificate: bottom right
    "cert:exact": (r"exact checks", 5, 3, "IV"),
    "cert:places": (r"the selected places of $F$", 4, 4, "IV"),
    "cert:enclosures": (r"interval enclosures", 4, 5, "IV"),
    "cert:lower-margin": (r"the margin is positive", 5, 5, "IV"),
    "thm:main": (r"$u(n)\ge n^{1.043171}$ infinitely often", 3, 6, "IV"),
}
# Statements whose outgoing arrows are not drawn (they would cross the figure); the caption says so.
FIGURE_OMIT = {"tw:field-family"}
# part: (fill colour, legend text)
PARTS = {
    "I": ("blue!10", "(I) the fields"),
    "II": ("orange!15", "(II) the relative zeta value"),
    "III": ("green!12", "(III) the planar sets"),
    "IV": ("gray!18", "(IV) the certificate"),
}
XSTEP, YSTEP, HALFW, HALFH = 2.76, 1.4, 1.3, 0.55
LEGEND = (0, 5)  # column and row of the legend's first entry


def sections():
    main = (PAPER / "main.tex").read_text()
    return re.findall(r"\\input\{(sections/[A-Za-z-]+)\}", main)


RANGE = re.compile(r"\\ref\{([^}]*)\}\s*(?:--|–)\s*~?\\ref\{([^}]*)\}")
LABEL = re.compile(r"\\label\{([^}]*)\}")


def extract():
    nodes, order, texts = {}, [], {}
    owner = {}  # label of an equation or item inside a statement or its proof -> the statement
    for f in sections():
        if f in ("sections/proof-structure", "sections/dependency-index"):
            continue
        text = (PAPER / (f + ".tex")).read_text()
        for m in ENV.finditer(text):
            kind, body = m.group(1), m.group(3)
            lab = LABEL.search(body)
            if not lab:
                continue
            rest = text[m.end():]
            nxt = ENV.search(rest)
            seg = rest[: nxt.start()] if nxt else rest
            # the proof of the statement: the first proof before the next statement (tables
            # or prose may come in between); a heading such as "Proof (computer-assisted)" is
            # allowed, while a heading that cites a statement, "Proof of ... \\ref{X}",
            # belongs to X and is handled below
            pm = re.search(r"\\begin\{proof\}(?:\[([^\]]*)\])?(.*?)\\end\{proof\}", seg, re.S)
            if pm and pm.group(1) and REF.search(pm.group(1)):
                pm = None
            proof = pm.group(2) if pm else ""
            name = lab.group(1)
            nodes[name] = {"kind": kind, "file": f}
            texts[name] = body + proof
            order.append(name)
            for inner in LABEL.findall(body + proof):
                if inner != name:
                    owner.setdefault(inner, name)
    for f in sections():
        text = (PAPER / (f + ".tex")).read_text()
        for m in re.finditer(r"\\begin\{proof\}\[([^\]]*)\](.*?)\\end\{proof\}", text, re.S):
            for target in REF.findall(m.group(1)):
                if target in nodes:
                    texts[target] += m.group(2)
                    for inner in LABEL.findall(m.group(2)):
                        owner.setdefault(inner, target)
    pos = {lab: i for i, lab in enumerate(order)}
    for name, text in texts.items():
        refs = set(REF.findall(text))
        # "Lemmas X--Y" cites every statement from X to Y
        for x, y in RANGE.findall(text):
            if x in pos and y in pos and pos[x] < pos[y]:
                refs |= set(order[pos[x]:pos[y] + 1])
        # a citation of an equation or item inside a statement cites the statement
        nodes[name]["refs"] = {owner.get(r, r) for r in refs}
    # A definition or remark that cites a later statement points ahead to where it is used;
    # it does not depend on it. Pointers elsewhere are written \\fref, which REF ignores.
    for lab, n in nodes.items():
        n["deps"] = sorted(r for r in n["refs"] if r in nodes and r != lab
                           and not (n["kind"] in ("definition", "remark") and pos[r] > pos[lab]))
    users = {lab: [] for lab in nodes}
    for lab in order:
        for d in nodes[lab]["deps"]:
            users[d].append(lab)
    return order, nodes, users


def reduced_edges(nodes, shown):
    """Edges a -> b between shown statements: b uses a, directly or through unshown ones."""
    edges = set()
    for b in shown:
        stack, seen = list(nodes[b]["deps"]), set()
        while stack:
            a = stack.pop()
            if a in seen:
                continue
            seen.add(a)
            if a in shown:
                edges.add((a, b))
            else:
                stack.extend(nodes[a]["deps"])
    # keep only edges not implied by a path through another shown statement
    def reach(u, v, skip):
        st, sn = [u], set()
        while st:
            x = st.pop()
            for (p, q) in edges:
                if p == x and (p, q) != skip and q not in sn:
                    if q == v:
                        return True
                    sn.add(q)
                    st.append(q)
        return False
    return sorted(e for e in edges if not reach(e[0], e[1], e))


def index_tex(order, nodes, users):
    lines = [
        "% Generated by tools/depgraph.py -- do not edit by hand.",
        "\\section{Dependency Index}\\label{dep:section}",
        "For each numbered statement, this index lists the numbered statements that it or its",
        "proof cites (``uses'') and the statements whose proofs cite it (``used by''). A",
        "citation of an equation inside a statement counts as a citation of the statement;",
        "references that only point ahead, or say where a statement is used, are not counted.",
        "The index is generated from the sources by \\texttt{tools/depgraph.py}, so it records",
        "the citations made in the text: a use that is not cited by number does not appear.",
        "Figure~\\ref{fig:structure} shows the main part of this graph.",
        "",
        "{\\small",
        "\\begin{longtable}{@{}p{0.19\\textwidth}p{0.37\\textwidth}p{0.37\\textwidth}@{}}",
        "\\toprule statement & uses & used by\\\\ \\midrule \\endhead",
    ]
    names = {"definition": "Def.", "lemma": "Lem.", "proposition": "Prop.", "theorem": "Thm.",
             "corollary": "Cor.", "remark": "Rem."}

    def cite(lab):
        return f"{names[nodes[lab]['kind']]}~\\ref{{{lab}}}"
    for lab in order:
        u = ", ".join(cite(x) for x in nodes[lab]["deps"]) or "--"
        v = ", ".join(cite(x) for x in users[lab]) or "--"
        lines.append(f"{cite(lab)} & {u} & {v}\\\\")
    lines += ["\\bottomrule", "\\end{longtable}}", ""]
    return "\n".join(lines)


def _hits(points, boxes):
    return any(abs(x - bx) < HALFW + 0.1 and abs(y - by) < HALFH - 0.03
               for (x, y) in points for (bx, by) in boxes)


def _cubic(a, c1, c2, b, n=48):
    pts = []
    for i in range(1, n):
        t = i / n
        u = 1 - t
        pts.append(tuple(u**3 * a[k] + 3 * u * u * t * c1[k] + 3 * u * t * t * c2[k] + t**3 * b[k]
                         for k in (0, 1)))
    return pts


def _route(a, b, boxes, free):
    """A path for an arrow from a to b that avoids the boxes: ("bend", degrees) for a TikZ bend,
    or ("via", c) for a curve with control point c through a free grid point."""
    import math
    (x0, y0), (x1, y1) = a, b
    dx, dy = x1 - x0, y1 - y0
    length = math.hypot(dx, dy)
    ang = math.atan2(dy, dx)
    for bend in (0, 15, -15, 25, -25, 35, -35):
        th = math.radians(bend)
        c = 0.3915 * length
        c1 = (x0 + c * math.cos(ang + th), y0 + c * math.sin(ang + th))
        c2 = (x1 - c * math.cos(ang - th), y1 - c * math.sin(ang - th))
        if not _hits(_cubic(a, c1, c2, b), boxes):
            return ("bend", bend)
    # a curve through a free point w: with both control points c = (8w - a - b)/6 the cubic
    # passes through w at t = 1/2
    best = None
    for w in free:
        c = ((8 * w[0] - x0 - x1) / 6, (8 * w[1] - y0 - y1) / 6)
        if _hits(_cubic(a, c, c, b), boxes):
            continue
        cost = math.hypot(w[0] - x0, w[1] - y0) + math.hypot(x1 - w[0], y1 - w[1])
        if best is None or cost < best[0]:
            best = (cost, c)
    return ("via", best[1]) if best else ("bend", 0)


def figure_tex(nodes):
    shown = [lab for lab in FIGURE if lab in nodes]
    missing = [lab for lab in FIGURE if lab not in nodes]
    assert not missing, ("labels of FIGURE not found", missing)
    edges = [e for e in reduced_edges(nodes, set(shown)) if e[0] not in FIGURE_OMIT]
    pos = {lab: (FIGURE[lab][1] * XSTEP, -FIGURE[lab][2] * YSTEP) for lab in shown}
    name = {lab: lab.replace(":", "-") for lab in shown}
    out = [
        "% Generated by tools/depgraph.py -- do not edit by hand.",
        "\\begin{figure}[tp]",
        "\\centering",
        "\\begin{tikzpicture}[x=1cm,y=1cm,>=stealth,",
        " box/.style={draw=black!60,rounded corners=2pt,align=center,font=\\scriptsize,",
        "  execute at begin node={\\hyphenpenalty=10000\\exhyphenpenalty=10000},",
        f"  inner sep=1.5pt,minimum height={2 * HALFH:.2f}cm,text width={2 * HALFW - 0.15:.2f}cm}}]",
    ]
    for lab in shown:
        cap, _, _, part = FIGURE[lab]
        kind = nodes[lab]["kind"].capitalize()
        x, y = pos[lab]
        out.append(f"\\node[box,fill={PARTS[part][0]}] ({name[lab]}) at ({x:.3f},{y:.3f}) "
                   f"{{{kind}~\\ref*{{{lab}}}\\\\ {cap}}};")
    cols = 1 + max(FIGURE[l][1] for l in shown)
    rows = 1 + max(FIGURE[l][2] for l in shown)
    taken = {(FIGURE[l][1], FIGURE[l][2]) for l in shown}
    # free points: empty grid cells, and the gaps between neighbouring rows and columns
    free = [(i * XSTEP, -j * YSTEP) for i in range(cols) for j in range(rows) if (i, j) not in taken]
    free += [((i + 0.5) * XSTEP, -(j + 0.5) * YSTEP) for i in range(cols - 1) for j in range(rows - 1)]
    for a, b in edges:
        boxes = [pos[c] for c in shown if c not in (a, b)]
        kind, val = _route(pos[a], pos[b], boxes, free)
        style = "->,black!50" if FIGURE[a][3] == FIGURE[b][3] else "->,black!50,densely dashed"
        if kind == "via":
            path = f".. controls ({val[0]:.3f},{val[1]:.3f}) .."
        elif val == 0:
            path = "--"
        else:
            path = f"to[bend left={val}]" if val > 0 else f"to[bend right={-val}]"
        out.append(f"\\draw[{style}] ({name[a]}) {path} ({name[b]});")
    col, row = LEGEND
    for i, (colour, text) in enumerate(PARTS.values()):
        x, y = col * XSTEP - HALFW, -(row * YSTEP) - 0.38 * i
        out.append(f"\\node[draw=black!60,fill={colour},minimum size=0.22cm,inner sep=0pt] "
                   f"at ({x + 0.11:.3f},{y:.3f}) {{}};")
        out.append(f"\\node[anchor=west,font=\\scriptsize,inner sep=0pt] at ({x + 0.35:.3f},{y:.3f}) "
                   f"{{{text}}};")
    omitted = ", ".join(f"{nodes[l]['kind'].capitalize()}~\\ref{{{l}}}" for l in sorted(FIGURE_OMIT))
    out += ["\\end{tikzpicture}",
            "\\caption{The structure of the proof (Subsection~\\ref{intro:structure}). Each box is a "
            "numbered statement, coloured by the part of the proof it belongs to. An arrow goes "
            "from a statement to each statement whose proof uses it, directly or through "
            "statements not shown, except that arrows implied by a chain of drawn arrows are "
            "left out; dashed arrows join different parts. The arrows from "
            f"{omitted}, which supplies the fields to which Parts (II)--(IV) apply, are also "
            "left out. Appendix~\\ref{dep:section} lists the citations between all numbered "
            "statements; the notation is collected in Subsection~\\ref{intro:notation}.}",
            "\\label{fig:structure}",
            "\\end{figure}", ""]
    return "\n".join(out)


def main():
    order, nodes, users = extract()
    files = {PAPER / "sections/dependency-index.tex": index_tex(order, nodes, users)}
    if FIGURE:
        files[PAPER / "sections/proof-structure.tex"] = figure_tex(nodes)
    check = "--check" in sys.argv
    stale = []
    for path, text in files.items():
        if check:
            if not path.exists() or path.read_text() != text:
                stale.append(str(path))
        else:
            path.write_text(text)
    print(f"{len(order)} statements, {sum(len(n['deps']) for n in nodes.values())} citations")
    if stale:
        print("out of date:", *stale, file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
