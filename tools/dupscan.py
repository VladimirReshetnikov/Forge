#!/usr/bin/env python3
"""Find sentences repeated across the article's sections.

The article is assembled from proposals that often said the same thing in the
same words; deduplicating them is part of the merge. This scan is the check that
a new edit has not reintroduced a repeated sentence -- one that appears in two
places, possibly in two different files.

It previously lived only in a session scratch directory, which another process
deleted. It is committed now for that reason.

Method: strip comments, environments that are not prose (tables, equations,
code), and LaTeX commands (keeping their text arguments); split into sentences;
normalise case, whitespace and punctuation; report any normalised sentence of at
least MIN_WORDS words that occurs more than once. Short sentences are ignored
because they legitimately repeat ("It does not.").

Exit code 1 when duplicates are found, so it can gate a build.
"""
from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MIN_WORDS = 8
SKIP_ENVS = ("table", "tabular", "equation", "align", "verbatim", "lstlisting",
             "quote", "center", "figure", "enumerate", "itemize")


def prose(tex: str) -> str:
    tex = re.sub(r"(?<!\\)%.*", "", tex)                       # comments
    for env in SKIP_ENVS:
        tex = re.sub(r"\\begin\{%s\*?\}.*?\\end\{%s\*?\}" % (env, env), " ", tex, flags=re.S)
    tex = re.sub(r"\$[^$]*\$", " MATH ", tex)                  # inline math
    tex = re.sub(r"\\(?:label|ref|cite|eqref|url|href)\{[^}]*\}", " ", tex)
    for _ in range(3):                                          # unwrap \cmd{text}
        tex = re.sub(r"\\[A-Za-z]+\*?(?:\[[^\]]*\])?\{([^{}]*)\}", r"\1", tex)
    tex = re.sub(r"\\[A-Za-z]+\*?", " ", tex)
    tex = tex.replace("~", " ").replace("---", " ").replace("--", " ")
    return re.sub(r"[{}]", " ", tex)


def sentences(text: str):
    for raw in re.split(r"(?<=[.!?])\s+", text):
        norm = re.sub(r"[^a-z0-9 ]+", "", raw.lower())
        norm = re.sub(r"\s+", " ", norm).strip()
        if len(norm.split()) >= MIN_WORDS:
            yield norm


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dir", type=Path, default=ROOT / "article" / "sections")
    args = ap.parse_args()
    seen: dict[str, list[str]] = defaultdict(list)
    for f in sorted(args.dir.glob("*.tex")):
        for s in sentences(prose(f.read_text(encoding="utf-8"))):
            seen[s].append(f.name)
    dups = {s: fs for s, fs in seen.items() if len(fs) > 1}
    for s, fs in sorted(dups.items()):
        print(len(fs), sorted(set(fs)), "::", s[:120])
    print("--- %d repeated sentences" % len(dups))
    # A LaTeX command whose backslash was eaten by a shell or a string literal
    # becomes a control character: \texttt -> TAB + "exttt", \ref -> CR + "ef",
    # \frac -> FF + "rac". LaTeX compiles most of these silently.
    mangled = 0
    for f in sorted(args.dir.glob("*.tex")):
        text = f.read_bytes().decode("utf-8").replace("\r\n", "\n")
        for i, line in enumerate(text.split("\n"), 1):
            for m in re.finditer(r"[\t\r\f\b\a\v](?=[a-z])", line):
                mangled += 1
                print("%s:%d: control character %r before %r" % (f.name, i, m.group(), line[m.end():m.end() + 8]))
    print("--- %d control characters where a backslash was probably eaten" % mangled)
    return 1 if dups or mangled else 0


if __name__ == "__main__":
    raise SystemExit(main())
