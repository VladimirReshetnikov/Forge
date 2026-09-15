#!/usr/bin/env python3
from pathlib import Path
import json
root=Path(__file__).resolve().parents[1]
d=json.loads((root/'results/benchmarks.json').read_text())
s='''\\begin{center}
\\begin{tabular}{@{}rrrrr@{}}
\\toprule
Depth & Forward facts & Demand atoms & Forward ms & Demand ms\\\\
\\midrule
'''
for r in d['horn']:
 s+=f"{r['depth']} & {r['forward_facts']:,} & {r['demand_facts']} & {1000*r['forward_seconds']:.3f} & {1000*r['demand_seconds']:.3f} \\\\\n"
s+='\\bottomrule\n\\end{tabular}\n\\end{center}\n'
(root/'article/horn-table.tex').write_text(s)
