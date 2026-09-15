"""Regenerate article tables from the recorded experiment JSON."""
import json
from pathlib import Path
R=Path(__file__).resolve().parents[1]
r=json.loads((R/'results/experiments.json').read_text())
escape=lambda x:str(x).replace('_',r'\_')
lines=[r'\begin{tabular}{lrrrr}',r'\toprule',r'Component & Cases & Accepted checks & Mutations rejected \\',r'\midrule']
for name,title in [('sos','Nonnegative-polynomial certificates'),('lattice','Integer lattice certificates'),('induction','Accumulator induction identities'),('horn','Ground-Horn search cases')]:
    a=r[name];valid=a.get('verified_derivations',a['positive_checks'])
    lines.append(f"{title} & {a['positive_checks']} & {valid} & {a['corruption_rejections']} \\\\")
lines += [r'\midrule',f"Total & {r['summary']['component_test_cases']} & {r['summary']['valid_certificate_checks']} & {r['summary']['corruption_rejections']} \\\\",r'\bottomrule',r'\end{tabular}']
# Exactly four columns; keep generated source self-contained.
lines[0]=r'\begin{tabular}{lrrr}'
(R/'article/table-summary.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{lrrr}',r'\toprule',r'Polynomial problem & Candidates & Terms & Median ms \\',r'\midrule']
for a in r['sos']['curated']:
    lines.append(f"{escape(a['case'])} & {a['candidates']} & {a['certificate_terms']} & {a['median_ms']:.3f} \\\\")
lines += [r'\bottomrule',r'\end{tabular}']
(R/'article/table-sos.tex').write_text('\n'.join(lines)+'\n')
lines=[r'\begin{tabular}{rrrrr}',r'\toprule',r'Distractor chains & Indexed rules & Forward firings & Demand firings & Times (ms) \\',r'\midrule']
for i in range(0,len(r['horn']['scaling']),2):
    a,b=r['horn']['scaling'][i:i+2]
    lines.append(f"{a['distractor_chains']} & {a['indexed_rules']} & {a['firings']} & {b['firings']} & {a['elapsed_ms']:.3f} / {b['elapsed_ms']:.3f} \\\\")
lines += [r'\bottomrule',r'\end{tabular}']
(R/'article/table-horn.tex').write_text('\n'.join(lines)+'\n')
print('Wrote 3 data-derived TeX tables.')
