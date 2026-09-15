#!/usr/bin/env python3
"""Assemble the modular article into one portable LaTeX source file."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[1]/'article'

def expand(path):
    path=path.resolve()
    if not path.is_relative_to(root.resolve()):
        raise ValueError('Input outside article directory')
    text=path.read_text()
    def sub(m):
        name=m.group(1)
        return '% BEGIN '+name+'\n'+expand(root/name)+'\n% END '+name+'\n'
    return re.sub(r'\\input\{([^}]+)\}',sub,text)

(root/'forge-standalone.tex').write_text(expand(root/'forge.tex'))
print('Assembled article/forge-standalone.tex')
