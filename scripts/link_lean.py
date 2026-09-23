#!/usr/bin/env python3
"""Link the Lean names in the proof docs to their declarations.

Every paragraph of docs/**/*.md that starts with `*Lean:` lists Lean names in
backticks. This script turns each name into a link to the file and line of
its declaration in SquaresInCircles.lean or SquaresInCircles/, and refreshes
links that are already there, so line numbers follow the code. Folder and
file names in those paragraphs are linked too.

    python3 scripts/link_lean.py           rewrite the docs in place
    python3 scripts/link_lean.py --check   exit 1 if any link is stale

A name that matches no declaration, or more than one, is an error.
"""
import argparse
import os
import re
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WIDTH = 80

DECL = re.compile(
    r'(?:@\[[^\]]*\]\s*)?'
    r'(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*'
    r'(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)'
    r'\s+([^\s:({\[]+)')
# A linked name, [`name`](target), or a bare one, `name`.
TOKEN = re.compile(r'\[`([^`]+)`\]\([^)]*\)|`([^`$]+)`')


def declarations():
    sources = [ROOT / 'SquaresInCircles.lean']
    sources += sorted((ROOT / 'SquaresInCircles').rglob('*.lean'))
    found = {}
    for path in sources:
        for number, line in enumerate(path.read_text().splitlines(), 1):
            m = DECL.match(line)
            if m:
                found.setdefault(m.group(1), []).append((path, number))
    return found


def target(name, doc_dir, decls, errors, doc):
    """The link target for `name`, relative to `doc_dir`, or None."""
    rel = lambda p: os.path.relpath(p, doc_dir)
    candidates = [ROOT / name, ROOT / 'SquaresInCircles' / name]
    if name.endswith('/') or name.endswith('.lean'):
        for path in candidates:
            if path.exists():
                return rel(path)
    hits = decls.get(name, [])
    if len(hits) == 1:
        path, number = hits[0]
        return f'{rel(path)}#L{number}'
    reason = 'no declaration' if not hits else f'{len(hits)} declarations'
    errors.append(f'{doc.relative_to(ROOT)}: `{name}`: {reason}')
    return None


def wrap(paragraph):
    # Keep inline math on one line: protect its spaces while wrapping.
    flat = re.sub(r'\$[^$]+\$', lambda m: m.group(0).replace(' ', '\0'),
                  ' '.join(paragraph.split()))
    text = textwrap.fill(flat, width=WIDTH, break_long_words=False,
                         break_on_hyphens=False)
    return text.replace('\0', ' ')


def relink(doc, decls, errors):
    doc_dir = doc.parent
    paragraphs = doc.read_text().split('\n\n')
    for i, paragraph in enumerate(paragraphs):
        if not paragraph.startswith('*Lean:'):
            continue

        def link(m):
            name = m.group(1) or m.group(2)
            dest = target(name, doc_dir, decls, errors, doc)
            return m.group(0) if dest is None else f'[`{name}`]({dest})'

        paragraphs[i] = wrap(TOKEN.sub(link, paragraph))
    return '\n\n'.join(paragraphs)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--check', action='store_true',
                        help='report stale links instead of rewriting them')
    args = parser.parse_args()

    decls = declarations()
    errors, stale = [], []
    for doc in sorted((ROOT / 'docs').rglob('*.md')):
        old = doc.read_text()
        new = relink(doc, decls, errors)
        if new != old:
            stale.append(doc.relative_to(ROOT))
            if not args.check:
                doc.write_text(new)

    for error in errors:
        print(f'error: {error}', file=sys.stderr)
    verb = 'stale' if args.check else 'updated'
    for doc in stale:
        print(f'{verb}: {doc}')
    if errors or (args.check and stale):
        if args.check and stale:
            print('Run python3 scripts/link_lean.py to refresh the links.',
                  file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
