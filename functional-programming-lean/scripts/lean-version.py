import json
from pathlib import Path
import re
import os
import sys

lean_version_re = re.compile(r'\{\{#lean_version\}\}')

def rewrite_lean_version(project_root):
    def rewrite(found):
        with open(f"{project_root}{os.path.sep}examples{os.path.sep}lean-toolchain", 'r') as f:
            return f.read().strip().split(':')[1]
    return rewrite


def rewrite_version(context, book):
    project_root = Path(context['root']).parent
    def rewrite_chapters(chapters):
        for ch in chapters:
            ch['Chapter']['content'] = lean_version_re.sub(rewrite_lean_version(project_root), ch['Chapter']['content'])
            rewrite_chapters(ch['Chapter']['sub_items'])

    rewrite_chapters(book['sections'])
    return book


def main():
    if len(sys.argv) > 1:
        if sys.argv[1] == "supports":
            sys.exit(0)
    context, book_contents = json.load(sys.stdin)
    print(json.dumps(rewrite_version(context, book_contents)))

if __name__ == '__main__':
    main()
