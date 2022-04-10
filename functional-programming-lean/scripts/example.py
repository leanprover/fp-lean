import json
import re
import textwrap
from pathlib import Path
import os
import sys

example_in_re = re.compile(r'\{\{#example_in\s+(?P<file>[^\s]+)\s+(?P<name>[^\s]+)\s*}}')
example_out_re = re.compile(r'\{\{#example_out\s+(?P<file>[^\s]+)\s+(?P<name>[^\s]+)\s*}}')

example_start_re = re.compile(r'bookExample\s+(type\s+)?\{\{\{\s*(?P<name>[a-zA-Z0-9_]+)\s*\}\}\}')
example_middle_re = re.compile(r'===>')
example_end_re = re.compile(r'end\s+bookExample')

expect_start_re = re.compile(r'expect\s+(info|error)\s+\{\{\{\s*(?P<name>[a-zA-Z0-9_]+)\s*\}\}\}')
expect_middle_re = re.compile(r'message')
expect_end_re = re.compile(r'end\s+expect')


def destring(string):
    return string[1:-1].replace(r'\"', '\"').replace(r'\n', '\n').replace(r'\t', '\t')

loaded_examples = {}

def load_examples(filename):
    if filename in loaded_examples:
        return loaded_examples[filename]
    else:
        sort = None
        state = None
        current = None
        accum_start = ''
        accum_end = ''
        examples = {}
        with open(filename) as f:
            for line in f.readlines():
                if state is None:
                    matches = example_start_re.search(line)
                    if matches:
                        state = 'start'
                        sort = 'example'
                        current = matches.group('name')
                        accum_start = ''
                    matches2 = expect_start_re.search(line)
                    if matches2:
                        state = 'start'
                        sort = 'expect'
                        current = matches2.group('name')
                        accum_start = ''
                elif state == 'start':
                    if sort == 'example':
                        matches = example_middle_re.search(line)
                        if matches:
                            state = 'end'
                            accum_end = ''
                        else:
                            accum_start += line
                    elif sort == 'expect':
                        matches = expect_middle_re.search(line)
                        if matches:
                            state = 'end'
                            accum_end = ''
                        else:
                            accum_start += line
                elif state == 'end':
                    if sort == 'example':
                        matches = example_end_re.search(line)
                        if matches:
                            state = None
                            sort = None
                            examples[current] = (textwrap.dedent(accum_start.rstrip()), textwrap.dedent(accum_end.rstrip()))
                            accum_start = ''
                            accum_end = ''
                            current = None
                        else:
                            accum_end += line
                    elif sort == 'expect':
                        matches = expect_end_re.search(line)
                        if matches:
                            state = None
                            sort = None
                            examples[current] = (textwrap.dedent(accum_start.rstrip()), destring(textwrap.dedent(accum_end.rstrip())))
                            accum_start = ''
                            accum_end = ''
                            current = None
                        else:
                            accum_end += line
        loaded_examples[filename] = examples
        return examples

def rewrite_example_in(project_root):
    def rewrite(found):
        filename = f"{project_root}{os.path.sep}examples{os.path.sep}{found.group('file')}"
        example_name = found.group('name')
        examples = load_examples(filename)
        return examples[example_name][0]
    return rewrite

def rewrite_example_out(project_root):
    def rewrite(found):
        filename = f"{project_root}{os.path.sep}examples{os.path.sep}{found.group('file')}"
        example_name = found.group('name')
        examples = load_examples(filename)
        return examples[example_name][1]
    return rewrite

def rewrite_examples(context, book):
    project_root = Path(context['root']).parent
    def rewrite_chapters(chapters):
        for ch in chapters:
            ch['Chapter']['content'] = example_in_re.sub(rewrite_example_in(project_root), ch['Chapter']['content'])
            ch['Chapter']['content'] = example_out_re.sub(rewrite_example_out(project_root), ch['Chapter']['content'])
            rewrite_chapters(ch['Chapter']['sub_items'])

    rewrite_chapters(book['sections'])
    return book

def main():
    if len(sys.argv) > 1:
        if sys.argv[1] == "supports":
            sys.exit(0)
    context, book_contents = json.load(sys.stdin)
    print(json.dumps(rewrite_examples(context, book_contents)))

if __name__ == '__main__':
    main()
