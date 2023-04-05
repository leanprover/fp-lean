import json
import re
import textwrap
from pathlib import Path
import os
import sys

def eprint(val):
    print(val, file=sys.stderr)

# Regexps for finding extension points in Markdown text
example_in_re = re.compile(r'\{\{#example_in\s+(?P<file>[^\s]+)\s+(?P<name>[^\s]+)\s*\}\}')
example_out_re = re.compile(r'\{\{#example_out\s+(?P<file>[^\s]+)\s+(?P<name>[^\s]+)\s*\}\}')
example_eval_re = re.compile(r'\{\{#example_eval\s+(?P<file>[^\s]+)\s+(?P<name>[^\s]+)\s+(?P<number>[0-9]+)\s*\}\}')
example_eval_many_re = re.compile(r'\{\{#example_eval\s+(?P<file>[^\s]+)\s+(?P<name>[^\s]+)\s*\}\}')
example_decl_re = re.compile(r'\{\{#example_decl\s+(?P<file>[^\s]+)\s+(?P<name>[^\s]+)\s*\}\}')
example_eq_re = re.compile(r'\{\{#equations\s+(?P<file>[^\s]+)\s+(?P<name>[^\s]+)\s*\}\}')

# Regexps for book examples
example_start_re = re.compile(r'bookExample\s+(type\s+)?(:[^{]+)?\{\{\{\s*(?P<name>[a-zA-Z0-9_]+)\s*\}\}\}')
example_middle_re = re.compile(r'===>|<===')
example_end_re = re.compile(r'end\s+bookExample')

# Regexps for definitions etc
example_decl_start_re = re.compile(r'book\s+declaration\s+\{\{\{\s*(?P<name>[a-zA-Z0-9_]+)\s*\}\}\}')
example_decl_end_re = re.compile(r'stop\s+book\s+declaration')

# Regexps for expected info/errors
expect_start_re = re.compile(r'expect\s+(eval\s+)?(info|error|warning)\s+\{\{\{\s*(?P<name>[a-zA-Z0-9_]+)\s*\}\}\}')
expect_middle_re = re.compile(r'message')
expect_end_re = re.compile(r'end\s+expect')

# Regexps for evaluation sequences
eval_start_re = re.compile(r'evaluation\s+steps\s+(:[^{]+)?\{\{\{\s*(?P<name>[a-zA-Z0-9_]+)\s*\}\}\}')
eval_middle_re = re.compile(r'===>')
eval_end_re = re.compile(r'end\s+evaluation steps')

# Regexps for equational reasoning
eq_start_re = re.compile(r'equational\s+steps\s+(:[^{]+)?\{\{\{\s*(?P<name>[a-zA-Z0-9_]+)\s*\}\}\}')
eq_middle_start_re = re.compile(r'=\{')
eq_middle_line_re = re.compile(r'^\s*--\s*(?P<line>.+)$')
eq_middle_end_re = re.compile(r'\}=')
eq_end_re = re.compile(r'stop\s+equational\s+steps')


def destring(string):
    return textwrap.dedent(string[1:-1].replace(r'\"', '\"').replace(r'\n', '\n').replace(r'\t', '\t').rstrip())

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
                    matches3 = eval_start_re.search(line)
                    if matches3:
                        state = 'start'
                        sort = ('eval', [])
                        current = matches3.group('name')
                        accum_start = ''
                    matches4 = eq_start_re.search(line)
                    if matches4:
                        state = 'start'
                        sort = ('eq_term', [])
                        current = matches4.group('name')
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
                    elif isinstance(sort, tuple) and len(sort) == 2 and sort[0] == 'eval':
                        matches_middle = eval_middle_re.search(line)
                        matches_end = eval_end_re.search(line)
                        if matches_middle:
                            sort[1].append(accum_start)
                            accum_start = ''
                        elif matches_end:
                            sort[1].append(accum_start)
                            examples[current] = [textwrap.dedent(x.rstrip()) for x in sort[1]]
                            state = None
                            sort = None
                            accum_start = ''
                            accum_end = ''
                            current = None
                        else:
                            accum_start += line
                    elif isinstance(sort, tuple) and len(sort) == 2 and sort[0] == 'eq_term':
                        matches_middle = eq_middle_start_re.search(line)
                        matches_end = eq_end_re.search(line)
                        if matches_middle:
                            sort[1].append(accum_start)
                            accum_start = ''
                            sort = ('eq_reason', sort[1])
                        elif matches_end:
                            sort[1].append(accum_start)
                            examples[current] = [textwrap.dedent(x.rstrip()) for x in sort[1]]
                            state = None
                            sort = None
                            accum_start = ''
                            accum_end = ''
                            current = None
                        else:
                            accum_start += line
                    elif isinstance(sort, tuple) and len(sort) == 2 and sort[0] == 'eq_reason':
                        matches_middle = eq_middle_end_re.search(line)
                        matches_end = eq_end_re.search(line)
                        matches_line = eq_middle_line_re.search(line)
                        if matches_middle:
                            sort[1].append(accum_start)
                            accum_start = ''
                            sort = ('eq_term', sort[1])
                        elif matches_end:
                            sort[1].append(accum_start)
                            examples[current] = [textwrap.dedent(x.rstrip()) for x in sort[1]]
                            state = None
                            sort = None
                            accum_start = ''
                            accum_end = ''
                            current = None
                        elif matches_line:
                            accum_start += matches_line['line']
                        else:
                            pass # this line is part of a Lean proof that's not there for readers

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

        # Load declarations as separate loop to prevent 100% spaghetti
        # (should refactor the whole loop, really)
        with open(filename) as f:
            for line in f.readlines():
                if state is None:
                    matches = example_decl_start_re.search(line)
                    if matches:
                        state = 'start'
                        sort = 'decl'
                        current = matches.group('name')
                        accum_start = ''
                elif state == 'start':
                    if sort == 'decl':
                        matches = example_decl_end_re.search(line)
                        if matches:
                            state = None
                            sort = None
                            examples[current] = textwrap.dedent(accum_start.rstrip())
                            current = None
                            accum_start = ''
                        else:
                            accum_start += line

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

def rewrite_example_eval(project_root):
    def rewrite(found):
        filename = f"{project_root}{os.path.sep}examples{os.path.sep}{found.group('file')}"
        example_name = found.group('name')
        example_eval_step = found.group('number')
        examples = load_examples(filename)
        return examples[example_name][int(example_eval_step)]
    return rewrite

def rewrite_example_eval_many(project_root):
    def rewrite(found):
        filename = f"{project_root}{os.path.sep}examples{os.path.sep}{found.group('file')}"
        example_name = found.group('name')
        examples = load_examples(filename)
        return '\n===>\n'.join(examples[example_name])
    return rewrite

markdown_code_re = re.compile(r'`([^`]+)`')

# This one has to generate interleaved HTML/Markdown to be reasonable. Ugh.
def rewrite_eq(project_root):
    def rewrite(found):
        filename = f"{project_root}{os.path.sep}examples{os.path.sep}{found.group('file')}"
        example_name = found.group('name')
        examples = load_examples(filename)
        out = '<div class="equational">\n'
        for (i, line) in enumerate(examples[example_name]):
            # Even indices are terms (Lean code)
            if i % 2 == 0:
                out += '<div class="term">\n'
                out += '<pre><code class="language-lean hljs">'
                # ouch. Markdown :-(
                out += line
                out += '</code></pre>\n'
            # Odd indices are explanations (Markdown)
            else:
                out += '<div class="explanation">\n'
                out += '={ <em>' + markdown_code_re.sub(r'<code class="hljs">\1</code>', line) + '</em> }=\n'
            out += '</div>\n'
        out += '</div>\n'
        return out
    return rewrite

def rewrite_example_decl(project_root):
    def rewrite(found):
        filename = f"{project_root}{os.path.sep}examples{os.path.sep}{found.group('file')}"
        example_name = found.group('name')
        examples = load_examples(filename)
        return examples[example_name]
    return rewrite


def rewrite_examples(context, book):
    project_root = Path(context['root']).parent
    def rewrite_chapters(chapters):
        for ch in chapters:
            ch['Chapter']['content'] = example_in_re.sub(rewrite_example_in(project_root), ch['Chapter']['content'])
            ch['Chapter']['content'] = example_out_re.sub(rewrite_example_out(project_root), ch['Chapter']['content'])
            ch['Chapter']['content'] = example_eval_re.sub(rewrite_example_eval(project_root), ch['Chapter']['content'])
            ch['Chapter']['content'] = example_eval_many_re.sub(rewrite_example_eval_many(project_root), ch['Chapter']['content'])
            ch['Chapter']['content'] = example_eq_re.sub(rewrite_eq(project_root), ch['Chapter']['content'])
            ch['Chapter']['content'] = example_decl_re.sub(rewrite_example_decl(project_root), ch['Chapter']['content'])
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
