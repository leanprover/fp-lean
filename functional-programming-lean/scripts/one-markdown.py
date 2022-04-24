import json
import os
import re
import subprocess


def bump_headers(level, md):
    def new_header(old_header):
        return old_header.group(1) + ('#' * level) + ' '
    # The space in the regexp is necessary to avoid rewriting #eval &c
    return re.sub(r'^(#+) ', new_header, md, flags=re.MULTILINE)

def emit_pandoc_markdown(book):
    root = book['root']
    title = book['config']['book']['title']
    authors = book['config']['book']['authors']
    sections = book['book']['sections']

    pandoc_metadata = {'title': title, 'author': authors}
    pandoc_metadata_file = os.path.join(book['destination'], 'metadata.json')
    with open(pandoc_metadata_file, 'w') as f:
        json.dump(pandoc_metadata, f)

    pandoc_dest = os.path.join(book['destination'], 'md')

    output_files = []
    if not os.path.exists(pandoc_dest):
        os.makedirs(pandoc_dest)

    def next_special(counter=[0]):
        counter[0] += 1
        return f"s{counter[0]}"

    def emit_sections(sections):
        for s in sections:
            ch = s['Chapter']
            # There is an assumption here that unnumbered sections live at the top level.
            if ch['number'] is not None:
                filename = os.path.join(pandoc_dest, '-'.join(str(i) for i in ch['number']) + '.md')
                header = ('#' * len(ch['number'])) + ' ' + ch['name']
                content = bump_headers(len(ch['number']), ch['content'])
            else:
                filename = os.path.join(pandoc_dest, next_special() + '.md')
                header = '# ' + ch['name'] + '{.unnumbered}'
                content = bump_headers(1, ch['content'])

            with open(filename, 'w') as f:
                f.write(header)
                f.write('\n\n')
                f.write(content)
                f.write('\n')
            output_files.append(filename)
            emit_sections(ch['sub_items'])
    emit_sections(sections)
    return (pandoc_metadata_file, output_files)

def main():
    json_str = input()
    book_contents = json.loads(json_str)
    meta, output = emit_pandoc_markdown(book_contents)
    subprocess.call(['pandoc', '--top-level-division=chapter', f'--metadata-file={meta}', '-o', 'book.epub', '-f', 'commonmark_x', '--number-sections'] + output)
    subprocess.call(['pandoc', '--top-level-division=chapter', f'--metadata-file={meta}', '-o', 'book.pdf', '--pdf-engine=xelatex', '-f', 'commonmark_x', '--toc', '--number-sections'] + output)

if __name__ == '__main__':
    main()
