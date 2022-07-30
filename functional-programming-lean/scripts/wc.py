import json
import os
import re
import subprocess


def count_words(book):
    root = book['root']
    title = book['config']['book']['title']
    authors = book['config']['book']['authors']
    sections = book['book']['sections']

    def count_sections(sections, level=0):
        total = 0
        for s in sections:
            ch = s['Chapter']
            # There is an assumption here that unnumbered sections live at the top level.
            if ch['number'] is not None:
                num = '.'.join(str(i) for i in ch['number']) + '. '
                name = ch['name']
            else:
                num = ''
                name = ch['name']

            words = len([w for w in ch['content'].split() if any(c.isalpha() for c in w)])
            print(f'{" " * level}{num}{name}: {words}')
            if len(ch['sub_items']) > 0:
                subtotal = count_sections(ch['sub_items'], level=level+1)
                print(f' {" " * level}----------')
                print(f'{" " * level} Subtotal ({name}): {subtotal + words}')
                total += subtotal
            total += words
            if level == 0: print('')
        return total

    overall = count_sections(sections)
    print('---------------------')
    print(f'Total: {overall}')

def main():
    json_str = input()
    book_contents = json.loads(json_str)
    count_words(book_contents)

if __name__ == '__main__':
    main()
