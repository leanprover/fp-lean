import json
import os


def emit_pandoc_markdown(book):
    root = book['root']
    title = book['config']['book']['title']
    authors = book['config']['book']['authors']
    print(f"Root = {root}")
    print(f"Title = {title}")
    print(f"Authors = {authors}")
    sections = book['book']['sections']
    print(f"Book = {sections}")

    with open(f"{book['destination']}{os.path.sep}metadata.json", "w") as f:
        pass


def main():
    json_str = input()
    book_contents = json.loads(json_str)
    print(json.dumps(book_contents, indent = 4))
    emit_pandoc_markdown(book_contents)

if __name__ == '__main__':
    main()
