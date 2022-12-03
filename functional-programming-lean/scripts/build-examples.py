import json
import subprocess
import sys


def main():
    if len(sys.argv) > 1:
        if sys.argv[1] == "supports":
            sys.exit(0)
    subprocess.run('lake build', shell=True, cwd=f'../examples', check=True, capture_output=True)
    context, book_contents = json.load(sys.stdin)
    print(json.dumps(book_contents))

if __name__ == '__main__':
    main()
