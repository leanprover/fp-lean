# Functional Programming in Lean

This repository contains the source code of the book Functional Programming in Lean by David Thrane Christiansen.

The original version of the book was released by Microsoft Corporation in 2023 under a Creative Commons Attribution 4.0 International License. The current version has been modified by the author from the original version to account for changes in newer versions of Lean and to use Verso; these changes are copyright 2023-2025 Lean FRO, LLC. A detailed account of the changes can be found in the book's [source code repository](https://github.com/leanprover/fp-lean/).

Generally speaking, the code in this repository is not intended to work on all computers. The purpose of the repository is to produce the book's HTML for readers. In particular, it probably only works on Unix-like systems, due to the way that the built-in tests exercise the programs built in the book. Building the book requires a C compiler available as `cc`, with the POSIX headers, a Unix-like shell, Python 3 available as `python3`, and [elan](https://github.com/leanprover/elan) with its executables on `PATH`. The first build needs Internet access to download the Lean toolchains and dependencies pinned by the repository.

To build the book, change to the [`book`](book/) directory and run `lake exe fp-lean`. After this, `book/_out/html-multi` contains a multi-page Web version of the book.

To read the book locally, remain in `book/`, serve the generated directory over HTTP, and open the address that the server prints:

```
lake exe verso-serve
```

The generated HTML can also be copied to another machine and served without Lean or Lake. For example, from the repository root:

```sh
python3 -m http.server --bind 127.0.0.1 --directory book/_out/html-multi 8000
```

Open <http://127.0.0.1:8000/>. Use a local HTTP server rather than opening `index.html` with a `file://` URL: navigation and JavaScript data loading rely on HTTP. The book text, search, and code tooltips work without Internet access once the HTML has been built. Links to other websites still require Internet access.

## Publishing

The book is published by pushing a tag whose name starts with `release-`. CI builds the tagged commit and deploys it to the production site. Publication happens on `release-` tags alone.

Every other build gets a preview deploy instead: pushes to `master`, pull requests (including those from forks), and manual runs. The preview URL appears as a `netlify/deploy` status on the commit that was built.

The build runs in [`ci.yml`](.github/workflows/ci.yml) and hands the HTML to [`deploy.yml`](.github/workflows/deploy.yml) as an artifact. The credentials live in the deploy workflow, which is what lets a pull request from a fork build and preview.

