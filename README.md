# Functional Programming in Lean

This repository contains the source code of the book Functional Programming in Lean by David Thrane Christiansen.

The original version of the book was released by Microsoft Corporation in 2023 under a Creative Commons Attribution 4.0 International License. The current version has been modified by the author from the original version to account for changes in newer versions of Lean and to use Verso; these changes are copyright 2023-2025 Lean FRO, LLC. A detailed account of the changes can be found in the book's [source code repository](https://github.com/leanprover/fp-lean/).


The book's build has been tested with:

1. Lean 4 (see the version in lean-toolchain in examples/)
2. expect (tested with v5.45.4 but any version from the last decade should work)

To build the book, change to the "book" directory and run "lake exe fp-lean". After this, "book/out/html-multi" contains a multi-page Web version of the book.

