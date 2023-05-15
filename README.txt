Functional Programming in Lean

This repository contains the source code of the book Functional Programming in Lean by David Thrane Christiansen.

All contents are copyright (C) Microsoft Corporation. As an open-source release by Microsoft, this project is covered by the Microsoft Open Source Code of Conduct at https://opensource.microsoft.com/codeofconduct/ . This project may contain trademarks or logos for projects, products, or services. Authorized use of Microsoft trademarks or logos is subject to and must follow Microsoft’s Trademark & Brand Guidelines. Use of Microsoft trademarks or logos in modified versions of this project must not cause confusion or imply Microsoft sponsorship. Any use of third-party trademarks or logos are subject to those third-party’s policies.

The book's build has been tested with:

1. Lean 4 (see the version in lean-toolchain in examples/)
2. mdbook version 0.4.17
3. Python 3.10.4
4. expect (tested with v5.45.4 but any version from the last decade should work)

To check the code examples, change to the "examples" directory and run "lake build".

To build the book, change to the "functional-programming-lean" directory and run "mdbook build". After this, "book/html/index.html" contains a multi-page Web version of the book.

The structure of the repository is as follows:
* examples/ contains the example code used in the book, as well as support code for the examples written in Lean.
* functional-programming-lean/ contains the source code for the text of the book. This has two parts:
  * scripts/ contains the Python scripts that are used to implement the custom preprocessors that are used with mdbook to include the code samples
  * src/ contains the Markdown sources

In order to enable programs to be run prior to their definitions, to include error messages that are checked by the book's CI, and to allow multiple versions of the same definition, the module Examples.Support contains a number of metaprograms. These metaprograms are associated with an intentionally-verbose syntax that's easy to extract from example files using regular expressions. Each example is associated with a name, and the text of the book contains references to these names in a custom syntax extension to Markdown. The book's preprocessors extract the examples, inserting them into the text prior to the generation of HTML.

Examples that are to be compiled and run are included using a different system. The file projects.py implements preprocessors for setting up fresh temporary directories based on some subdirectory of examples/, and then running a series of commands in these temporary directories, comparing the output to some expected string. This ensures that changes to Lean that affect the runtime behavior of programs are caught in the book's CI, and that mistakes introduced during editing are caught early. Much of the code to be compiled uses mdbook's built-in support for including sections of files, because it works well for this purpose.
