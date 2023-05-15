# Contribution Guidelines

This project is a single-author text. Generally speaking, I'm not interested in pull requests that modify the text of the online book, because I want to maintain a single coherent authorial voice and style for readers. Additionally, the book is now considered to be complete. It may receive updates to keep it up to date with changes in Lean 4 over time, or to fix errors, but I do not expect to add significant amounts of new content.

## Mistakes

If you find a mistake in the book, please open an issue! I'd like this book to be a correct and reliable resource, and to stay that way over time.

Please don't open issues for questions about Lean or solving exercises. These discussions are better suited to the [Lean Zulip](https://leanprover.zulipchat.com/).

## Book Infrastructure

The infrastructure of the book, like the Lean metaprograms in `Examples.Support` and the Python scripts that extract examples into the text, is currently "good enough". This means that the code is not as elegant as it could be, but it's sufficient to accomplish its task. If you re-use this code in your own book project and find bugs, then I'd like to fix them here too, but I'm not generally interested in stylistic improvements.

The code exists to create the rendered HTML version of the book, primarily when running on GitHub Actions and secondarily on Unix-like systems such as WSL, Linux, or macOS. I'm not interested in generalizations to other platforms or contexts because I don't have the time and expertise to maintain them.

## Pull Requests

Generally speaking, pull requests are not welcome without prior agreement. Should you wish to contribute a pull request, you'll need to [sign a CLA](https://cla.opensource.microsoft.com/) with Microsoft. Please contact Sarah Smith (smithsarah@microsoft.com) or Gabriel Ebner (gabrielebner@microsoft.com) if you have any questions about this.
