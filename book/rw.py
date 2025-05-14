#!/usr/bin/env python3
"""
File Rewriting Script

This script processes text files and applies a set of regex transformations.
Usage: python rewrite_file.py input_file [output_file]

If no output file is specified, the original file will be overwritten.
"""

import re
import sys
import argparse
from pathlib import Path


def apply_transformations(content):
    """Apply all regex transformations to the content."""
    # Example 1: Transform example_decl blocks
    content = re.sub(
        r'```lean\(tac\)\s*\{\{#example_decl\s+[^\s]+\s+([^}]+)\}\}\s*```',
        r'\n{exampleDecl \1}\n',
        content,
        flags=re.DOTALL
    )

    # Example 2: Transform example_in blocks
    content = re.sub(
        r'```lean\s*\{\{#example_in\s+[^\s]+\s+([^}]+)\}\}\s*```',
        r'\n{exampleIn \1}\n',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'```lean\s*\{\{#include\s+([^}:]+)/([^}:./]+)\.lean:([^}]+)\}\}\s*```',
        r'```module \2 (anchor:=\3)\n```\n',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'```lean\s*\{\{#example_eval\s+[^\s]+\s+([^}]+)\}\}\s*```',
        r'\n{exampleEval \1}\n',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'`\{\{#command\s+\{([^}]+)\}\s+\{([^}]+)\}\s+\{([^}]+)\}\s*\}\}`',
        r'{command \2 "\1"}`\3`',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'`\{\{#command_out\s+\{([^}]+)\}\s+\{([^}]+)\}\s*\}\}`',
        r'{command \1}`\2`',
        content,
        flags=re.DOTALL
    )


    content = re.sub(
        r'```\s*\{\{#command\s+\{([^}]+)\}\s+\{([^}]+)\}\s+\{([^}]+)\}\s*\}\}\s*```',
        r'```command \2 "\1" "\3"\n```\n',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'```\s*\{\{#command_out\s+\{([^}]+)\}\s+\{([^}]+)\}\s*\}\}\s*```',
        r'```commandOut \1 "\2"\n```\n',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'```\s*\{\{#command_out\s+\{([^}]+)\}\s+\{([^}]+)\}\s*\{[^}]+\}\s*\}\}\s*```',
        r'```commandOut \1 "\2"\n```\n',
        content,
        flags=re.DOTALL
    )


    content = re.sub(
        r'```lean\s*\{\{#file_contents\s+\{([^}]+)\}\s+\{([^}]+)}\s*\{[^}]+\}\s*\}\}\s*```',
        r'```file \1 "\2"\n\n```\n',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'```lean\s*\{\{#file_contents\s+\{([^}]+)\}\s+\{([^}]+)}\s*\}\}\s*```',
        r'```file \1 "\2"\n\n```\n',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'```\s*\{\{#include\s+([^}]+)\}\}\s*```',
        r'```plainFile "\1"\n```\n',
        content,
        flags=re.DOTALL
    )


    content = re.sub(
        r'```output\s+error\s*\{\{#example_out\s+[^\s]+\s+([^}]+)\}\}\s*```',
        r'\n{exampleError \1}\n',
        content,
        flags=re.DOTALL
    )

    # Example 5: Transform example_out info blocks
    content = re.sub(
        r'```output\s+info\s*\{\{#example_out\s+[^\s]+\s+([^}]+)\}\}\s*```',
        r'\n{exampleInfo \1}\n',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'`\{\{#include\s+([^:}]+)/([^/.]+).lean:([^}]+)\}\}`',
        r'{module (anchor:=\3)}`\2`',
        content
    )


    # Example 4: Transform example_eval in-line references (not necessarily at start of line)
    content = re.sub(
        r'`\{\{#example_eval\s+[^\s]+\s+([^\s]+)\s+(\d+)\}\}`',
        r'{exampleEval \2}`\1`',
        content
    )

    content = re.sub(
        r'`\{\{#example_in\s+[^\s]+\s+([^\s]+)\}\}`',
        r'{exampleIn}`\1`',
        content
    )

    content = re.sub(
        r'`\{\{#example_out\s+[^\s]+\s+([^\s]+)\}\}`',
        r'{exampleOut}`\1`',
        content
    )


    content = content.replace(r'\\( ', '$`')
    content = content.replace(r' \\)', '`')

    content = re.sub(r'(?<!{kw})`def`', r'{kw}`def`', content)
    content = re.sub(r'(?<!{kw})`theorem`', r'{kw}`theorem`', content)
    content = re.sub(r'(?<!{kw})`by`', r'{kw}`by`', content)
    content = re.sub(r'(?<!{kw})`let`', r'{kw}`let`', content)
    content = re.sub(r'(?<!{kw})`fun`', r'{kw}`fun`', content)
    content = re.sub(r'(?<!{kw})`match`', r'{kw}`match`', content)
    content = re.sub(r'(?<!{kw})`if let`', r'{kw}`if let`', content)
    content = re.sub(r'(?<!{kw})`if`', r'{kw}`if`', content)
    content = re.sub(r'(?<!{kw})`then`', r'{kw}`then`', content)
    content = re.sub(r'(?<!{kw})`else`', r'{kw}`else`', content)
    content = re.sub(r'(?<!{kw})`structure`', r'{kw}`structure`', content)
    content = re.sub(r'(?<!{kw})`inductive`', r'{kw}`inductive`', content)
    return content


def process_file(input_path, output_path=None):
    """
    Process a file by applying transformations and writing the result.
    If output_path is None, overwrites the input file.
    """
    # Read the input file
    with open(input_path, 'r', encoding='utf-8') as file:
        content = file.read()

    # Apply transformations
    transformed_content = apply_transformations(content)

    # Determine output path
    final_output_path = output_path if output_path else input_path

    # Write the output
    with open(final_output_path, 'w', encoding='utf-8') as file:
        file.write(transformed_content)

    print(f"Processed {input_path} -> {final_output_path}")


def main():
    """Parse arguments and process the file."""
    parser = argparse.ArgumentParser(description='Rewrite files based on regex patterns.')
    parser.add_argument('input_file', help='Path to the input file')
    parser.add_argument('output_file', nargs='?', help='Path to the output file (optional)')

    args = parser.parse_args()

    input_path = Path(args.input_file)
    output_path = Path(args.output_file) if args.output_file else None

    if not input_path.exists():
        print(f"Error: Input file '{input_path}' does not exist.", file=sys.stderr)
        sys.exit(1)

    try:
        process_file(input_path, output_path)
    except Exception as e:
        print(f"Error processing file: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
