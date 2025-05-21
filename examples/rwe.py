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


def deindent_anchored_sections(text, anchor_prefix="-- ANCHOR:", anchor_end_prefix="-- ANCHOR_END:"):
    lines = text.splitlines()
    result_lines = []
    current_anchor = None
    anchor_lines = []
    anchor_start_index = -1

    i = 0
    while i < len(lines):
        line = lines[i]

        # Check if this is an anchor start line
        if line.strip().startswith(anchor_prefix):
            current_anchor = line.strip()[len(anchor_prefix):].strip()
            anchor_start_index = i
            anchor_lines = [line]
            i += 1

            # Collect all lines in this anchor block
            while i < len(lines) and not lines[i].strip().startswith(anchor_end_prefix):
                anchor_lines.append(lines[i])
                i += 1


            # Add the end anchor line if we found it
            if i < len(lines):
                anchor_lines.append(lines[i])
                i += 1

            # Process the anchor block
            # Find minimum indentation of non-empty lines between start and end markers
            content_lines = anchor_lines[1:-1]  # Exclude anchor start/end lines
            non_empty_lines = [l for l in content_lines if l.strip()]

            if non_empty_lines:
                min_indent = min(len(l) - len(l.lstrip()) for l in non_empty_lines)

                # Apply deindentation
                for j in range(1, len(anchor_lines) - 1):  # Skip anchor start/end lines
                    line_content = anchor_lines[j]
                    if line_content.strip():  # Only deindent non-empty lines
                        # Calculate the actual indent of this line
                        current_indent = len(line_content) - len(line_content.lstrip())
                        # Remove exactly min_indent spaces, but not more than the current indent
                        spaces_to_remove = min(min_indent, current_indent)
                        anchor_lines[j] = line_content[spaces_to_remove:]

            # Add processed lines to result
            result_lines.extend(anchor_lines)

        else:
            result_lines.append(line)
            i += 1

    return "\n".join(result_lines) + "\n"

def replace_expect(match):
    kind = match.group(1)
    anchor_id = match.group(2).strip()
    content = match.group(3)  # This contains the code
    message_str = match.group(4).strip()  # This contains the quoted STR part

    # Process the message string to remove quotes and unescape characters
    if (message_str.startswith('"') and message_str.endswith('"')):
        # Remove surrounding quotes and trailing newlines or spaces
        message_str = message_str[1:-1].rstrip()

        # Unescape special characters
        message_str = message_str.replace('\\"', '"')  # Unescape double quotes
        message_str = message_str.replace("\\'", "'")  # Unescape single quotes
        message_str = message_str.replace("\\n", "\n") # Convert literal \n to newlines
        message_str = message_str.replace("\\t", "\t") # Convert literal \t to tabs
        message_str = message_str.replace("\\\\", "\\") # Convert literal \\ to \

    transformed = f"/-- {kind}:\n{message_str}\n-/\n#check_msgs in\n-- ANCHOR: {anchor_id}\n{content}-- ANCHOR_END: {anchor_id}"
    return transformed


def apply_transformations(content):

    content = re.sub(
        r'expect\s+(error|info)\s+\{\{\{\s*([^ }]+)\s*\}\}\}[ ]*\n(.*?)message\s+(.*?)end\s+expect',
        replace_expect,
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'book\s+declaration\s+\{\{\{\s*([^ }]+)\s*\}\}\}[ ]*\n(.*?)\nstop\s+book\s+declaration',
        r'-- ANCHOR: \1\n\2\n-- ANCHOR_END: \1',
        content,
        flags=re.DOTALL
    )


    content = re.sub(
        r'bookExample\s+type\s+\{\{\{\s*([^ }]+)\s*\}\}\}\s*(.*?)\s*<?===>?\s*(.*?)\s*end\s+bookExample',
        r'-- ANCHOR: \1\nexample : \3 := \2\n-- ANCHOR_END: \1',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'bookExample\s+\{\{\{\s*([^ }]+)\s*\}\}\}\s*(.*?)\s*===>\s*(.*?)\s*end\s+bookExample',
        r'-- ANCHOR: \1\nexample : (\n\2\n) = (\n\3\n) := rfl\n-- ANCHOR_END: \1',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'bookExample\s+:\s*([^{]+?)\s*\{\{\{\s*([^ }]+)\s*\}\}\}\s*(.*?)\s*===>\s*(.*?)\s*end\s+bookExample',
        r'-- ANCHOR: \2\nexample : (\3 : (\1)) = (\4 : (\1)) := rfl\n-- ANCHOR_END: \2',
        content,
        flags=re.DOTALL
    )

    content = re.sub(
        r'equational\s+steps\s*([^\{]*?)\s*\{\{\{\s*([^ }]+)\s*\}\}\} *\n(?!--\s*ANCHOR)(.*?)\n *?stop\s+equational\s+steps',
        r'equational steps \1 {{{ \2 }}}\n-- ANCHOR: \2\n\3\n-- ANCHOR_END: \2\nstop equational steps',
        content,
        flags=re.DOTALL
    )


    content = re.sub(
        r'evaluation\s+steps\s*([^\{]*?)\s*\{\{\{\s*([^ }]+)\s*\}\}\} *\n(?!--\s*ANCHOR)(.*?)\n *?end\s+evaluation\s+steps',
        r'evaluation steps \1 {{{ \2 }}}\n-- ANCHOR: \2\n\3\n-- ANCHOR_END: \2\nend evaluation steps',
        content,
        flags=re.DOTALL
    )


    # de-indent anchors
    content = deindent_anchored_sections(content)

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
