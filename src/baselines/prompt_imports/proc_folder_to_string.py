import argparse
import os
import pathlib


def folder_to_string(folder_path: pathlib.Path) -> str:
    """
    Convert all text files in a folder (and its subfolders) into a single formatted string.
    Each file's content is preceded by its relative path and followed by '// END'.

    Args:
        folder_path (str): Path to the folder containing text files

    Returns:
        str: Formatted string containing all file contents
    """
    result = []

    # Walk through the directory tree
    for root, _, files in os.walk(folder_path):
        # Sort files for consistent output
        for file in sorted(files):
            # Only process text files
            if file.endswith(".lean"):
                file_path = pathlib.Path(root) / file
                # Get relative path from the input folder
                rel_path = file_path.relative_to(folder_path)

                try:
                    # Read file content
                    with open(file_path, "r", encoding="utf-8") as f:
                        content = f.read().strip()

                    # Format the file content
                    formatted_content = f"***\n{rel_path}\n\n{content}\n\n***\n"
                    result.append(formatted_content)

                except Exception as e:
                    print(f"Error reading {file_path}: {str(e)}")

    # Join all formatted contents with newlines
    return "\n".join(result)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--folder_path", type=pathlib.Path, required=True)
    parser.add_argument("--output_path", type=pathlib.Path, required=True)
    args = parser.parse_args()

    result = folder_to_string(args.folder_path)

    with open(args.output_path, "w", encoding="utf-8") as f:
        f.write(result)
