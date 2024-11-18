#!/bin/bash

# Directory containing .dot files
DOT_DIR="./diagram"

# Check if the directory exists
if [ ! -d "$DOT_DIR" ]; then
    echo "Error: $DOT_DIR does not exist."
    exit 1
fi

# Convert .dot files to .png
for dot_file in "$DOT_DIR"/*.dot; do
    if [ -f "$dot_file" ]; then
        png_file="${dot_file%.dot}.png"
        dot -Tpng -o "$png_file" "$dot_file"
        echo "Converted $dot_file to $png_file"
    fi
done

echo "Conversion complete."
