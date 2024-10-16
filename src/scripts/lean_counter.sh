#!/bin/bash

# Function to process a single Lean file
process_file() {
    local file="$1"
    local folder="$2"

    # Count total theorems, lemmas, and definitions
    local total_count=$(grep -c '^theorem\|^lemma\|^def' "$file")

    # Run Lean and capture its output
    local lean_output=$(lean "$file" 2>&1)

    # Count errors and warnings
    local error_count=$(echo "$lean_output" | grep -c "error")
    local warning_count=$(echo "$lean_output" | grep -c "warning")

    # Calculate correct statements (this is an estimate)
    local correct_count=$((total_count - error_count))

    echo "$folder,$total_count,$error_count,$warning_count,$correct_count"
}

# Main script
echo "Folder,Total Statements,Errors,Warnings,Estimated Correct Statements"

# Loop through all numbered folders
for folder in artefacts/apps/train/*/; do
    # Remove trailing slash from folder name
    folder=${folder%/}
    file="$folder/Proof.lean"
    if [ -f "$file" ]; then
        process_file "$file" "$folder"
    fi
done