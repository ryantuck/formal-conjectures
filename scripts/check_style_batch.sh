#!/bin/bash

# scripts/check_style_batch.sh
# Usage: ./scripts/check_style_batch.sh START END

START=$1
END=$2

if [ -z "$START" ] || [ -z "$END" ]; then
    echo "Usage: $0 START END"
    exit 1
fi

mkdir -p style-review

for i in $(seq "$START" "$END"); do
    file="FormalConjectures/ErdosProblems/$i.lean"
    
    if [ ! -f "$file" ]; then
        continue
    fi

    out="style-review/$i.md"
    echo "# Style Review - Erdős Problem $i" > "$out"
    echo "" >> "$out"
    echo "## Checklist Verification" >> "$out"
    echo "" >> "$out"

    # 3. Copyright header
    if grep -q "Copyright 2026" "$file"; then
        echo "- [x] **3. Copyright header present**" >> "$out"
    else
        year=$(grep "Copyright" "$file" | head -n 1 | grep -oE "[0-9]{4}")
        echo "- [f] **3. Copyright header present** - Year is $year, should be 2026." >> "$out"
    fi

    # 5. Question format / 19-21. Answer elaborator
    # Only fail if it uses the OLD answer pattern. If it uses NEITHER, it might be a statement.
    if grep -q "answer(" "$file"; then
        echo "- [x] **5. Question format**" >> "$out"
        echo "- [x] **19. answer(sorry) for unknowns**" >> "$out"
    elif grep -q "\(answer\s*:\s*Prop\)\s*:\s*answer\s*↔" "$file" || grep -q "answer :" "$file"; then
        echo "- [f] **5. Question format** - Uses non-standard answer parameter instead of elaborator." >> "$out"
    else
        echo "- [x] **5. Question format** - Statement (no answer elaborator needed or used)." >> "$out"
    fi

    # 6. Statement format / 13. Theorem docstring
    if grep -q "English version:" "$file"; then
        echo "- [x] **6. Statement format**" >> "$out"
        echo "- [x] **13. Theorem docstring**" >> "$out"
    else
        echo "- [ ] **6. Statement format** - Missing 'English version:' prefix." >> "$out"
        echo "- [ ] **13. Theorem docstring** - Missing 'English version:' prefix." >> "$out"
    fi

    # 8. AMS attribute
    if grep -qE "AMS [0-9]{2}" "$file"; then
        echo "- [x] **8. AMS attribute present**" >> "$out"
    elif grep -qE "AMS [0-9][^0-9]" "$file"; then
        echo "- [f] **8. AMS attribute present** - Single-digit AMS code (should be two digits)." >> "$out"
    else
        echo "- [ ] **8. AMS attribute present** - Missing AMS code." >> "$out"
    fi

    # 10. File docstring / 12. Problem description
    if grep -q "/-!" "$file"; then
        echo "- [x] **10. File docstring present**" >> "$out"
        if grep -q "STATUS:" "$file"; then
            echo "- [x] **12. Problem description**" >> "$out"
        else
            echo "- [ ] **12. Problem description** - Missing STATUS: line." >> "$out"
        fi
    else
        echo "- [ ] **10. File docstring present**" >> "$out"
        echo "- [ ] **12. Problem description**" >> "$out"
    fi

    # 18. Namespace
    if grep -q "namespace Erdos$i" "$file"; then
        echo "- [x] **18. Namespace usage**" >> "$out"
    else
        echo "- [f] **18. Namespace usage** - Incorrect namespace." >> "$out"
    fi

    echo "" >> "$out"
    echo "## Conclusion" >> "$out"
    echo "" >> "$out"
    
    # Simple logic to determine Status
    if grep -q "\[ \]\|\[f\]" "$out"; then
        echo "**Status: FAIL**" >> "$out"
    else
        echo "**Status: PASS**" >> "$out"
    fi

    echo "" >> "$out"
    echo "Automatically generated review highlighting style inconsistencies." >> "$out"
done
