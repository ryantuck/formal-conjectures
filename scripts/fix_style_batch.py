import os
import re
import sys

def fix_file(file_path, problem_id):
    with open(file_path, 'r') as f:
        content = f.read()

    # 1. Copyright Year
    content = re.sub(r'Copyright 2025', 'Copyright 2026', content)

    # 2. AMS Code (single digit to two digits)
    content = re.sub(r'AMS ([0-9])([^0-9])', r'AMS 0\1\2', content)

    # 3. File docstring (Ensure it exists and has STATUS)
    is_solved = 'solved' in content.lower() or 'PROVED' in content or 'SOLVED' in content
    status_str = "STATUS: SOLVED" if is_solved else "STATUS: OPEN"
    
    if '/-!' not in content:
        import_match = re.search(r'import .*?\n', content)
        if import_match:
            pos = import_match.end()
            file_doc = f"\n/-!\n# Erd\u0151s Problem {problem_id}\n\n{status_str}\n\n*Reference:* [erdosproblems.com/{problem_id}](https://www.erdosproblems.com/{problem_id})\n-/\n"
            content = content[:pos] + file_doc + content[pos:]
    else:
        if 'STATUS:' not in content:
            content = re.sub(r'(# Erd\u0151s Problem [0-9]+\n)', r'\1\n' + status_str + r'\n', content)

    # 4. Theorem/Lemma docstrings (prepend English version:)
    
    # First, handle existing docstrings
    content = re.sub(r'(?s)(/--((?!English version:).)*?-/)\s*(@\[category)', r'/--\nEnglish version: \2-/\n\3', content)

    # Next, handle theorems/lemmas that MISS a docstring entirely
    # Look for @[category...] not preceded by /-- ... -/
    def add_missing_doc(match):
        full_match = match.group(0)
        # Check if there is a docstring right before this match
        # We search backwards from the start of the match in the original content
        start_pos = match.start()
        # Look at the last few characters before the match
        before = content[max(0, start_pos-100):start_pos]
        if '-/' not in before:
            return f"/-- English version:  -/\n{full_match}"
        return full_match

    content = re.sub(r'@\[category', add_missing_doc, content)

    # 5. Standardize answer parameter
    ans_val = 'True' if is_solved else 'sorry'
    if 'answer(False)' in content: ans_val = 'False'
    elif 'answer(True)' in content: ans_val = 'True'

    content = re.sub(r'\(answer\s*:\s*[A-Za-z0-9\s→]+\)\s*:', f':', content)
    content = re.sub(r':\s+answer\s+↔', f': answer({ans_val}) ↔', content)
    content = re.sub(r'\banswer\b(?!\()', f'answer({ans_val})', content)

    # 6. Namespace
    if f'namespace Erdos{problem_id}' not in content:
        file_doc_end = re.search(r'-\/\s*?\n', content)
        if file_doc_end:
            pos = file_doc_end.end()
            imports_after = re.search(r'(import .*?\n\s*)*', content[pos:])
            if imports_after:
                 pos += imports_after.end()
            content = content[:pos] + f"\nnamespace Erdos{problem_id}\n" + content[pos:]
            if f'end Erdos{problem_id}' not in content:
                content = content + f"\nend Erdos{problem_id}\n"

    # 7. Cleanup
    content = re.sub(r'English version:\s+English version:', 'English version:', content)
    content = re.sub(r'/--\nEnglish version: \s+\n', r'/--\nEnglish version: ', content)
    content = re.sub(r'English version:\s*\n\s*-/', 'English version: -/', content)
    content = re.sub(r'/-- English version:\s+-/', '/-- English version: -/', content)

    with open(file_path, 'w') as f:
        f.write(content)

if __name__ == "__main__":
    start = int(sys.argv[1])
    end = int(sys.argv[2])
    for i in range(start, end + 1):
        file_path = f"FormalConjectures/ErdosProblems/{i}.lean"
        if os.path.exists(file_path):
            fix_file(file_path, i)
