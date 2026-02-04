import yaml
import os

with open('erdos-problems-data.yaml', 'r') as f:
    data = yaml.safe_load(f)

unformalized_in_yaml = []
for p in data:
    if isinstance(p, dict) and p.get('formalized', {}).get('state') == 'no':
        unformalized_in_yaml.append(p['number'])

# Check FormalConjectures/ErdosProblems/
existing_files = os.listdir('FormalConjectures/ErdosProblems')
existing_numbers = [f.replace('.lean', '') for f in existing_files if f.endswith('.lean')]

truly_unformalized = [n for n in unformalized_in_yaml if n not in existing_numbers]

print("Total unformalized in YAML:", len(unformalized_in_yaml))
print("Unformalized problems (YAML marked 'no' and no .lean file):")
print(', '.join(truly_unformalized))
