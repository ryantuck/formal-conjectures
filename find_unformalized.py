import yaml

try:
    with open('erdos-problems-data.yaml', 'r') as f:
        data = yaml.safe_load(f)

    unformalized = []
    for p in data:
        if isinstance(p, dict) and p.get('formalized', {}).get('state') == 'no':
            unformalized.append(p['number'])

    # Filter for numbers > 43
    next_problems = [n for n in unformalized if int(n) > 43]
    print('\n'.join(next_problems[:20]))

except Exception as e:
    print(f"Error: {e}")

