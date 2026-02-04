import yaml

def get_next_problems(start_from, count):
    try:
        with open('erdos-problems-data.yaml', 'r') as f:
            data = yaml.safe_load(f)
        
        unformalized = []
        for p in data:
            if isinstance(p, dict):
                try:
                    num = int(p['number'])
                    if num > start_from and p.get('formalized', {}).get('state') == 'no':
                        unformalized.append(num)
                except ValueError:
                    continue
        
        return unformalized[:count]

    except Exception as e:
        print(f"Error: {e}")
        return []

if __name__ == "__main__":
    problems = get_next_problems(73, 50)
    for p in problems:
        print(p)
