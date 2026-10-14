import os

dirs = ['Spqr/Crypto/Fips203', 'Spqr/Specs/IncrementalMlkem768']

for d in dirs:
    for root, _, files in os.walk(d):
        for fname in files:
            if not fname.endswith('.lean'):
                continue
            path = os.path.join(root, fname)
            with open(path, 'r') as f:
                content = f.read()

            lines = content.split('\n')
            new_lines = []
            changed = False

            for line in lines:
                stripped = line.strip()
                # Make any non-public import public (skip 'import all')
                if stripped.startswith('import ') and not stripped.startswith('import all'):
                    new_lines.append('public ' + line)
                    changed = True
                else:
                    new_lines.append(line)

            if changed:
                with open(path, 'w') as f:
                    f.write('\n'.join(new_lines))
                print(f'Updated {path}')
