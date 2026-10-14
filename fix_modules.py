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

            if '@[expose] public section' in content:
                print(f'SKIP (already has expose) {path}')
                continue

            lines = content.split('\n')
            new_lines = []
            last_import_idx = -1

            # Find the last import line index
            for i, line in enumerate(lines):
                stripped = line.strip()
                if stripped.startswith('import ') or stripped.startswith('public import '):
                    last_import_idx = i

            if last_import_idx == -1:
                print(f'SKIP (no imports) {path}')
                continue

            for i, line in enumerate(lines):
                stripped = line.strip()
                # Make non-public imports public (skip 'import all')
                if stripped.startswith('import ') and not stripped.startswith('import all') and not stripped.startswith('import Spqr.Crypto.Fips203.Bridge'):
                    new_lines.append('public ' + line)
                else:
                    new_lines.append(line)

                # After last import, insert @[expose] public section
                if i == last_import_idx:
                    new_lines.append('@[expose] public section')

            with open(path, 'w') as f:
                f.write('\n'.join(new_lines))
            print(f'Updated {path}')
