import pathlib, sys
for path in sys.argv[1:]:
    p = pathlib.Path(path); L = p.read_text().split('\n'); out = []; i = 0; n = 0
    while i < len(L):
        if L[i].startswith('<<<<<<< '):
            b = next(k for k in range(i, len(L)) if L[k] == '======='); c = next(k for k in range(b, len(L)) if L[k].startswith('>>>>>>> '))
            out += L[i+1:b] + L[b+1:c]; i = c + 1; n += 1
        else:
            out.append(L[i]); i += 1
    p.write_text('\n'.join(out)); print(f'{path}: {n} hunk(s) keep-both')
