"""Remove only reproducible Lake setup/C scratch; preserve all Lean objects.
Run between builds, never concurrently with Lake. No source or Git data is removed.
"""
from pathlib import Path
import shutil,sys
root=Path(__file__).resolve().parents[1]
if (root/'.lake/build/ir').is_symlink():
    raise SystemExit('Refusing a symlinked build directory')
free=shutil.disk_usage(root).free
if '--check' in sys.argv:
    print(f'{free/2**30:.2f} GiB free')
    if free<4*2**30:raise SystemExit('Below 4 GiB reserve; do not start a local build')
    raise SystemExit(0)
paths=list((root/'.lake/build/ir').rglob('*.setup.json'))+list((root/'.lake/build/ir').rglob('*.c'))
size=sum(p.stat().st_size for p in paths)
for p in paths:p.unlink()
print(f'Removed {len(paths)} generated scratch files ({size/2**20:.1f} MiB); retained Lean proof objects')
