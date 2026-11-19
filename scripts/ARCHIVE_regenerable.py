#!/usr/bin/env python3
"""Archive the regenerable, git-ignored bulk of the working tree into git-pushable chunks (user, 10/10/2026: "push mấy cái tạo lại dc lên
git đi r xoá luôn đi"), so that it can be removed from disk only after it is on GitHub.
  build <name>   name in {scenarios, tripinfo, lean}: the ignored files of that kind (scenarios/, scenarios_partial_*/ copies; SUMO tripinfo/;
                 Lean .lake/ and *.olean / *.ilean / *.trace), listed NUL-separated in archives/regenerable_20261010/<name>.list, streamed
                 bsdtar (hardlinks stored once) | zstd -T10 -10 | split into 95-MiB parts <name>.tar.zst.partNNN; MANIFEST_<name>.json records
                 every part's sha256 and size, the file count and the unique-content size.
  verify <name>  reads the parts back (cat | zstd -d), walks the tar stream (python tarfile 'r|'), hashes every regular member and checks it
                 against the file on disk; checks that every listed path is in the archive and that each hardlink member points to a path with
                 the same inode on disk.  Writes VERIFY_<name>.txt; exit 1 on any mismatch.
  delete <name>  only if HEAD == origin/<branch>, every part is in origin's tree with the manifest's sha256, and VERIFY_<name>.txt says PASS:
                 removes the listed files (and the directories this leaves empty).  Restore: cat <name>.tar.zst.part* | zstd -d | bsdtar -x -f -
Run from the repository root."""
import hashlib, json, os, subprocess, sys, tarfile
from pathlib import Path

OUT = Path('archives/regenerable_20261010'); PART = 95 * 2 ** 20; BRANCH = 'backup/full-corpus-20260915'


def kind(p):
    if '/scenarios/' in p or '/scenarios_partial_' in p:
        return 'scenarios'
    if '/tripinfo/' in p:
        return 'tripinfo'
    if '/.lake/' in p or p.endswith(('.olean', '.ilean', '.trace')):
        return 'lean'
    return None


def listing(name):
    out = subprocess.run(['git', 'ls-files', '--others', '--ignored', '--exclude-standard', '-z', '--', 'research', 'work', 'legacy'],
                         capture_output=True, check=True).stdout.split(b'\0')
    return sorted(p.decode() for p in out if p and kind(p.decode()) == name and os.path.isfile(p.decode()) and not os.path.islink(p.decode()))


def sha(path, bufsize=2 ** 20):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(bufsize), b''):
            h.update(b)
    return h.hexdigest()


def build(name):
    OUT.mkdir(parents=True, exist_ok=True); files = listing(name)
    (OUT / f'{name}.list').write_bytes(b'\0'.join(p.encode() for p in files) + b'\0')
    ino = {}
    for p in files:
        st = os.stat(p); ino[(st.st_dev, st.st_ino)] = st.st_size
    for old in OUT.glob(f'{name}.tar.zst.part*'):
        old.unlink()                                                    # only our own partial output of an earlier attempt
    env = dict(os.environ, COPYFILE_DISABLE='1')                       # no AppleDouble ._ members
    tar = subprocess.Popen(['bsdtar', '-c', '-f', '-', '--no-mac-metadata', '--no-xattrs', '--null', '-T', str(OUT / f'{name}.list')], stdout=subprocess.PIPE, env=env)
    z = subprocess.Popen(['zstd', '-q', '-T10', '-10', '-c'], stdin=tar.stdout, stdout=subprocess.PIPE); tar.stdout.close()
    parts = []; i = 0
    while True:
        buf = z.stdout.read(PART)
        if not buf:
            break
        fn = OUT / f'{name}.tar.zst.part{i:03d}'; fn.write_bytes(buf); parts.append(dict(file=fn.name, size=len(buf), sha256=hashlib.sha256(buf).hexdigest())); i += 1
        print(f'{name}: part {i} ({sum(p["size"] for p in parts) / 2 ** 30:.2f} GB)', flush=True)
    assert z.wait() == 0 and tar.wait() == 0, 'bsdtar / zstd failed'
    man = dict(name=name, files=len(files), unique_inodes=len(ino), unique_bytes=sum(ino.values()), parts=parts, compressed_bytes=sum(p['size'] for p in parts),
               restore=f'cat {OUT}/{name}.tar.zst.part* | zstd -d | bsdtar -x -f -   (from the repository root)')
    (OUT / f'MANIFEST_{name}.json').write_text(json.dumps(man, indent=1)); print(json.dumps({k: v for k, v in man.items() if k != 'parts'}), flush=True)


def verify(name):
    man = json.loads((OUT / f'MANIFEST_{name}.json').read_text()); want = set((OUT / f'{name}.list').read_bytes().decode().split('\0')) - {''}
    for p in man['parts']:
        assert sha(OUT / p['file']) == p['sha256'], f'part {p["file"]} differs from the manifest'
    cat = subprocess.Popen(['cat'] + [str(OUT / p['file']) for p in man['parts']], stdout=subprocess.PIPE)
    z = subprocess.Popen(['zstd', '-q', '-d', '-c'], stdin=cat.stdout, stdout=subprocess.PIPE); cat.stdout.close()
    seen = set(); bad = []; nreg = nlink = 0
    with tarfile.open(fileobj=z.stdout, mode='r|') as tf:
        for m in tf:
            if m.isreg():
                f = tf.extractfile(m); h = hashlib.sha256()
                for b in iter(lambda: f.read(2 ** 20), b''):
                    h.update(b)
                if h.hexdigest() != sha(m.name):
                    bad.append(('content', m.name))
                nreg += 1
            elif m.islnk():
                a, b = os.stat(m.name), os.stat(m.linkname)
                if (a.st_dev, a.st_ino) != (b.st_dev, b.st_ino):
                    bad.append(('hardlink', m.name))
                nlink += 1
            seen.add(m.name)
    assert z.wait() == 0
    missing = sorted(want - seen)
    ok = not bad and not missing
    rep = (f'{name}: {nreg} regular + {nlink} hardlink members; listed {len(want)}; missing {len(missing)}; mismatches {len(bad)} {bad[:5]} '
           f'{missing[:5]}\n{"PASS" if ok else "FAIL"}\n')
    (OUT / f'VERIFY_{name}.txt').write_text(rep); print(rep, flush=True); sys.exit(0 if ok else 1)


def delete(name):
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    org = subprocess.run(['git', 'rev-parse', f'origin/{BRANCH}'], capture_output=True, text=True).stdout.strip()
    assert head and head == org, 'HEAD is not pushed'
    assert (OUT / f'VERIFY_{name}.txt').read_text().strip().endswith('PASS'), 'not verified'
    man = json.loads((OUT / f'MANIFEST_{name}.json').read_text())
    for p in man['parts']:
        blob = subprocess.run(['git', 'cat-file', '-p', f'origin/{BRANCH}:{OUT}/{p["file"]}'], capture_output=True, check=True).stdout
        assert hashlib.sha256(blob).hexdigest() == p['sha256'], f'{p["file"]} on origin differs from the manifest'
    files = [p for p in (OUT / f'{name}.list').read_bytes().decode().split('\0') if p]; freed = {}; n = 0
    for p in files:
        if os.path.isfile(p):
            st = os.stat(p); freed[(st.st_dev, st.st_ino)] = st.st_size; os.remove(p); n += 1
    dirs = sorted({str(Path(p).parent) for p in files}, key=lambda d: -d.count('/'))
    for d in dirs:                                                      # empty directories left behind, deepest first
        q = Path(d)
        while q != Path('.') and q.exists() and not any(q.iterdir()):
            q.rmdir(); q = q.parent
    print(f'{name}: removed {n} files ({sum(freed.values()) / 2 ** 30:.2f} GB unique content); restore with: {man["restore"]}', flush=True)


if __name__ == '__main__':
    {'build': build, 'verify': verify, 'delete': delete}[sys.argv[1]](sys.argv[2])
