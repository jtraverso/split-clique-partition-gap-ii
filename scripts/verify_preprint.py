"""Verify the official 1.1 repository and run the standalone edition verifier."""
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys
from zipfile import ZipFile

root = Path(__file__).resolve().parents[1]
edition = root / "preprints/SPLITGAPII-v1.1"
archive = root / "archives/split-gap-ii-preprint-v1.1.zip"
digest = sha256(archive.read_bytes()).hexdigest()
if archive.with_suffix(".zip.sha256").read_text().strip() != digest + "  " + archive.name:
    raise SystemExit("FAIL: distribution archive hash")
prefix = "SPLITGAPII-v1.1/"
files = {prefix+p.relative_to(edition).as_posix():p for p in edition.rglob("*") if p.is_file()}
with ZipFile(archive) as z:
    if sorted(z.namelist()) != sorted(files) or z.testzip() is not None:
        raise SystemExit("FAIL: archive members")
    for name, path in files.items():
        if z.read(name) != path.read_bytes():
            raise SystemExit("FAIL: archive member " + name)
sources = json.loads((edition/"02_validation/v1.1/lean/SOURCE_HASHES.json").read_text())
for name, h in sources.items():
    if sha256((root/"lean"/name).read_bytes().replace(b"\r\n",b"\n")).hexdigest() != h:
        raise SystemExit("FAIL: source " + name)
subprocess.run([sys.executable,str(edition/"03_reproducibility/verify_edition.py")],check=True)
print("PASS: repository sources, edition and distribution archive agree.")
