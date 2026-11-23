"""Verify the released bytes, formal audit and bilingual equations. Run with Python 3."""
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ED = ROOT / "preprints/SPLITGAPII"
QA = ED / "02_validation/v1.0"
LEAN = QA / "lean"
MANIFEST = ED / "04_integrity/SHA256SUMS"
ARCHIVE = ROOT / "archives/split-gap-ii-preprint-v1.0.zip"
DOI = "10.5281/zenodo.24452724"
URL = "https://github.com/jtraverso/split-clique-partition-gap-ii"


def check(ok, message):
    if not ok:
        raise SystemExit("FAIL: " + message)


def read(path):
    return path.read_text(encoding="utf-8-sig")


def data(path):
    return json.loads(read(path))


def digest(binary):
    return sha256(binary).hexdigest()


def main():
    entries = [row.split("  ", 1) for row in read(MANIFEST).splitlines()]
    files = {p.relative_to(ED).as_posix(): p for p in ED.rglob("*") if p.is_file() and p != MANIFEST}
    check(len(entries) == len(files) and set(files) == {n for _, n in entries}, "edition manifest coverage")
    for h, n in entries:
        check(digest(files[n].read_bytes()) == h, n)
    files[MANIFEST.relative_to(ED).as_posix()] = MANIFEST
    check(read(ARCHIVE.with_suffix(".zip.sha256")).strip() == digest(ARCHIVE.read_bytes())+"  "+ARCHIVE.name, "archive digest")
    with ZipFile(ARCHIVE) as z:
        prefix = "SPLITGAPII-v1.0/"
        check(z.testzip() is None and sorted(z.namelist()) == sorted(prefix+n for n in files), "archive CRC and contents")
        for n, p in files.items():
            check(z.read(prefix+n) == p.read_bytes(), "archive member "+n)

    index = data(ED/"PUBLICATION_INDEX.json")
    receipt = data(QA/"doi-reservation.json")
    check(index["doi"] == receipt["doi"] == DOI and receipt["submitted"] is False, "reservation at audit")
    check(index["repository"] == URL and index["title_en"] == receipt["title"] and index["version"]=="1.0", "official metadata")
    check(DOI in read(ROOT/"CITATION.cff") and URL in read(ROOT/"CITATION.cff"), "citation")
    docs = [read(ED/f"01_manuscript/split-gap-ii-{lang}.md") for lang in ("en","es")]
    for lang, doc in zip(("en","es"),docs):
        check(doc.splitlines()[0][2:] == index["title_"+lang] and DOI in doc and URL in doc, lang+" title and identifiers")
        check(re.findall(r"\\tag\{(\d+)\}",doc)==list(map(str,range(1,12))),lang+" equation numbering")
        check(re.findall(r"^\*\*(?:Theorem|Lemma|Corollary|Proposition|Teorema|Lema|Corolario|Proposición) (\d+)",doc,re.M)==list(map(str,range(1,11))),lang+" theorem numbering")
        check(re.findall(r"^\[(\d+)\] ",doc,re.M)==list(map(str,range(1,9))),lang+" bibliography numbering")
    maths = [re.findall(r"\$\$.*?\$\$|\$[^$\n]+\$", s,re.S) for s in docs]
    check(maths[0] == maths[1], "every inline and displayed formula in translation")
    check("10.1017/S0963548320000280" in docs[0], "published EGJ citation")

    expected=data(LEAN/"SOURCE_HASHES.json")
    with ZipFile(ED/"05_formalization/split-gap-ii-lean-v1.0.zip") as z:
        check(z.testzip() is None and sorted(z.namelist())==sorted("lean/"+n for n in expected),"Lean archive contents")
        for n,h in expected.items():
            raw=z.read("lean/"+n)
            check(digest(raw)==h and raw==(ROOT/"lean"/n).read_bytes().replace(b"\r\n",b"\n"),"Lean source "+n)
    allow={"propext","Classical.choice","Quot.sound"}
    proofs={}
    for row in read(LEAN/"all-theorems.tsv").splitlines()[1:]:
        mod,name,ax=row.split("\t")
        check((mod,name) not in proofs and ax.startswith("#[") and ax.endswith("]"),"theorem record "+name)
        proofs[mod,name]=set(filter(None,ax[2:-1].split(", ")))
    check(all(a<=allow for a in proofs.values()),"kernel theorem axioms")
    names=re.findall(r"#print axioms (\S+)",read(ROOT/"lean/SplitGapIIAudit.lean"))
    named=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]", read(LEAN/"checking-axioms.log"))
    check([n for n,_ in named]==names and len(names)==25,"named axiom report")
    for name,ax in named:
        check(set(ax.replace("\n"," ").replace(" ","").split(","))<=allow and name in {n for _,n in proofs},name)
    report=data(QA/"AUDIT_RESULT.json")
    check(report["technical_audit"]=="PASS" and len(proofs)==report["theorem_declarations"],"audit scope")
    for n,h in report["artifacts"].items():
        check(digest((ED/n).read_bytes())==h,"audited artifact "+n)
    check(read(ED/"03_reproducibility/six_core.py")==read(ROOT/"examples/six_core.py"),"example sources")
    result=subprocess.check_output([sys.executable,str(ROOT/"examples/six_core.py")],text=True)
    check(result.splitlines()==read(QA/"six-core.log").splitlines(),"exact finite example")
    print(f"PASS: {len(entries)} edition files, {len(expected)} frozen Lean files, {len(proofs)} theorem declarations, {len(names)} named checks, {len(maths[0])} bilingual math spans, three exact optima.")


if __name__ == "__main__":
    main()
