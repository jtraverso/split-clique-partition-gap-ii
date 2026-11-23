"""Verify the sealed bytes, formal audit and bilingual equations. Run with Python 3."""
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile
import json
import re
import subprocess
import sys

ED = Path(__file__).resolve().parents[1]
QA = ED / "02_validation/v1.0"
LEAN = QA / "lean"
MANIFEST = ED / "04_integrity/SHA256SUMS"
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
    index = data(ED/"PUBLICATION_INDEX.json")
    receipt = data(QA/"doi-reservation.json")
    check(index["doi"] == receipt["doi"] == DOI and receipt["submitted"] is False, "reservation at audit")
    check(index["repository"] == URL and index["title_en"] == receipt["title"] and index["version"]=="1.0", "official metadata")
    docs = [read(ED/f"01_manuscript/split-gap-ii-{lang}.md") for lang in ("en","es")]
    for lang, doc in zip(("en","es"),docs):
        check(doc.splitlines()[0][2:] == index["title_"+lang] and DOI in doc and URL in doc, lang+" title and identifiers")
        check(re.findall(r"\\tag\{(\d+)\}",doc)==list(map(str,range(1,12))),lang+" equation numbering")
        check(re.findall(r"^\*\*(?:Theorem|Lemma|Corollary|Proposition|Teorema|Lema|Corolario|Proposición) (\d+[a-z]?)",doc,re.M)=="1 2 3 4 5 5a 6 6a 7 8 9 10".split(),lang+" theorem numbering")
        check(re.findall(r"^\[(\d+)\] ",doc,re.M)==list(map(str,range(1,10))),lang+" bibliography numbering")
    docs = [d.replace(r"\text{ahorro total}",r"\text{total saving}").replace("$5000$","$5{,}000$") for d in docs]
    for d in docs:
        check("[1]" in d.split("## 1.")[0] and "10.5281/zenodo.24408988" in d, "Part I attribution")
    maths = [re.findall(r"\$\$.*?\$\$|\$[^$\n]+\$", s,re.S) for s in docs]
    check(maths[0] == maths[1], "every inline and displayed formula in translation")
    check("10.1017/S0963548320000280" in docs[0], "published EGJ citation")

    ledgers = [read(ED/f"06_proof_ledger/ledger-{lang}.md") for lang in ("en","es")]
    def paragraph_math(source):
        return [sorted(re.findall(r"\$\$.*?\$\$|\$[^$\n]+\$", paragraph,re.S))
                for paragraph in source.split("\n\n")]
    check(paragraph_math(ledgers[0])==paragraph_math(ledgers[1]),"ledger mathematical translation")
    for stem, record in data(QA/"PDF_QA.json").items():
        folder = "05_formalization" if stem.startswith("companion-") else ("06_proof_ledger" if stem.startswith("ledger-") else "01_manuscript")
        for ext in ("pdf","tex"):
            check(digest((ED/folder/(stem+"."+ext)).read_bytes()) == record[ext+"_sha256"],stem+" "+ext)
        if folder == "01_manuscript":
            check(len(record["printed_reference_urls"]) == 9,stem+" printed references")

    expected=data(LEAN/"SOURCE_HASHES.json")
    check(digest((ED/"05_formalization/split-gap-ii-lean-v1.0.zip").read_bytes())=="fb167eed7405bc79ab3680ab6207a6911415448fd48786db690291034c19c074","unchanged reviewed Lean freeze")
    with ZipFile(ED/"05_formalization/split-gap-ii-lean-v1.0.zip") as z:
        check(z.testzip() is None and sorted(z.namelist())==sorted("lean/"+n for n in expected),"Lean archive contents")
        named_src=z.read("lean/SplitGapIIAudit.lean").decode()
        for n,h in expected.items():
            raw=z.read("lean/"+n)
            check(digest(raw)==h,"Lean source "+n)
    allow={"propext","Classical.choice","Quot.sound"}
    proofs={}
    for row in read(LEAN/"all-theorems.tsv").splitlines()[1:]:
        mod,name,ax=row.split("\t")
        check((mod,name) not in proofs and ax.startswith("#[") and ax.endswith("]"),"theorem record "+name)
        proofs[mod,name]=set(filter(None,ax[2:-1].split(", ")))
    check(all(a<=allow for a in proofs.values()),"kernel theorem axioms")
    names=re.findall(r"#print axioms (\S+)",named_src)
    named=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]", read(LEAN/"checking-axioms.log"))
    check([n for n,_ in named]==names and len(names)==25,"named axiom report")
    for name,ax in named:
        check(set(ax.replace("\n"," ").replace(" ","").split(","))<=allow and name in {n for _,n in proofs},name)
    report=data(QA/"AUDIT_RESULT.json")
    check(report["technical_audit"]=="PASS" and len(proofs)==report["theorem_declarations"],"audit scope")
    for n,h in report["artifacts"].items():
        check(digest((ED/n).read_bytes())==h,"audited artifact "+n)
    extra = re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",read(LEAN/"edition11-axioms.log"))
    check([n.rsplit(".",1)[-1] for n,_ in extra] == ["local_deletion_list_sizes","single_deletion_gap_jump"],"new Lean statements")
    check(all(set(ax.split(", ")) <= allow for _,ax in extra),"additional kernel axioms")
    for stem in ("six","eight"):
        program = ED/"03_reproducibility"/(stem+"_core.py")
        result = subprocess.check_output([sys.executable,"-O","-X","utf8",str(program)],encoding="utf8")
        check(result.splitlines()==read(QA/(stem+"-core.log")).splitlines(),stem+"-core certificate")
    print(f"PASS: {len(entries)} sealed files, {len(expected)} Lean sources/configuration files, {len(proofs)} inherited theorem records and {len(extra)} new axiom records, {len(maths[0])} bilingual math spans, five exact states.")


if __name__ == "__main__":
    main()
