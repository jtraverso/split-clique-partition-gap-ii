"""Build the English and Spanish Markdown sources with Pandoc and Tectonic."""
from argparse import ArgumentParser
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
EDITION = HERE.parent
REPOSITORY = "https://github.com/jtraverso/split-clique-partition-gap-ii"
FILES = sorted(EDITION.glob("01_manuscript/split-gap-*.md")) + sorted(EDITION.glob("05_formalization/companion-*.md"))


def figures(body):
    def convert(match):
        name, _, caption = match.groups()
        return (
            r"\begin{figure}[htbp]" + "\n"
            + rf"\centering\includegraphics[width=.73\linewidth]{{figures/{name}.png}}" + "\n"
            + rf"\caption{{{caption}}}\label{{fig:{name}}}" + "\n"
            + r"\end{figure}"
        )

    return re.subn(
        r"!\[[^\n]*\]\(figures/([\w-]+)\.png\)\n\n\*(?:Figure|Figura) (\d+)\. ([^\n]+)\*",
        convert,
        body,
    )


def tables(body):
    def convert(match):
        rows = [line.strip("|").split("|") for line in match.group().strip().splitlines()]
        data = [" & ".join(cell.strip().replace("−", "$-$") for cell in row) + r" \\"
                for row in [rows[0], *rows[2:]]]
        return "\n".join([
            r"\begin{center}", r"\begin{tabular}{" + "c" * len(rows[0]) + "}",
            r"\toprule", data[0], r"\midrule", *data[1:],
            r"\bottomrule", r"\end{tabular}", r"\end{center}", "",
        ])

    return re.sub(r"(?:^\|[^\n]*\|[ \t]*\n)+", convert, body, flags=re.M)


def tex_source(md, pandoc):
    source = md.read_text(encoding="utf-8")
    title = source.splitlines()[0][2:]
    spanish = md.stem.endswith("-es")
    paper = md.stem.startswith("split-gap")
    if paper:
        body, count = figures(source[source.index("## Resumen" if spanish else "## Abstract"):])
        if count != 2:
            raise ValueError("Expected two numbered figures")
        body = tables(body)
    else:
        title = title.replace("*", "")
        body = source[source.index("## Alcance" if spanish else "## What the formal statement says"):]
    if not paper:
        prefix = REPOSITORY + "/blob/main/preprints/SPLITGAPII/"
        body = re.sub(r"\]\(\.\./((?:01_manuscript|02_validation|03_reproducibility)/[^)]+)\)",
                      lambda m: "](" + prefix + m[1] + ")", body)
        body = re.sub(r"\]\((split-gap-lean-v1\.0\.zip|LICENSE-Apache-2\.0\.txt)\)",
                      lambda m: "](" + prefix + "05_formalization/" + m[1] + ")", body)
    body = body.replace("#### ", "### ")
    body = subprocess.run(
        [pandoc, "-f", "markdown+raw_tex+tex_math_dollars", "-t", "latex", "--wrap=none", "--syntax-highlighting=none"],
        input=body, stdout=subprocess.PIPE, text=True, encoding="utf-8", check=True,
    ).stdout
    preamble = (HERE / "preamble.tex").read_text(encoding="utf-8")
    lines = [
        preamble.rstrip(),
        r"\clubpenalty=10000\widowpenalty=10000",
        r"\DeclareMathSizes{9}{10}{7}{5}",
        r"\hypersetup{pdflang={en-US},colorlinks=true,linkcolor=blue,urlcolor=blue,citecolor=blue}",
        rf"\hypersetup{{pdftitle={{{title}}},pdfauthor={{Juan Pablo Traverso Gianini}}}}",
        rf"\title{{{title}}}",
        (r"\author{Juan Pablo Traverso Gianini\\\small Independent researcher, Santiago, Chile"
         r"\\\small\href{mailto:jtraverso@gmail.com}{jtraverso@gmail.com}"
         r"\quad\href{https://orcid.org/0009-0003-6068-4096}{ORCID 0009-0003-6068-4096}}"),
        r"\date{Preprint 1.1 \enspace · \enspace November 23, 2026}",
        r"\begin{document}\raggedbottom\maketitle",
        r"\noindent\textbf{Reserved DOI:} \url{https://doi.org/10.5281/zenodo.24452724}\\",
        rf"\textbf{{Official repository:}} \url{{{REPOSITORY}}}",
        body.replace("\n\n\\[", "\n\\["), r"\end{document}", "",
    ]
    if not paper:
        lines[0] = lines[0].replace("11pt,a4paper", "10pt,a4paper").replace("margin=1in","margin=0.82in")
        lines = [line.replace(r"\maketitle", r"\maketitle\vspace{-1.5em}") for line in lines]
    if spanish:
        lines[0] = lines[0].replace("[english,","[spanish,").replace("[english]{babel}", "[spanish,es-noshorthands]{babel}")
        lines = [line.replace("en-US", "es-CL").replace("Independent researcher", "Investigador independiente")
                 .replace("November 23, 2026", "23 de noviembre de 2026").replace("Reserved DOI:", "DOI reservado:")
                 .replace("Official repository:", "Repositorio oficial:").replace("Formalization companion (PDF)", "Guía de la formalización (PDF)")
                 .replace("{Manuscript}", "{Manuscrito}").replace("companion-en.pdf", "companion-es.pdf")
                 .replace("split-gap-en.pdf", "split-gap-es.pdf") for line in lines]
        lines.insert(1, r"\AtBeginDocument{\renewcommand{\figurename}{Figura}}")
    return "\n".join(lines)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--pandoc", default="pandoc")
    parser.add_argument("--tectonic", default="tectonic")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--only-cached", action="store_true")
    parser.add_argument("--language", choices=["en", "es"])
    args = parser.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(EDITION) or EDITION.is_relative_to(output):
        parser.error("Choose an output directory separate from the edition")
    output.mkdir(parents=True, exist_ok=True)
    for md in FILES:
        if args.language and not md.stem.endswith("-" + args.language):
            continue
        dest = output / md.parent.name
        dest.mkdir(exist_ok=True)
        if (md.parent / "figures").is_dir():
            shutil.copytree(md.parent / "figures", dest / "figures", dirs_exist_ok=True)
        tex = dest / md.with_suffix(".tex").name
        tex.write_text(tex_source(md, args.pandoc), encoding="utf-8", newline="\n")
        command = [args.tectonic, "--keep-logs", "--outdir", str(dest), str(tex)]
        if args.only_cached:
            command.insert(1, "--only-cached")
        for run in range(1, 4):
            cp = subprocess.run(command, cwd=tex.parent, capture_output=True)
            log = output / f"{tex.stem}-pass-{run}.log"
            log.write_bytes(cp.stdout + cp.stderr)
            if cp.returncode:
                raise SystemExit((cp.stdout + cp.stderr).decode(errors="replace"))
            print(log.name, "PASS", flush=True)
        pdf = tex.with_suffix(".pdf")
        assert pdf.stat().st_mtime_ns >= tex.stat().st_mtime_ns



if __name__ == "__main__":
    main()
