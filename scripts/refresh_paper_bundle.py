# SPDX-License-Identifier: Apache-2.0
"""Package exactly the active local TeX inputs for a standalone paper build."""
from pathlib import Path
import io
import re
import tarfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    paper = ROOT / "paper"
    pending = [Path("main.tex")]
    included = set()
    while pending:
        relative = pending.pop()
        if relative in included:
            continue
        source = (paper / relative).resolve()
        if not source.is_relative_to(paper.resolve()):
            raise SystemExit("Nonlocal paper input: " + str(relative))
        text = source.read_text(encoding="utf-8")
        included.add(relative)
        for name in re.findall(r"\\(?:input|include)\{([^}]+)\}", text):
            child = Path(name)
            if not child.suffix:
                child = child.with_suffix(".tex")
            pending.append(child)
    with tarfile.open(paper / "source.tar.gz", "w:gz") as archive:
        for relative in sorted(included):
            data = (paper / relative).read_bytes().replace(b"\r\n", b"\n")
            info = tarfile.TarInfo(relative.as_posix())
            info.size = len(data)
            info.mode = 0o644
            info.mtime = 0
            archive.addfile(info, io.BytesIO(data))
    print("Packaged", len(included), "active TeX inputs.")


if __name__ == "__main__":
    main()
