#!/usr/bin/env python3
"""Check that the seven restated definitions of Challenge.lean and OB/Defs.lean agree character for character
with each other and with the two challenge files of openai/math at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, up to the namespace: IsSign, aperiodic and IsBarker with
lean/ComparatorChallenges/EvenBarker.lean (scripts/EvenBarker-oai.txt) and RealMatrix, IsCirculant,
IsSignHadamard and ExistsRealCirculantHadamard with lean/ComparatorChallenges/CirculantHadamard.lean
(scripts/CirculantHadamard-oai.txt). The reference copies are not part of the development. Docstrings
are not compared (the upstream files carry none). Exit status 0 means every definition block agrees."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
REFERENCES = {
    "scripts/EvenBarker-oai.txt": ["IsSign", "aperiodic", "IsBarker"],
    "scripts/CirculantHadamard-oai.txt": ["RealMatrix", "IsCirculant", "IsSignHadamard",
                                          "ExistsRealCirculantHadamard"],
}
HOUSE = ["canon"]  # defined here, compared between Challenge.lean and OB/Defs.lean only
NAMES = [name for names in REFERENCES.values() for name in names] + HOUSE


def blocks(text):
    """The definition blocks, keyed by name: from the `abbrev`/`def` line to the blank line after it."""
    out = {}
    lines = text.splitlines()
    for idx, line in enumerate(lines):
        m = re.match(r"^(abbrev|def) (\w+)", line)
        if m and m.group(2) in NAMES:
            end = idx
            while end + 1 < len(lines) and lines[end + 1].strip() != "":
                end += 1
            out[m.group(2)] = "\n".join(lines[idx:end + 1])
    return out


def main():
    ref = {}
    for rel, names in REFERENCES.items():
        found = blocks((ROOT / rel).read_text(encoding="utf-8"))
        for name in names:
            if name not in found:
                print(f"reference {rel} lacks {name}")
                sys.exit(1)
            ref[name] = found[name]
    ok = True
    chal = blocks((ROOT / "Challenge.lean").read_text(encoding="utf-8"))
    defs = blocks((ROOT / "OB/Defs.lean").read_text(encoding="utf-8"))
    for name in HOUSE:
        if name not in chal or name not in defs or chal[name] != defs[name]:
            print(f"house definition {name} missing or differs between Challenge.lean and OB/Defs.lean")
            ok = False
        else:
            print(f"ok    Challenge.lean = OB/Defs.lean: {name}")
    for rel in ("Challenge.lean", "OB/Defs.lean"):
        ours = blocks((ROOT / rel).read_text(encoding="utf-8"))
        for name in NAMES:
            if name in HOUSE:
                continue
            if name not in ours:
                print(f"{rel} lacks {name}")
                ok = False
            elif ours[name] != ref[name]:
                print(f"{rel}: {name} differs from the reference")
                print("  ours:", ours[name].replace("\n", "\n        "))
                print("  ref: ", ref[name].replace("\n", "\n        "))
                ok = False
            else:
                print(f"ok    {rel}: {name}")
    print("ALL DEFINITIONS AGREE" if ok else "DEFINITIONS DIFFER")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
