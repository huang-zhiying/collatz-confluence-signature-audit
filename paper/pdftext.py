"""Read-only helpers for asserting on PDF text.

Two traps this exists to avoid:

  * A word split by hyphenation across a line or column break
    (``verify_rem_condi-`` + ``tion``) makes a naive ``needle in text`` fail
    even though the word is there. ``normalize`` rejoins it.
  * The abstract lives on page 1 and ends at ``Index Terms``; searching the
    whole document silently captures the rest of the paper.

Usage::

    from pdftext import count, abstract_words
    count("supplement.pdf", "verify_rem_condition.py")   # -> 1
    abstract_words("manuscript.pdf")                     # -> 241

Read-only by design: nothing here rebuilds, stages or writes. Run it against a
finished PDF; staging is always the last step of a release.
"""
import re
import subprocess

__all__ = ["text", "normalize", "count", "abstract_words"]


def text(pdf, page=None):
    """Text layer of a PDF (optionally one page), via poppler's pdftotext."""
    cmd = ["pdftotext"] + (["-f", str(page), "-l", str(page)] if page else []) + [pdf, "-"]
    return subprocess.run(cmd, capture_output=True).stdout.decode("utf-8", "ignore")


def normalize(t):
    """Rejoin hyphenated line breaks, then collapse all whitespace."""
    t = re.sub(r"(\w)-\s*\n\s*(\w)", r"\1\2", t)
    return " ".join(t.split())


def count(pdf, needle, page=None):
    """Occurrences of `needle`, insensitive to hyphenation and line breaks."""
    return normalize(text(pdf, page)).count(needle)


def abstract_words(pdf):
    """Word count of the abstract: page 1 only, up to ``Index Terms``."""
    p = normalize(text(pdf, 1))
    i, j = p.find("Abstract"), p.find("Index Terms")
    if i < 0 or j <= i:
        return None
    return len(p[i:j].split()) - 1          # drop the "Abstract" label itself
