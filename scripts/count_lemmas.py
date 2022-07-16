#!/usr/bin/env python

# ## Instructions
# Run inside repo (but not in _target/deps)
# Uses the parser that github uses for syntax highlighting, so might not be quite right.

import logging
import os
from collections import defaultdict
from pathlib import Path

try:
    import git
    import pygments
    from pygments.lexers.theorem import LeanLexer
    from pygments.token import Token
except ModuleNotFoundError:
    print("You need to run this: pip install Pygments gitpython")
    exit()

logger = logging.getLogger(__file__)


def get_git_root():
    git_repo = git.Repo(".", search_parent_directories=True)
    return git_repo.git.rev_parse("--show-toplevel")


os.chdir(get_git_root())


def count_in_file(file_contents, lexer):
    counters = defaultdict(int)
    generator = pygments.lex(file_contents, lexer)
    for token in generator:
        token_type, token_text = token
        if token_type == Token.Keyword.Declaration and token_text in [
            "def",
            "lemma",
            "theorem",
        ]:
            counters[token_text] += 1
    return counters


global_counter = defaultdict(int)
for path in Path("src").rglob("*.lean"):
    if path == Path("src", "all.lean"):
        logger.info("Skipping all.lean")
        continue
    with open(path, "r") as f:
        file_counter = count_in_file(f.read(), LeanLexer())
        for key, value in file_counter.items():
            global_counter[key] += value

for key, value in global_counter.items():
    print(f"Number of {key}s: {value}")
print("\nCounters exclude commented-out code.")
