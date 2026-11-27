# SPDX-License-Identifier: Apache-2.0
"""Negative controls for the proof-source scanner."""
from check_submission import code_only
import re
assert 'sorry' not in code_only('/- sorry /- axiom -/ -/ module\n-- sorry\n"axiom"')
assert re.search(r'\bsorry\b',code_only('module\ntheorem x : True := by sorry'))
assert re.search(r'\baxiom\b',code_only('module\naxiom x : False'))
for text in ('/- unterminated','"unterminated'):
    try:code_only(text)
    except ValueError:pass
    else:raise AssertionError('Unterminated source accepted')
print('Source scanner positive and negative controls passed.')
