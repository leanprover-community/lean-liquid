import os
import re
import subprocess
import sys


SCRIPT_LOCATION = os.path.join(os.path.dirname(__file__), "print_thm95_axioms.lean")

# We need lean to rebuild this file each time otherwise our #print statement doesn't execute, so
# first delete its olean, if it exists.
try:
  os.remove(SCRIPT_LOCATION.replace(".lean", ".olean"))
except OSError:
  pass

completed_lean_process = subprocess.run(["lean", "--make", SCRIPT_LOCATION], capture_output=True)

if completed_lean_process.returncode or b"BEGIN_THM95_AXIOMS" not in completed_lean_process.stdout:
  print("Lean subprocess didn't complete successfully:")
  sys.stdout.buffer.write(completed_lean_process.stdout)
  exit(1)

output = completed_lean_process.stdout.decode('utf-8', errors='replace')
match = re.search("BEGIN_THM95_AXIOMS(.*)END_THM95_AXIOMS", output, flags=re.DOTALL)
thm95_axioms = match.group(1).strip().splitlines()

if "[sorry]" in thm95_axioms:
  print("Proof of Theorem 9.5 is not sorry-free.")
  exit(1)
else:
  print("Proof of Theorem 9.5 is sorry-free.")
