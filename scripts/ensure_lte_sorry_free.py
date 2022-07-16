import os
import re
import subprocess
import sys


SCRIPT_LOCATION = os.path.join(os.path.dirname(__file__), "print_lte_axioms.lean")

completed_lean_process = subprocess.run(["lean", "--run", SCRIPT_LOCATION], capture_output=True)

if completed_lean_process.returncode or b"BEGIN_LTE_AXIOMS" not in completed_lean_process.stdout:
  print("Lean subprocess didn't complete successfully:")
  sys.stdout.buffer.write(completed_lean_process.stdout)
  exit(1)

output = completed_lean_process.stdout.decode('utf-8', errors='replace')
match = re.search("BEGIN_LTE_AXIOMS(.*)END_LTE_AXIOMS", output, flags=re.DOTALL)
lte_axioms = match.group(1).strip().splitlines()

if "[sorry]" in lte_axioms:
  print("Proof of liquid_tensor_experiment is not sorry-free.")
  exit(1)
else:
  print("Proof of liquid_tensor_experiment is sorry-free.")
