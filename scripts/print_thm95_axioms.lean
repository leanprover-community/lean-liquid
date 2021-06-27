import system.io
import thm95

-- Surround with unique tokens to be robust against anything in the import that may product output.
#print "BEGIN_THM95_AXIOMS"
#print axioms thm95''
#print "END_THM95_AXIOMS"

meta def main : io unit := pure ()
