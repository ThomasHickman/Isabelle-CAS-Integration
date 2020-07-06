import os
import re
import sys
from pprint import pprint

ignored_sodes = 0
num_found = 0

sodes = set()
for root, _, files in os.walk("/put/the/path/to/keymaera/examples/here"):
    for file_name in files:
        file_path = os.path.join(root, file_name)
        if file_path.endswith(".key"):
            try:
                with open(file_path) as fp:
                    for line in fp.readlines():
                        for bracketed in re.findall(r"\{[^}]+\}", line):
                            num_found += 1
                            #print(bracketed)
                            ode_vars = []
                            ode_eqs = []
                            ode_strs = re.findall(
                                r"[a-z0-9]+['`]\ *=\ *.+?[,}]",
                                bracketed,
                                re.IGNORECASE
                            )

                            if ode_strs == []:
                                print("Failed to parse ode:" + bracketed, file=sys.stderr) # TODO: look into these cases
                            else:
                                for ode_str in ode_strs:
                                    parts = re.match(r"([a-z0-9]+)['`]\ *=\ *(.+?)[,}&]", ode_str, re.IGNORECASE)

                                    ode_vars.append(parts.group(1))
                                    ode_eqs.append(parts.group(2))

                                
                                #"(λ (t::real) (x, y). (t, x))"
                                # NOTE: the independent variable is not accessed by name is KeYmaera. If
                                # needed, it is obtained by t' = 1 (to make t the independent
                                # variable).
                                conv_str = f"(λ ind ({', '.join(ode_vars)}). ({', '.join(ode_eqs)}))"
                                if False and all((re.match(r"^(-?([a-z0-9]+|([0-9](\.[0-9])?)+))$", ode_eq, re.IGNORECASE) is not None
                                        for ode_eq in ode_eqs)):
                                    print("Ignoring: " + conv_str, file=sys.stderr)
                                    ignored_sodes += 1
                                else:
                                    print("Adding: " + conv_str + "from: " + line)
                                    sodes.add("ode_solve_thm \"" + conv_str + "\"")

            except:
                print("Error in :" + file_path)
                raise

print("Found: " + str(num_found), file=sys.stderr)
print("Generated: " + str(len(sodes)), file=sys.stderr)
print("Ignored: " + str(ignored_sodes), file=sys.stderr)
print("\n".join(sodes))