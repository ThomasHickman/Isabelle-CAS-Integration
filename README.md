# Isabelle-CAS-Integration

Developed from the dissertations of Thomas Hickman and Christian Pardillo Laursen.

## Steps for installation
 - Install [Isabelle 2020](https://isabelle.in.tum.de). Earlier versions are not supported.

 - Add the [Ordinary_Differential_Equations](https://www.isa-afp.org/entries/Ordinary_Differential_Equations.html) entry to your Isabelle ROOTS - follow [these](https://www.isa-afp.org/using.html) instructions.

 - Download and activate the [Wolfram Engine](https://www.wolfram.com/engine/). WolframScript is installed with it, and is called from bash.

 OR

 - Install [SageMath](https://www.sagemath.org/download.html) and optionally [FriCAS](http://fricas.sourceforge.net/).

 - Add the file `config.sml` configures the path of the file `sage-integration/ConvertToIsabelle.py`. An example of this file is found in `config-example.sml`.

 - Finally, launch Isabelle/jEdit with the ODE theory loading, to avoid
recompiling. This can be done with the command
``isabelle jedit -d ~/AFP/thys -l Ordinary_Differential_Equations``,
replacing the path to the AFP with wherever it is downloaded.

## Usage

Examples can be found in the two test sets: `Keymaera_tests.thy` and `TestSet.thy`.
