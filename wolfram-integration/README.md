# Wolfram integration

This directory holds the implementation of the interface between Isabelle and the Wolfram engine.

- isabelle_to_wolfram implements a translation procedure from AExp objects to Wolfram expressions.
- parse_wolfram and lex_wolfram are self-explanatory - they work in conjunction to parse output from the Wolfram engine into an expression datatype.
- wolfram_to_isabelle translates Wolfram expression objects into AExps.
