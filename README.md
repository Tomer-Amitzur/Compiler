The compiler is written in Ocaml language, and compiles scheme code to assembly code.
the project contains:

-the compiler pipeline:
-reader
  -tag-parser
  -semantic-analysis
  -code-generation
  -compiler.ml - which combines the four parts of the compilation pipeline.

-implimentation of additional libary functions:
  -prims.s - an assembly file containing implementations of many of the low-level standard library procedures.
  -stdlib.scm - a Scheme file containing implementations of many of the high-level standard library procedures.
  
 
           

