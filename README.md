# Compiler

The compiler is written in Ocaml language, and compiles Scheme code to Assembly code.
the project contains the compiler pipeline (reader, tag-parser, semantic-analysis, code-generation)
and the file compiler.ml - which combines the four parts of the compilation pipeline.
moreover, it contains 2 implimentations of additional libary functions (prims.s, stdlib.scm)

## Run:

### Linux:

put your scm file insidse the directory and run:

```bash
make -f ./Makefile your-file-name
```


  
 
           

