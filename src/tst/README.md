# dOvs student grading tool 

## Usage 

The tool can be invoked by running either `_build/install/default/bin/runtests` 
`make test` in the compiler project home directory.

The call to the compiler takes place via ./tigerc.sh shell script that invokes
the compiler and also redirects the stderr to stdout. It may be nice in the
future to avoid having to have a wrapper shell script. 

**OBS**: Because the path to the shell script is hardcoded it is imperative this
program is executed from the main project directory. 

## Test naming convention

Every Tiger test case is associated with a set of expected output files -- one
for each phase. The naming convention is such that we associate `file.tig` with the
following expected-files.

- `file.tig.expected-lex`
- `file.tig.expected-par`
- `file.tig.expected-sem`
- `file.tig.expected-out`

If the corresponding expected-file does not exist it is created upon the first
invocation of the test. This is the standard "golden testing". Note that when
comparing the results of the compiler, we also distinguish between positive and
negative tests and additionally check for the exit codes.

## Overwriting the expected files

Use flag `--overwrite-expected`. Beware the tool provides no textual feedback
when overwriting the files. Overwritten tests are automatically successful.

## Filtering options

There are three ways to filter tests


### Filtering by group name 

Use Alcotest's built-in _test_ feature that takes a string for matching 
a test group, e.g., `_build/install/default/bin/runtests test Lexer`

### Filtering by file name

Use flag `--only` to filter tests by file, e.g., `_build/install/default/bin/runtests --only zero`

### By feature set

Use flag `--fs` to filter tests by the feature sets, e.g., `_build/install/default/bin/runtests --fs "^#llvm0$"` that runs tests where the extent of the test case is strictly restricted to the LLVM0 feature set. This flag internally OCaml's standard Str module for regular expressions, so see 
the module documentation for the information on the regular expression syntax <https://caml.inria.fr/pub/docs/manual-ocaml/libref/Str.html>


## Infrastructure/Alcotest

Our implementation uses Alcotest unit test library that does all the heavy
lifting wrt logging/error reporting. Using a unit test library for the
"end-to-end" testing feels a bit of a hack, but so far it has been rather
unproblematic. 

Alcotest API: https://docs.mirage.io/alcotest/Alcotest/index.html.
