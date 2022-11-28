# AU Compilation student project template

This folder includes a VSCode .devcontainer configuration. The installation
steps are dependent on whether you are using the Docker VSCode integration
or not. 


## Installation steps for use with the Docker/VSCode integration (recommended)

1. Make sure Docker is installed and running.
2. Make sure VSCode Remote Develpoment extension is installed.
3. Open this folder in VSCode and choose "reopen in container" in the dialogue.
   - In case you forgot to click "reopen in container", you can also do this by
     activating VSCode's command palette (View -> Command Palette or F1) and
     then typing "Reopen in container".
4. Proceed to section on running the compiler below.

## Installation for use without the Docker integration

1. Make sure `opam` is installed.
2. Install all dependencies by running `make deps`


## Running the compiler
1. Compile the skeleton compiler by running `make`
2. Compile the test tool by  running `make compile-test-tool`
3. Run the tests by running `make test`


## Accessing generated html files from outside the Docker container

At various points in the development, the compiler project generates .html files
that one may want to check out. Because the `_build` directory is not mapped to the 
host operating system, we use a simple python http server for serving the content
of that file. VSCode provides the port forwarding. See `http-server` target in 
the Makefile.

## Using custom utop

Run `make utop` to start a custom ocaml utop that loads the libraries defined
in this directory. Note that we pass a custom .ocamlinit file that additionally
open the Tigerc_lib module -- this makes the various custom modules, e.g.,
Symbol, immediately accussible through the utop.


## Notes on usage

We use opam and dune package managers. See their respective home pages for more
information. The Makefile also contains an option for reporting missing
dependencies and clearing the source tree.
