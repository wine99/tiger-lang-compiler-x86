.PHONY: default test deps clean report-missing-deps
BUILD=dune build

# Compile the main compiler natively
native:
	$(BUILD) _build/install/default/bin/tigerc


# Compiles just the test tool. The test tool generally 
# needs to be compiled once per phase
compile-test-tool:
	$(BUILD) _build/install/default/bin/runtests 


# Runs the test tool in default configuration. 
# To customize which tests are invoked, use the test
# tool directly; Check out the arguments through by running
# it with --help option; Some usage is also described in 
# the course document
test:
	_build/install/default/bin/runtests


# Wait continuously for file changes and recompile
watch:
	$(BUILD) --watch



# Compile all the tools in the workspace.
# This includes the compiler, the test tool, and 
# additional utilities that may be placed here.
all:
	$(BUILD)


# Start a simple http server on port 8000 for serving files 
# generated in the build director. Change the port number
# and the path tho the forwarded directory, if desired
# 
# Observe that the output of the server is suppressed; to 
# make it visible comment out pipe redirect, that is the part 
# after ">" symbol in the command
http-server:
	python3 -m http.server 8000 --directory _build/ > /dev/null 2>&1

# Wipe out the _build directory; note that because 
# of how we mount the _build directory in the container 
# this may result in an error
clean:
	dune clean

# clean generated LLVM files
ll-clean:
	rm -f _build/ll/*.ll 
	rm -f _build/ll/*.out	

# Launch utop initialized with the project files
utop:
	dune utop . -- -init=./.ocamlinit
	
# Create an archive of the current compiler; 
zip-compiler:
	(cd src; zip -FSr ../compiler.zip compiler)

# -------------------------------------------------------- #
# These are internal targets, typcially used for the       #
# configuration, custom installation or troubleshooting    #
# -------------------------------------------------------- #

# Compiles the main compiler into ocaml bytecode
# -- we generally do not use this 
bytecode:
	$(BUILD) _build/install/default/bin/tigerc.bc

# Install dependencies; typically already done as 
# part of the docker configuration; but needed 
# for custom installs
deps:
	opam install .  --deps-only --locked

# Report missing dependencies; should be used only in 
# custom installs and at the time of docker configuration
report-missing-deps:
	dune external-lib-deps @install --missing

# Lock packages; use only in the configuration
lock-packages:
	opam lock ./tiger.opam

