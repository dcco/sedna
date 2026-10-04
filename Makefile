
# makefile commands

runtime: _runtime/runtime.o

build: _build/install/default/bin/sedna

test: FORCE
	dune runtest

run: main.exe

help: _build/install/default/bin/sedna
	_build/install/default/bin/sedna -help

# build targets

main.exe: FORCE
	dune exec -- sedna "workspace/$(dir)" -l "workspace/_lib" -w -r _runtime

_build/install/default/bin/sedna: FORCE
	dune build

_runtime/runtime.o: FORCE
	cd _runtime; make

FORCE: ;