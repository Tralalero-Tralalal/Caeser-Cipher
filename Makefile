.PHONY: all 

# Define the Coq source file
COQ_FILE = encrypt.v

# Define the main OCaml executable name
OCAML_EXE = main.native

# Define the expected OCaml output file from Coq extraction
# Coq usually extracts .ml and .mli files based on the Coq file name
# For 'encrypt.v', it likely generates 'Encrypt.ml' and 'Encrypt.mli'
# And it will also extract 'Datatypes.ml' and 'Datatypes.mli' from Coq's standard library.
# We need to explicitly list these extracted files as dependencies for our OCaml build.
EXTRACTED_OCAML_FILES = Encrypt.ml Encrypt.mli Datatypes.ml Datatypes.mli

OCAML_SOURCE_FILES = main.ml

all: $(OCAML_EXE)

# Rule to compile the OCaml executable
# It depends on the Coq extraction being done first, and your OCaml source files.
$(OCAML_EXE): $(EXTRACTED_OCAML_FILES) $(OCAML_SOURCE_FILES)
	ocamlbuild $(OCAML_EXE)

# Rule to perform Coq extraction
# This implicitly creates Encrypt.ml, Encrypt.mli, Datatypes.ml, Datatypes.mli etc.
# Note: coqc doesn't have a direct "output" parameter like that.
# It generates files in the current directory or a specified output directory.
$(EXTRACTED_OCAML_FILES): $(COQ_FILE)
	coqc $(COQ_FILE)

