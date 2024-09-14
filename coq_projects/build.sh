# Build projects using Coq 8.10
opam switch set palm8.10 && eval $(opam env)
make v10

# Build projects using Coq 8.11
opam switch set palm8.11 && eval $(opam env)
make v11

# Build projects using Coq 8.12
opam switch set palm8.12 && eval $(opam env)
make v12