./clean.sh

eval $(opam env)

coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile install
make -f CoqMakefile