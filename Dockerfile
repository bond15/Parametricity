FROM coqorg/coq:8.19.2-ocaml-4.14.2-flambda
#FROM alpine:3.21

USER root

RUN sudo apt-get update
#RUN sudo apt-get install opam

# "this is necessary, unless you run a privileged Docker container."
# source :https://rocq-prover.org/docs/installing-rocq

#run all of these in the container shell

#RUN opam init --disable-sandboxing -y
#RUN eval $(opam env)


#RUN opam pin add coq 8.19.2 -y
#RUN opam install vscoq-language-server -y