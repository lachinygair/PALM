# create a switch for projects using 8.10
opam switch create palm8.10 4.08.1+flambda && eval $(opam env)
opam pin add coq 8.10.0 -y
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hammer coq-serapi coq-mathcomp-ssreflect=1.9.0 coq-int-map=8.10.0 -y

# create a switch for projects using 8.11
opam switch create palm8.11 4.08.1+flambda && eval $(opam env)
opam pin add coq 8.11.0 -y
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hammer coq-serapi coq-mathcomp-ssreflect=1.10.0 coq-hydra-battles=0.4 coq-fcsl-pcm=1.2.0 coq-coqprime=1.0.5 coq-equations=1.2.4+8.11 coq-bignums=8.11.dev coq-pocklington -y

# create a switch for projects using 8.12
opam switch create palm8.12 4.08.1+flambda && eval $(opam env)
opam pin add coq 8.12.1 -y
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hammer coq-serapi coq-fcsl-pcm=1.3.0 coq-equations=1.2.3+8.12 coq-mathcomp-ssreflect=1.11.0 coq-metacoq-template=1.0~beta2+8.12 coq-smpl=8.12.0.1 -y