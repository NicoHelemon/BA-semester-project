#!/bin/sh

files="RbarComp.v SetTheory.v FunImage.v InfSup.v Definitions.v Seq.v Main.v Packetizer.v Scheduler.v Examples.v"

cd ~/Documents/semester-project/
pwd
eval $(opam env)
coqc -R src "" ${files}
coqdoc -d doc/ -q --plain-comments -utf8 -l -toc --no-lib-name ${files}
coqide
