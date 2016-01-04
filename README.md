# DSVerifier (Digital System Verifier)

DSVerifier is a verification tool developed for digital systems. In particular, DSVerifier employs the bounded model checking technique based on satisfiability modulo theories (SMT) solvers, which allows engineers to verify the occurrence of design errors, due to the finite word-length approach employed in fixed-point digital filters and controllers.

Property Supported:

* Overflow
* Limit Cycle
* Timing
* Error
* Stability
* Minimum Phase

Required Libraries:

For Ubuntu x86-64:
* apt-get install libc6-dev-i386

Quickly Configuration:

make
export DSVERIFIER_HOME=$(pwd)
export PATH=$PATH:$DSVERIFIER_HOME

DSVerifier is developed at the Federal University of Amazonas (UFAM). This project is supported by Samsung, CNPq, and FAPEAM grants.

http://www.dsverifier.org
