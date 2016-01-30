# DSVerifier (Digital-Systems Verifier)

DSVerifier is a verification tool for digital systems.
In particular, DSVerifier employs the bounded model checking (BMC) technique
based on satisfiability modulo theories (SMT) and boolean satisfiability (SAT),
which allows engineers to verify the occurrence of design errors,
due to the finite word-length (FWL) effects employed in fixed-point digital filters
and controllers.

Supported properties:

###### For Digital-Systems:
  * Overflow
  * Limit Cycle
  * Timing
  * Error
  * Stability
  * Minimum Phase

###### For Digital-Systems in Closed-loop:
  * Stability in Closed-loop
  * Limit Cycle in Closed-loop
  * Quantization Error in Closed-loop

http://www.dsverifier.org

http://esbmc.org/dsverifier

## Configuration

Firstly, before to use the DSVerifier is necessary to
configure an environment variable called DSVERIFIER_HOME. So, add to the .bashrc file on your computer the following:

./export DSVERIFIER_HOME='path to dsverifier folder'

Save it, and then use the following command:

./$ source .bashrc

Secondly, you have to download the desired version of CBMC, or ESBMC
executable for DSVerifier. This package contain the CBMC v5.2 and ESBMC v2.1.0

Please, put it into: $DSVERIFIER_HOME/model-checker

The recommended versions for DSVerifier v2.0 are:

ESBMC v2.1.0: http://esbmc.org/binaries/esbmc-v2.1.0-linux-static-64.tgz

CBMC v5.2: http://www.cprover.org/cbmc/download/cbmc-5-2-linux-64.tgz

## Command line mode

###### Verification of Digital-Systems *

  It is necessary to generate a verification file using the following format:

  ```c
  #include <dsverifier.h>

  digital_system ds = {
    .a = { 1.0, 1.068, 0.1239 },
    .a_size = 3,
    .b = { 2.813, -0.0163, -1.872 },
    .b_size = 3
  };

  implementation impl = {
    .int_bits = 4,
    .frac_bits = 10,
    .min = -5.0,
    .max = 5.0
  };
  ```

  Execution:

      ./dsverifier ds.c --realization <r> --property <j> --x-size <k>

  where <file> is the digital-system specification file, <r> is the chosen
  realization, <j> is the property to be verified, and <k> is the verification
  bound.

  Properties: OVERFLOW, LIMIT_CYCLE, ZERO_INPUT_LIMIT_CYCLE, TIMING, ERROR,
              STABILITY, and MINIMUM_PHASE.

  Realizations: DFI, DFII, TDFII, DDFI, DDFII, and TDDFII.

###### Verification of Digital-Systems in Closed-loop

  It is necessary to generate a verification file using the following format:

  ```c
  #include <dsverifier.h>

  digital_system plant = {
    .b = { 0.00018604, 0.000172886972 },
    .b_uncertainty = { 5, 5 },
    .b_size = 2,
    .a = { 1.0,-1.7989, 0.80248974 },
    .a_uncertainty = { 5, 5, 5 },
    .a_size = 3
  };

  digital_system controller = {
    .b = { 1.422, -1.1360358, -1.41689538972, 1.14114041028 },
    .b_size = 4,
    .a = { 1.0, -1.0307, -0.861428, 0.892128 },
    .a_size = 4
  };

  implementation impl = {
    .int_bits = 16,
    .frac_bits = 12,
    .min = -1.0,
    .max = 1.0,
    .max_error = 5
  };
  ```

  Execution:

      ./dsverifier <file> --connection-mode <cm> --property <j>
                          --realization <r> --x-size <k> --bmc CBMC

  where <file> is the digital-system specification file, <cm> is the chosen
  connection-mode, <j> is the property to be verified, <r> is the desired
  realization, and <k> is the verification bound.

  Properties: STABILITY_CLOSED_LOOP, LIMIT_CYCLE_CLOSED_LOOP,
              and QUANTIZATION_ERROR_CLOSED_LOOP

  Realizations: DFI, DFII, and TDFII.

## Graphical User Interface

To use DSVerifier GUI, is necessary to have at least Java Runtime Environment
Version 8.0 Update 40 (jre1.8.0_40)

Execution:

     java -jar dsverifier-gui.jar
