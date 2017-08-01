/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *                Iury Bessa     <iury.bessa@gmail.com>
 *                Renato Abreu   <renatobabreu@yahoo.com.br>
 *
 * ------------------------------------------------------
 *
 * compatibility functions
 *
 * ------------------------------------------------------
 */
#ifndef DSVERIFIER_CORE_COMPATIBILITY_H
#define DSVERIFIER_CORE_COMPATIBILITY_H

#include <stdlib.h>
#include <assert.h>
#include <stdio.h>

// these definitions are common to the verifiers
// that participate in SV-COMP
void __VERIFIER_assume(int expression)
{
  if (!expression)
  {
    LOOP: goto LOOP;
  };
  return;
}

void __VERIFIER_assert(int cond)
{
  assert(cond);
}

void __DSVERIFIER_assume(int expression)
{
#if(BMC == ESBMC || BMC == CBMC)
  __VERIFIER_assume(expression);
#else
  printf("");
  printf("*********************");
  printf("* BMC NOT SUPPORTED *");
  printf("*********************");
  assert(0);
#endif
}

void __DSVERIFIER_assert(int expression)
{
  __VERIFIER_assert(expression);
}

void __DSVERIFIER_assert_msg(int expression, char msg[])
{
  printf("%s", msg);
  __VERIFIER_assert(expression);
}
#endif // DSVERIFIER_CORE_COMPATIBILITY_H
