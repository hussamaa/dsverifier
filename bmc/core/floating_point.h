/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Hussama Ismail <hussamaismail@gmail.com>
 *                Iury Bessa     <iury.bessa@gmail.com>
 *                Renato Abreu   <renatobabreu@yahoo.com.br>
 *                Felipe Monteiro <felipemonteiro@ufam.edu.br>
 *
 * Contributors: Lennon Chaves <lennon.correach@gmail.com>
 *
 * ------------------------------------------------------
 *
 * brief This file contains the common definitions and declarations of the
 * floating-point arithmetic library.
 *
 * ------------------------------------------------------
 */
#ifndef DSVERIFIER_CORE_FLOATING_POINT_H
#define DSVERIFIER_CORE_FLOATING_POINT_H

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

extern implementation impl;

typedef float fp_t;

/** some useful floating-point constants definitions */
fp_t _fp_one;
fp_t _fp_half;
fp_t _fp_minus_one;
fp_t _fp_min;
fp_t _fp_max;

/** fractional part bit mask */
fp_t _fp_fmask;

/** integer part bit mask */
fp_t _fp_imask;

/**
 * Get integer part of fp number.
 * The output has the same signal as the input.
 * @param [in] number in fp format to extract integer from
 * @return fp number consisting of integer part of [in].
 */
fp_t fp_get_int_part(fp_t in)
{
  // If the value of the integral part cannot be represented
  // by the integer type, the behavior is undefined.
  int temp = (int) in;
  return (fp_t) temp;
}

/**
 * Helper function to check and apply quantization effects.
 * @param aquant
 * @return quantized value
 */
fp_t fp_quantize(fp_t aquant)
{
  if(set_overflow_mode == SATURATE)
  {
    if(aquant < _fp_min)
    {
      return _fp_min;
    }
    else if(aquant > _fp_max)
    {
      return _fp_max;
    }
  }
  else if(set_overflow_mode == WRAPAROUND)
  {
    if(aquant < _fp_min || aquant > _fp_max)
    {
      return wrap(aquant, _fp_min, _fp_max);
    }
  }
  return (fp_t) aquant;
}

void fp_verify_overflow(fp_t value)
{
  fp_quantize(value);
  printf("An Overflow Occurred in system's output");
  __DSVERIFIER_assert(value <= _fp_max && value >= _fp_min);
}

void fp_verify_overflow_node(fp_t value, char* msg)
{
  if(OVERFLOW_MODE == SATURATE)
  {
    printf("%s", msg);
    __DSVERIFIER_assert(value <= _fp_max && value >= _fp_min);
  }
}

void fp_verify_overflow_array(fp_t array[], int n)
{
  int i = 0;
  for(i = 0; i < n; i++)
  {
    fp_verify_overflow(array[i]);
  }
}

/**
 * Converts a signed int to fp representation
 * @param [a] number in 16 bits signed int format
 * @return number in fp_t signed representation
 */
fp_t fp_int_to_fp(int in)
{
  return (fp_t) in;
}

/**
 * Converts a number in fp representation to int32_t.
 * @param [a] number in fp representation
 * @return integer in int32_t format
 */
int fp_to_int(fp_t fp)
{
  return (int) fp;
}

fp_t fp_double_to_fp(double value)
{
  return (fp_t) value;
}

/**
 * Typcast an array of double to floating-point
 * @param f[] double array
 * @param r[] floating-point array
 * @param N number of elements
 * @return void
 */
void fp_double_to_fp_array(double f[], fp_t r[], int N)
{
  int i;
  for(i = 0; i < N; ++i)
  {
    r[i] = fp_double_to_fp(f[i]);
  }
}

/**
 * Typcast floating-point to double
 * @param fp floating-point input
 * @return fp converted into double
 */
double fp_to_double(fp_t fp)
{
  return (double) fp;
}

/**
 * Typcast an array of floating-point to double
 * @param f[] double array
 * @param r[] floating-point array
 * @param N number of elements
 * @return void
 */
void fp_to_double_array(double f[], fp_t r[], int N)
{
  int i;
  for(i = 0; i < N; ++i)
  {
    f[i] = fp_to_double(r[i]);
  }
}

/**
 * Floating-point absolute value
 * @param [a] floating-point input
 * @return absolute value of a
 */
fp_t fp_abs(fp_t a)
{
  fp_t tmp;
  tmp = ((a < 0) ? -(fp_t) (a) : a);
  tmp = fp_quantize(tmp);
  return tmp;
}

/**
 * Floating-point addition out = a + b
 * @param [aadd] floating-point input
 * @param [badd] floating-point input
 * @return result of summing the inputs
 */
fp_t fp_add(fp_t aadd, fp_t badd)
{
  fp_t tmpadd;
  tmpadd = aadd + badd;
  tmpadd = fp_quantize(tmpadd);
  return tmpadd;
}

/**
 * Floating-point subtraction out = a - b
 * @param [asub] floating-point input
 * @param [bsub] floating-point input
 * @return result of subtracting the inputs
 */
fp_t fp_sub(fp_t asub, fp_t bsub)
{
  fp_t tmpsub;
  tmpsub = asub - bsub;
  tmpsub = fp_quantize(tmpsub);
  return tmpsub;
}

/**
 * Floating-point multiplication out = a * b
 * @param [amult] floating-point input
 * @param [bmult] floating-point input
 * @return product result out
 */
fp_t fp_mult(fp_t amult, fp_t bmult)
{
  fp_t tmpmult;
  tmpmult = amult * bmult;
  tmpmult = fp_quantize(tmpmult);
  return tmpmult;
}

/**
 * Floating-point division out = a / b
 * @param [amult] floating-point input
 * @param [bmult] floating-point input
 * @return div result out
 */
fp_t fp_div(fp_t a, fp_t b)
{
  __DSVERIFIER_assert(b != 0);
  fp_t tmpdiv = a / b;
  tmpdiv = fp_quantize(tmpdiv);
  return tmpdiv;
}

/**
 * Floating-point negate
 * @param [aneg] floating-point input
 * @return -a;
 */
fp_t fp_neg(fp_t aneg)
{
  fp_t tmpneg;
  tmpneg = -(fp_t) (aneg);
  tmpneg = fp_quantize(tmpneg);
  return tmpneg;
}

/**
 * Floating-point sign.
 * It returns -1 for a <  0
 *             1 for a >=  0
 * @param [a] floating-point input
 * @return signal of a in fixed point format
 */
fp_t fp_sign(fp_t a)
{
  return ((a == 0) ? 0 : ((a < 0) ? _fp_minus_one : _fp_one));
}

/**
 * Floating-point logical right shift
 * @param [a] floating-point parameter
 * @param [shift] number of shifts
 * @return logical right shift a, "shift" bits to the right
 */
fp_t fp_shrl(fp_t in, int shift)
{
  return (fp_t) (((unsigned int) in) >> shift);
}

/**
 * Floating-point square.
 * @param [a] fixed point parameter
 * @return the square of a
 */
fp_t fp_square(fp_t a)
{
  return fp_mult(a, a);
}

void fp_print_int(fp_t a)
{
  printf("\n%i", (int32_t) a);
}

void fp_print_float(fp_t a)
{
  printf("\n%f", a);
}

void fp_print_float_array(fp_t a[], int N)
{
  int i;
  for(i = 0; i < N; ++i)
  {
    printf("\n%f", a[i]);
  }
}

/* print array elements */
void print_fp_array_elements(char * name, fp_t * v, int n)
{
  printf("%s = {", name);
  int i;
  for(i = 0; i < n; i++)
  {
    printf(" %f ", v[i]);
  }
  printf("}\n");
}
#endif // DSVERIFIER_CORE_FLOATING_POINT_H
