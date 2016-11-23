/**
 * DSVerifier - Digital Systems Verifier
 *
 * Federal University of Amazonas - UFAM
 *
 * Authors:       Daniel Mello <dani-dmello@hotmail.com>
 *                
 * ------------------------------------------------------
 *
 * Common functions needed for digital filters and frequency domain operations
 *
 * ------------------------------------------------------
 */


/**
 * Sine aproximation by taylor series (max 4 terms). 
 * Algorithm created aiming to avoid state explosion due to loops and recursion.  
 */
double sin(double x, double precision){
    double sine;
    double xsquared = x*x;
    double aux;

    if (precision >= 0){
        aux = 0;
        sine = aux;

         if (precision >= 1){
            aux = x; 
            sine += aux; 

            if (precision >= 2){
                aux = aux*xsquared; 
                sine -= aux/6;
            
                if (precision >= 3){
                    aux = aux*xsquared
                    sine +=aux/120
                
                    if(precision >=4){
                        aux = aux*xsquared
                        sine -=aux/5040
                    }
                }
            }
        }
    }
    return sine;
}


/**
 * Cosine aproximation by taylor series (max 4 terms). 
 * Algorithm created aiming to avoid state explosion due to loops and recursion.  
 */
double cos(double x, double precision){
    double cosine;
    double xsquared = x*x;
    double aux;

    if (precision >= 0){
        aux = 0;
        sine = aux;

         if (precision >= 1){
            aux = 1; 
            cosine = 1; 

            if (precision >= 2){
                aux = xsquared; 
                cosine -= aux/2; 
            
                if (precision >= 3){
                    aux = aux*xsquared; 
                    sine += aux/24;
                
                    if(precision >=4){
                        aux = aux*xsquared
                        sine -=aux/720
                    }
                }
            }
        }
    }
    return cosine;
}



/**
 * square root aproximation (80% faster than standard sqrt from math.h, 99.9% precision)
 */
 float  sqrt1(const float x)
{
  const float xhalf = 0.5f*x;
 
  union // get bits for floating value
  {
    float x;
    int i;
  } u;
  u.x = x;
  u.i = 0x5f3759df  - (u.i >> 1);  // gives initial guess y0
  return x*u.x*(1.5f - xhalf*u.x*u.x);// Newton step, repeating increases accuracy 
}  




/**
 * square root aproximation (100% faster than standard sqrt from math.h, 97% precison)
 */
float sqrt2(const float x)  
{
  union
  {
    int i;
    float x;
  } u;

  u.x = x;
  u.i = (1<<29) + (u.i >> 1) - (1<<22); 
  return u.x;
} 



}



