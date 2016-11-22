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
 * sine aproximation by taylor series (Good aproximation, but not too fast computationally)
 */
double sin(double x,double precision=3)
{
    double sine = x;
    bool signal_flag = true;

    for (double i=3;i<=n;i+=2)
    {
        if(signal_flag)
        {
            sine -= pow(x,i)/factorial(i);
            signal_flag = false;
        }
        else
        {
            sine += pow(x,i)/factorial(i);
            signal_flag = true;
        }
    }
    return sine;
}



/**
 * cossine aproximation by taylor series (Good aproximation, but not too fast computationally)
 */
double cos(double x,double precision=3)
{
    double sine = x;
    bool signal_flag = true;

    for (double i=2;i<=n;i+=2)
    {
        if(signal_flag)
        {
            sine -= pow(x,i)/factorial(i);
            signal_flag = false;
        }
        else
        {
            sine += pow(x,i)/factorial(i);
            signal_flag = true;
        }
    }
    return sine;
}








}



