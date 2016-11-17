#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <bauer.h>

int main(){

bool result = false;

/*Check system 1*/
double system1[10] = {1.0,-1.0,1.0,-1.0,1.0,-1.0,1.0,-1.0,1.0,-1.0};
result = check_exhaustively_limit_cycle(system1,10);
assert( result == true);

}
