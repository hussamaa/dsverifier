#include <stdio.h>
#include <stdlib.h>

/** function to limit cycles exhaustively*/
bool check_exhaustively_limit_cycle(fxp_t y[]	, int y_size){
	int window_timer = 0;
	int window_count = 0;
	int i, j;
	for (i = 2; i < y_size; i++){
		int window_size = i;
		for(j=0; j<y_size; j++){
			if (window_timer > window_size){
				window_timer = 0;
				window_count = 0;
			}
			/* check bound of outputs */
			int window_index = j + window_size;
			if (window_index < y_size){
				/* check if window occurr */
				if (y[j] == y[window_index]){
					window_count++;
				}
			}else{
				break;
			}
			window_timer++;
		}
	}

return true;
}
