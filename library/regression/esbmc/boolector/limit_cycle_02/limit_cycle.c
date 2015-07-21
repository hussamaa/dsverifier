#include <stdio.h>
#include <assert.h>

int main(){

	double y[11] = { 0.5, 1.0, 0.5, 1.1, 0.0, 1.0, 0.5, -0.5, 0.5, -0.5, 1.0 }; /* limit cycle window == 2 */
	//double y[10] = { 4.0, 3.0, 2.0, 1.0, 0.5, 1.0, -0.5, 0.5, 1.0, -0.5 }; /* limit cycle window == 3 */
	//double y[6] = { 1.0, 1.0, 1.0, 1.0, 1.0, 1.0 }; /* limit cycle window == 2 */
	int x_size = 11;
	int i, j;


	int window_timer = 0;
	int window_count = 0; 
	double previous = -1;
	for (i = 2; i < x_size/2; i++){
		int window_size = i;
		for(j=0; j<x_size; j++){ 
			if (window_timer > window_size){
				window_timer = 0;
				window_count = 0;
			}
			/* check bound of outputs */
			int window_index = j + window_size;
		    if (window_index < x_size){
				/* check if window occurr */ 
				if (y[j] == y[window_index] && (y[j] != y[j+1])){
					window_count++;
					// printf("aconteceu uma repetição entre y[%d] = %.3f e y[%d] = %.3f\n", i, y[i], i+window_size, y[i+window_size]);
					// printf("window count: %d\n", window_count);
					/* window_count == window_size (the repeats occurs) */
					if (window_count == window_size){
						printf("ciclo limite com janela: %d\n", window_size);
						assert(0);
					}
					assert(!(window_count == window_size));
				}
			}else{
				break;
			}
			window_timer++;
		}
	}
}
