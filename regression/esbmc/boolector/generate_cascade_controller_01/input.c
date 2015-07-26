#include<stdio.h>
#include<stdlib.h>
#include<verificationfxp.h>
#include<assert.h>

digital_system ds = {
        .a = { 1.0000, 9.1122, -2.2473, -8.6564, 0.6569, 0.1355 },
        .a_size = 6,
	.b = { 0.0937,-0.3582, 0.5201, -0.3482, 0.1003, -0.0078 },
	.b_size = 6
};

implementation impl = {
        .int_bits = 3,
        .frac_bits = 13,
	.delta = 0.25
};

int main(){  

   double a_cascade[100];
   int a_cascade_size;
   double b_cascade[100];
   int b_cascade_size;

    __DSVERIFIER_generate_cascade_controllers(&ds, a_cascade, a_cascade_size, b_cascade, b_cascade_size);

   assert(a_cascade_size = 9);
   assert(b_cascade_size = 9);

   assert(a_cascade[0] == 0l);
   assert(a_cascade[1] == 1l);
   assert(a_cascade[2] == 9.2531563374213874340057373046875l);
   assert(a_cascade[3] == 1l);
   assert(a_cascade[4] == -0.0676432219333946704864501953125l);
   assert(a_cascade[5] == -0.93226042226888239383697509765625l);
   assert(a_cascade[6] == 1l);
   assert(a_cascade[7] == -0.07331311539746820926666259765625l);
   assert(a_cascade[8] == -0.01570768351666629314422607421875l);

   assert(b_cascade[0] == 0l);
   assert(b_cascade[1] == 1l);
   assert(b_cascade[2] == -1.1406899630092084407806396484375l);
   assert(b_cascade[3] == 1l);
   assert(b_cascade[4] == -0.78469419269822537899017333984375l);
   assert(b_cascade[5] == 0.0790459210984408855438232421875l);
   assert(b_cascade[6] == 1l);
   assert(b_cascade[7] == -1.8974546971730887889862060546875l);
   assert(b_cascade[8] == 0.9232257879339158535003662109375l);

}
