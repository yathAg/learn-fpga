#include <femtorv32.h>

/* print_dec, print_hex taken from picorv32 */

void print_dec(int val) {
   char buffer[255];
   char *p = buffer;
   if(val < 0) {
      put_char('-');
      print_dec(-val);
      return;
   }
   while (val || p == buffer) {
      *(p++) = val % 10;
      val = val / 10;
   }
   while (p != buffer) {
      put_char('0' + *(--p));
   }
}

void print_hex(unsigned int val) {
   print_hex_digits(val, 8);
}

void print_hex_digits(unsigned int val, int nbdigits) {
   for (int i = (4*nbdigits)-4; i >= 0; i -= 4) {
      put_char("0123456789ABCDEF"[(val >> i) % 16]);
   }
}

