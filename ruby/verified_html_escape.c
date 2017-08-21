#include "ruby.h"

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <nmmintrin.h>

#include <stdbool.h> /* defines bool type */
#define n0_true() true
#define n0_false() false
#define sw_bool(b) (b)
#define case_true_bool default
#define case_false_bool case false

typedef uint64_t nat;
#define n0_O() ((nat)0)
#define n1_S(n) ((n)+1)
#define sw_nat(n) (n)
#define case_O_nat case 0
#define case_S_nat default
#define field0_S_nat(n) ((n)-1)

#define n2_addn(a,b) ((a)+(b))
#define n2_subn(a,b) ((a)-(b))
#define n2_muln(a,b) ((a)*(b))
#define n2_divn(a,b) ((a)/(b))
#define n2_modn(a,b) ((a)%(b))
#define n2_leq(a,b) ((a)<=(b))
#define n2_eqn(a,b) ((a)==(b))

typedef char ascii;

typedef const char *byteptr;
#define n1_bptrget(p) (*(unsigned char *)p)
#define n2_bptradd(p, n) (p + n)

typedef struct {
  VALUE str;
  nat len;
} buffer;

#define buffer_new(n) ((buffer){ rb_str_buf_new(n), 0 })

buffer
n3_bufaddmem(buffer buf, byteptr p, nat n)
{
  if ((nat)RSTRING_LEN(buf.str) == buf.len) {
    rb_str_buf_cat(buf.str, (char *)p, n);
    return (buffer){ buf.str, buf.len + n };
  }
  else {
    rb_bug("buffer used non-linearly");
  }
}

typedef struct {
  byteptr p;
  nat n;
} prod_byteptr_nat;
#define field0_pair_prod_byteptr_nat(pair) ((pair).p)
#define field1_pair_prod_byteptr_nat(pair) ((pair).n)

prod_byteptr_nat html_escape_byte_tbl[256] = {
  { "\x00", 1 }, /* "\x00" */
  { "\x01", 1 }, /* "\x01" */
  { "\x02", 1 }, /* "\x02" */
  { "\x03", 1 }, /* "\x03" */
  { "\x04", 1 }, /* "\x04" */
  { "\x05", 1 }, /* "\x05" */
  { "\x06", 1 }, /* "\x06" */
  { "\x07", 1 }, /* "\a" */
  { "\x08", 1 }, /* "\b" */
  { "\x09", 1 }, /* "\t" */
  { "\x0a", 1 }, /* "\n" */
  { "\x0b", 1 }, /* "\v" */
  { "\x0c", 1 }, /* "\f" */
  { "\x0d", 1 }, /* "\r" */
  { "\x0e", 1 }, /* "\x0E" */
  { "\x0f", 1 }, /* "\x0F" */
  { "\x10", 1 }, /* "\x10" */
  { "\x11", 1 }, /* "\x11" */
  { "\x12", 1 }, /* "\x12" */
  { "\x13", 1 }, /* "\x13" */
  { "\x14", 1 }, /* "\x14" */
  { "\x15", 1 }, /* "\x15" */
  { "\x16", 1 }, /* "\x16" */
  { "\x17", 1 }, /* "\x17" */
  { "\x18", 1 }, /* "\x18" */
  { "\x19", 1 }, /* "\x19" */
  { "\x1a", 1 }, /* "\x1A" */
  { "\x1b", 1 }, /* "\e" */
  { "\x1c", 1 }, /* "\x1C" */
  { "\x1d", 1 }, /* "\x1D" */
  { "\x1e", 1 }, /* "\x1E" */
  { "\x1f", 1 }, /* "\x1F" */
  { "\x20", 1 }, /* " " */
  { "\x21", 1 }, /* "!" */
  { "&quot;", 6 }, /* "\"" */
  { "\x23", 1 }, /* "#" */
  { "\x24", 1 }, /* "$" */
  { "\x25", 1 }, /* "%" */
  { "&amp;", 5 }, /* "&" */
  { "&#39;", 5 }, /* "'" */
  { "\x28", 1 }, /* "(" */
  { "\x29", 1 }, /* ")" */
  { "\x2a", 1 }, /* "*" */
  { "\x2b", 1 }, /* "+" */
  { "\x2c", 1 }, /* "," */
  { "\x2d", 1 }, /* "-" */
  { "\x2e", 1 }, /* "." */
  { "\x2f", 1 }, /* "/" */
  { "\x30", 1 }, /* "0" */
  { "\x31", 1 }, /* "1" */
  { "\x32", 1 }, /* "2" */
  { "\x33", 1 }, /* "3" */
  { "\x34", 1 }, /* "4" */
  { "\x35", 1 }, /* "5" */
  { "\x36", 1 }, /* "6" */
  { "\x37", 1 }, /* "7" */
  { "\x38", 1 }, /* "8" */
  { "\x39", 1 }, /* "9" */
  { "\x3a", 1 }, /* ":" */
  { "\x3b", 1 }, /* ";" */
  { "&lt;", 4 }, /* "<" */
  { "\x3d", 1 }, /* "=" */
  { "&gt;", 4 }, /* ">" */
  { "\x3f", 1 }, /* "?" */
  { "\x40", 1 }, /* "@" */
  { "\x41", 1 }, /* "A" */
  { "\x42", 1 }, /* "B" */
  { "\x43", 1 }, /* "C" */
  { "\x44", 1 }, /* "D" */
  { "\x45", 1 }, /* "E" */
  { "\x46", 1 }, /* "F" */
  { "\x47", 1 }, /* "G" */
  { "\x48", 1 }, /* "H" */
  { "\x49", 1 }, /* "I" */
  { "\x4a", 1 }, /* "J" */
  { "\x4b", 1 }, /* "K" */
  { "\x4c", 1 }, /* "L" */
  { "\x4d", 1 }, /* "M" */
  { "\x4e", 1 }, /* "N" */
  { "\x4f", 1 }, /* "O" */
  { "\x50", 1 }, /* "P" */
  { "\x51", 1 }, /* "Q" */
  { "\x52", 1 }, /* "R" */
  { "\x53", 1 }, /* "S" */
  { "\x54", 1 }, /* "T" */
  { "\x55", 1 }, /* "U" */
  { "\x56", 1 }, /* "V" */
  { "\x57", 1 }, /* "W" */
  { "\x58", 1 }, /* "X" */
  { "\x59", 1 }, /* "Y" */
  { "\x5a", 1 }, /* "Z" */
  { "\x5b", 1 }, /* "[" */
  { "\x5c", 1 }, /* "\\" */
  { "\x5d", 1 }, /* "]" */
  { "\x5e", 1 }, /* "^" */
  { "\x5f", 1 }, /* "_" */
  { "\x60", 1 }, /* "`" */
  { "\x61", 1 }, /* "a" */
  { "\x62", 1 }, /* "b" */
  { "\x63", 1 }, /* "c" */
  { "\x64", 1 }, /* "d" */
  { "\x65", 1 }, /* "e" */
  { "\x66", 1 }, /* "f" */
  { "\x67", 1 }, /* "g" */
  { "\x68", 1 }, /* "h" */
  { "\x69", 1 }, /* "i" */
  { "\x6a", 1 }, /* "j" */
  { "\x6b", 1 }, /* "k" */
  { "\x6c", 1 }, /* "l" */
  { "\x6d", 1 }, /* "m" */
  { "\x6e", 1 }, /* "n" */
  { "\x6f", 1 }, /* "o" */
  { "\x70", 1 }, /* "p" */
  { "\x71", 1 }, /* "q" */
  { "\x72", 1 }, /* "r" */
  { "\x73", 1 }, /* "s" */
  { "\x74", 1 }, /* "t" */
  { "\x75", 1 }, /* "u" */
  { "\x76", 1 }, /* "v" */
  { "\x77", 1 }, /* "w" */
  { "\x78", 1 }, /* "x" */
  { "\x79", 1 }, /* "y" */
  { "\x7a", 1 }, /* "z" */
  { "\x7b", 1 }, /* "{" */
  { "\x7c", 1 }, /* "|" */
  { "\x7d", 1 }, /* "}" */
  { "\x7e", 1 }, /* "~" */
  { "\x7f", 1 }, /* "\x7F" */
  { "\x80", 1 }, /* "\x80" */
  { "\x81", 1 }, /* "\x81" */
  { "\x82", 1 }, /* "\x82" */
  { "\x83", 1 }, /* "\x83" */
  { "\x84", 1 }, /* "\x84" */
  { "\x85", 1 }, /* "\x85" */
  { "\x86", 1 }, /* "\x86" */
  { "\x87", 1 }, /* "\x87" */
  { "\x88", 1 }, /* "\x88" */
  { "\x89", 1 }, /* "\x89" */
  { "\x8a", 1 }, /* "\x8A" */
  { "\x8b", 1 }, /* "\x8B" */
  { "\x8c", 1 }, /* "\x8C" */
  { "\x8d", 1 }, /* "\x8D" */
  { "\x8e", 1 }, /* "\x8E" */
  { "\x8f", 1 }, /* "\x8F" */
  { "\x90", 1 }, /* "\x90" */
  { "\x91", 1 }, /* "\x91" */
  { "\x92", 1 }, /* "\x92" */
  { "\x93", 1 }, /* "\x93" */
  { "\x94", 1 }, /* "\x94" */
  { "\x95", 1 }, /* "\x95" */
  { "\x96", 1 }, /* "\x96" */
  { "\x97", 1 }, /* "\x97" */
  { "\x98", 1 }, /* "\x98" */
  { "\x99", 1 }, /* "\x99" */
  { "\x9a", 1 }, /* "\x9A" */
  { "\x9b", 1 }, /* "\x9B" */
  { "\x9c", 1 }, /* "\x9C" */
  { "\x9d", 1 }, /* "\x9D" */
  { "\x9e", 1 }, /* "\x9E" */
  { "\x9f", 1 }, /* "\x9F" */
  { "\xa0", 1 }, /* "\xA0" */
  { "\xa1", 1 }, /* "\xA1" */
  { "\xa2", 1 }, /* "\xA2" */
  { "\xa3", 1 }, /* "\xA3" */
  { "\xa4", 1 }, /* "\xA4" */
  { "\xa5", 1 }, /* "\xA5" */
  { "\xa6", 1 }, /* "\xA6" */
  { "\xa7", 1 }, /* "\xA7" */
  { "\xa8", 1 }, /* "\xA8" */
  { "\xa9", 1 }, /* "\xA9" */
  { "\xaa", 1 }, /* "\xAA" */
  { "\xab", 1 }, /* "\xAB" */
  { "\xac", 1 }, /* "\xAC" */
  { "\xad", 1 }, /* "\xAD" */
  { "\xae", 1 }, /* "\xAE" */
  { "\xaf", 1 }, /* "\xAF" */
  { "\xb0", 1 }, /* "\xB0" */
  { "\xb1", 1 }, /* "\xB1" */
  { "\xb2", 1 }, /* "\xB2" */
  { "\xb3", 1 }, /* "\xB3" */
  { "\xb4", 1 }, /* "\xB4" */
  { "\xb5", 1 }, /* "\xB5" */
  { "\xb6", 1 }, /* "\xB6" */
  { "\xb7", 1 }, /* "\xB7" */
  { "\xb8", 1 }, /* "\xB8" */
  { "\xb9", 1 }, /* "\xB9" */
  { "\xba", 1 }, /* "\xBA" */
  { "\xbb", 1 }, /* "\xBB" */
  { "\xbc", 1 }, /* "\xBC" */
  { "\xbd", 1 }, /* "\xBD" */
  { "\xbe", 1 }, /* "\xBE" */
  { "\xbf", 1 }, /* "\xBF" */
  { "\xc0", 1 }, /* "\xC0" */
  { "\xc1", 1 }, /* "\xC1" */
  { "\xc2", 1 }, /* "\xC2" */
  { "\xc3", 1 }, /* "\xC3" */
  { "\xc4", 1 }, /* "\xC4" */
  { "\xc5", 1 }, /* "\xC5" */
  { "\xc6", 1 }, /* "\xC6" */
  { "\xc7", 1 }, /* "\xC7" */
  { "\xc8", 1 }, /* "\xC8" */
  { "\xc9", 1 }, /* "\xC9" */
  { "\xca", 1 }, /* "\xCA" */
  { "\xcb", 1 }, /* "\xCB" */
  { "\xcc", 1 }, /* "\xCC" */
  { "\xcd", 1 }, /* "\xCD" */
  { "\xce", 1 }, /* "\xCE" */
  { "\xcf", 1 }, /* "\xCF" */
  { "\xd0", 1 }, /* "\xD0" */
  { "\xd1", 1 }, /* "\xD1" */
  { "\xd2", 1 }, /* "\xD2" */
  { "\xd3", 1 }, /* "\xD3" */
  { "\xd4", 1 }, /* "\xD4" */
  { "\xd5", 1 }, /* "\xD5" */
  { "\xd6", 1 }, /* "\xD6" */
  { "\xd7", 1 }, /* "\xD7" */
  { "\xd8", 1 }, /* "\xD8" */
  { "\xd9", 1 }, /* "\xD9" */
  { "\xda", 1 }, /* "\xDA" */
  { "\xdb", 1 }, /* "\xDB" */
  { "\xdc", 1 }, /* "\xDC" */
  { "\xdd", 1 }, /* "\xDD" */
  { "\xde", 1 }, /* "\xDE" */
  { "\xdf", 1 }, /* "\xDF" */
  { "\xe0", 1 }, /* "\xE0" */
  { "\xe1", 1 }, /* "\xE1" */
  { "\xe2", 1 }, /* "\xE2" */
  { "\xe3", 1 }, /* "\xE3" */
  { "\xe4", 1 }, /* "\xE4" */
  { "\xe5", 1 }, /* "\xE5" */
  { "\xe6", 1 }, /* "\xE6" */
  { "\xe7", 1 }, /* "\xE7" */
  { "\xe8", 1 }, /* "\xE8" */
  { "\xe9", 1 }, /* "\xE9" */
  { "\xea", 1 }, /* "\xEA" */
  { "\xeb", 1 }, /* "\xEB" */
  { "\xec", 1 }, /* "\xEC" */
  { "\xed", 1 }, /* "\xED" */
  { "\xee", 1 }, /* "\xEE" */
  { "\xef", 1 }, /* "\xEF" */
  { "\xf0", 1 }, /* "\xF0" */
  { "\xf1", 1 }, /* "\xF1" */
  { "\xf2", 1 }, /* "\xF2" */
  { "\xf3", 1 }, /* "\xF3" */
  { "\xf4", 1 }, /* "\xF4" */
  { "\xf5", 1 }, /* "\xF5" */
  { "\xf6", 1 }, /* "\xF6" */
  { "\xf7", 1 }, /* "\xF7" */
  { "\xf8", 1 }, /* "\xF8" */
  { "\xf9", 1 }, /* "\xF9" */
  { "\xfa", 1 }, /* "\xFA" */
  { "\xfb", 1 }, /* "\xFB" */
  { "\xfc", 1 }, /* "\xFC" */
  { "\xfd", 1 }, /* "\xFD" */
  { "\xfe", 1 }, /* "\xFE" */
  { "\xff", 1 }, /* "\xFF" */
};

#define n1_html_escape_byte(a) (html_escape_byte_tbl[(unsigned char)a])

typedef __m128i m128;

#define n1_m128_of_bptr(p) _mm_loadu_si128((__m128i const*)(p))
#define n0_need_to_escape() n1_m128_of_bptr("&<>\"'\0\0\0\0\0\0\0\0\0\0\0")

#define n4_cmpestri_ubyte_eqany_ppol_lsig(a, la, b, lb) \
  _mm_cmpestri(a, la, b, lb, \
      _SIDD_UBYTE_OPS|_SIDD_CMP_EQUAL_ANY| \
      _SIDD_POSITIVE_POLARITY|_SIDD_LEAST_SIGNIFICANT)

#include "../coq/gen/esc.c"

VALUE
trec_html_escape(VALUE self, VALUE str)
{
  buffer buf;

  StringValue(str);
  RB_GC_GUARD(str);

  buf = buffer_new(RSTRING_LEN(str));
  buf = n3_sse_html_escape(buf, RSTRING_PTR(str), RSTRING_LEN(str));

  return buf.str;
}

VALUE
sse_html_escape(VALUE self, VALUE str)
{
  buffer buf;

  StringValue(str);
  RB_GC_GUARD(str);

  buf = buffer_new(RSTRING_LEN(str));

  n3_sse_html_escape(buf, RSTRING_PTR(str), RSTRING_LEN(str));

  return buf.str;
}

void
Init_verified_html_escape()
{
  rb_define_global_function("trec_html_escape", trec_html_escape, 1);
  rb_define_global_function("sse_html_escape", sse_html_escape, 1);
}
