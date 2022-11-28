/**************************************************************************/
/* AU compilation.                                                        */
/* Skeleton file -- expected to be modified as part of the assignment     */
/**************************************************************************/

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

int64_t tigermain(void *, int64_t);

int64_t divisionByZero()
{
  /* Note: Division by zero should normally exit with SIGFPE,
   * which has error code 136, but for the purpose of testing
   * we choose to use exit(1) to distinguish the handled case
   * from the unhandled. See here for more info:
   * http://www.bu.edu/tech/files/text/batchcode.txt
   * 
   * "But doesn't the system handle it for us?"
   * Unfortunately, division by zero has undefined semantics
   * in LLVM. Further motivation can be found in
   * 'A Sermon on Safety' on pp. 160-161 in the book :) */
  fprintf(stderr, "Error: division by zero\n");
  exit(1);
  return 0; /* keeping gcc happy */
}

int64_t arrLenError(int64_t len)
{
  fprintf(stderr, "Error: attempt to create array with negative length (%" PRId64 ")\n", len);
  exit(1);
  return 0; /* keeping gcc happy */
}

/* p164 */
void *initArray(int64_t size, int64_t elem_size, void *init)
{
  /* Array layout: [S, elm0, elm1, ..., elmS-1].  Returning pointer
   * to elm0, which means that the size S may be ignored---but it
   * is available in case array bounds checking code is generated */

  int64_t i;
  void *a;
  void *p;

  if (size < 0)
    arrLenError(size);
  a = calloc(sizeof(int64_t) + size * elem_size, 1);
  p = a;
  memcpy(p, &size, sizeof(int64_t));
  p += sizeof(int64_t);
  for (i = 0; i < size; i++)
  {
    memcpy(p, init, elem_size);
    p += elem_size;
  }
  return a + sizeof(int64_t);
}

int64_t arrInxError(int64_t index)
{
  fprintf(stderr, "Error: array index (%" PRId64 ") out of range\n", index);
  exit(1);
  return 0; /* keeping gcc happy */
}

void *allocRecord(int64_t size)
{
  return calloc(size, 1);
}

int64_t recFieldError()
{
  fprintf(stderr, "Error: record field lookup applied to nil\n");
  exit(1);
  return 0; /* keeping gcc happy */
}

struct string
{
  int64_t length;
  unsigned char chars[1];
};

int64_t stringEqual(struct string *s, struct string *t)
{
  int64_t i;
  if (s == t)
    return 1;
  if (s->length != t->length)
    return 0;
  for (i = 0; i < s->length; i++)
    if (s->chars[i] != t->chars[i])
      return 0;
  return 1;
}

int64_t stringNotEq(struct string *s, struct string *t)
{
  return !stringEqual(s, t);
}

int64_t stringLessEq(struct string *s, struct string *t)
{
  int64_t i, len;
  if (s == t)
    return 1;
  len = s->length <= t->length ? s->length : t->length;
  for (i = 0; i < len; i++)
  {
    if (s->chars[i] < t->chars[i])
      return 1;
    if (s->chars[i] > t->chars[i])
      return 0;
  }
  return (s->length <= t->length);
}

int64_t stringLess(struct string *s, struct string *t)
{
  return !stringLessEq(t, s);
}

int64_t stringGreater(struct string *s, struct string *t)
{
  return !stringLessEq(s, t);
}

int64_t stringGreaterEq(struct string *s, struct string *t)
{
  return stringLessEq(t, s);
}

void print(void *static_link, struct string *s)
{
  int64_t i;
  unsigned char *p = s->chars;
  for (i = 0; i < s->length; i++, p++)
  {
    putchar(*p);
  }
}

void flush(void *static_link)
{
  fflush(stdout);
}

struct string consts[256];
struct string empty = {0, ""};

int main(int argc, char *argv[])
{
  int i;
  int result;

  for (i = 0; i < 256; i++)
  {
    consts[i].length = 1;
    consts[i].chars[0] = i;
  }
  /* args to tigermain: 0 is the static link, 1000 is unused, but
   * easy to see on the stack, nice when debugging frames */
  result = tigermain(0, 1000);
  return result;
}

int64_t ord(void *static_link, struct string *s)
{
  if (s->length == 0)
    return -1;
  else
    return s->chars[0];
}

struct string *chr(void *static_link, int64_t i)
{
  if (i < 0 || i >= 256)
  {
    fprintf(stderr, "Error: chr(%" PRId64 ") out of range\n", i);
    exit(1);
  }
  return consts + i;
}

int64_t size(void *static_link, struct string *s)
{
  return s->length;
}

struct string *substring(void *static_link, struct string *s, int64_t first, int64_t n)
{
  if (first < 0 || first + n > s->length)
  {
    fprintf(stderr, "Error: substring([%" PRId64 "], %" PRId64 ", %" PRId64 ") out of range\n", s->length, first, n);
    exit(1);
  }
  if (n == 1)
    return consts + s->chars[first];
  {
    struct string *t = (struct string *)malloc(sizeof(int64_t) + n);
    int64_t i;
    t->length = n;
    for (i = 0; i < n; i++)
      t->chars[i] = s->chars[first + i];
    return t;
  }
}

struct string *concat(void *static_link, struct string *a, struct string *b)
{
  if (a->length == 0)
    return b;
  else if (b->length == 0)
    return a;
  else
  {
    int64_t i, n = a->length + b->length;
    struct string *t = (struct string *)malloc(sizeof(int64_t) + n);
    t->length = n;
    for (i = 0; i < a->length; i++)
      t->chars[i] = a->chars[i];
    for (i = 0; i < b->length; i++)
      t->chars[i + a->length] = b->chars[i];
    return t;
  }
}

int64_t not(void *static_link, int64_t i)
{
  return !i;
}

struct string *getChar(void *static_link)
{
  int i = getc(stdin);
  if (i == EOF)
    return &empty;
  else
    return consts + i;
}

void tigerexit(void *static_link, int64_t code)
{
  exit(code);
}

int64_t exponent(int64_t base, int64_t expn)
{
  fprintf(stderr, "Error: exponent not yet implemented\n");
  exit(1);
  return 0; /* keeping gcc happy */
}
