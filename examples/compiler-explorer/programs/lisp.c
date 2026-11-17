/* A tiny Lisp: integers, symbols, cons cells; reads and evaluates (+ ...), (* ...),
   (quote x), (if c a b) and (car/cdr/cons ...). No garbage collection: a fixed arena. */
#include <ctype.h>
#include <stdio.h>
#include <string.h>

enum tag { NUM, SYM, CONS, NIL };
typedef struct cell { enum tag tag; long num; const char *sym; struct cell *car, *cdr; } cell;

static cell arena[1024];
static int used;
static cell nil = { NIL, 0, 0, 0, 0 };

static cell *mk(enum tag t) { cell *c = &arena[used++]; c->tag = t; return c; }
static cell *num(long n) { cell *c = mk(NUM); c->num = n; return c; }
static cell *cons(cell *a, cell *d) { cell *c = mk(CONS); c->car = a; c->cdr = d; return c; }

static const char *p;
static char names[64][16];
static int nnames;

static const char *intern(const char *s, size_t n)
{
  for (int i = 0; i < nnames; i++)
    if (strlen(names[i]) == n && !strncmp(names[i], s, n))
      return names[i];
  memcpy(names[nnames], s, n);
  names[nnames][n] = 0;
  return names[nnames++];
}

static cell *read(void)
{
  while (isspace((unsigned char)*p)) p++;
  if (*p == '(') {
    p++;
    cell *head = &nil, **tail = &head;
    for (;;) {
      while (isspace((unsigned char)*p)) p++;
      if (*p == ')') { p++; return head; }
      *tail = cons(read(), &nil);
      tail = &(*tail)->cdr;
    }
  }
  if (isdigit((unsigned char)*p)) {
    long n = 0;
    while (isdigit((unsigned char)*p)) n = 10 * n + (*p++ - '0');
    return num(n);
  }
  const char *s = p;
  while (*p && !isspace((unsigned char)*p) && *p != '(' && *p != ')') p++;
  cell *c = mk(SYM);
  c->sym = intern(s, (size_t)(p - s));
  return c;
}

static cell *eval(cell *e)
{
  if (e->tag != CONS) return e;
  const char *op = e->car->sym;
  cell *args = e->cdr;
  if (!strcmp(op, "quote")) return args->car;
  if (!strcmp(op, "if"))
    return eval(eval(args->car)->num ? args->cdr->car : args->cdr->cdr->car);
  if (!strcmp(op, "car")) return eval(args->car)->car;
  if (!strcmp(op, "cdr")) return eval(args->car)->cdr;
  if (!strcmp(op, "cons")) return cons(eval(args->car), eval(args->cdr->car));
  long acc = !strcmp(op, "*");
  for (; args->tag == CONS; args = args->cdr)
    acc = (*op == '*') ? acc * eval(args->car)->num : acc + eval(args->car)->num;
  return num(acc);
}

static void print(cell *c)
{
  if (c->tag == NUM) printf("%ld", c->num);
  else if (c->tag == SYM) printf("%s", c->sym);
  else if (c->tag == NIL) printf("()");
  else {
    putchar('(');
    for (;;) {
      print(c->car);
      c = c->cdr;
      if (c->tag != CONS) break;
      putchar(' ');
    }
    if (c->tag != NIL) { printf(" . "); print(c); }
    putchar(')');
  }
}

int main(void)
{
  p = "(+ 1 (* 2 3) (if 0 100 (car (quote (4 5)))))";
  print(eval(read()));
  putchar('\n');
  p = "(cons 1 (quote (2 3)))";
  print(eval(read()));
  putchar('\n');
  return 0;
}
