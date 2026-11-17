/* A layout demonstration header for the explorer's Headers tab (written for this repository).
   The same aggregates are laid out under System V x86-64 and Microsoft x64. */
#pragma once
typedef unsigned int u32;
enum mode { MODE_OFF, MODE_ON = 4, MODE_AUTO };
struct rec { char c; unsigned flags : 3; unsigned mode : 5; long n; int x; double d; };
struct pt { char tag; long v; short s; };
union word { u32 u; float f; unsigned char b[4]; };
struct node { struct pt where; struct node *next; u32 count; };
long rec_size(const struct rec *r);
double scale(double x, float k, int n);
long double precise(long double x);
struct pt make_pt(long v);
int sum(int n, ...);
