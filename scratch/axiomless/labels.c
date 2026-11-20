/* Which kinds of use reach a constant.

   labels EDGES N LABELS

   EDGES is the graph of Census.lean (--edges), N its number of constants, and LABELS a file of N lines "own cut":
   `own` is a bit mask of labels that the constant carries itself, and `cut` is 1 if what the constant names is not
   to be followed. The program prints, for each constant, the union of the labels of the constants it reaches. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: labels EDGES N LABELS\n"); return 1; }
  int n = atoi(argv[2]);
  if (n <= 0) { fprintf(stderr, "N must be positive\n"); return 1; }
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror(argv[1]); return 1; }
  long cap = 1 << 25, m = 0;
  int *uses = malloc(cap * sizeof(int));
  long *ustart = calloc(n + 1, sizeof(long));
  size_t len = 0; char *line = NULL;
  for (int i = 0; i < n; i++) {
    if (getline(&line, &len, f) < 0) { fprintf(stderr, "short edge file\n"); return 1; }
    ustart[i] = m;
    char *p = strchr(line, '\t');
    if (!p) continue;
    p++;
    while (*p && *p != '\n') {
      char *q; long j = strtol(p, &q, 10);
      if (q == p) break;
      if (m == cap) { cap *= 2; uses = realloc(uses, cap * sizeof(int)); }
      uses[m++] = (int)j;
      p = q;
    }
  }
  ustart[n] = m;
  fclose(f);
  unsigned *mask = calloc(n, sizeof(unsigned)); char *cut = calloc(n, 1);
  FILE *l = fopen(argv[3], "r");
  if (!l) { perror(argv[3]); return 1; }
  for (int i = 0; i < n; i++) { unsigned o = 0; int c = 0; if (fscanf(l, "%u %d", &o, &c) != 2) break; mask[i] = o; cut[i] = (char)c; }
  fclose(l);
  /* depth-first postorder over the whole graph */
  int *order = malloc(n * sizeof(int)), cnt = 0;
  int *stack = malloc(n * sizeof(int)); long *pos = malloc(n * sizeof(long));
  char *seen = calloc(n, 1);
  for (int r = 0; r < n; r++) {
    if (seen[r]) continue;
    int sp = 1; stack[0] = r; pos[0] = ustart[r]; seen[r] = 1;
    while (sp) {
      int c = stack[sp - 1];
      if (pos[sp - 1] < ustart[c + 1]) {
        int d = uses[pos[sp - 1]++];
        if (!seen[d]) { seen[d] = 1; stack[sp] = d; pos[sp] = ustart[d]; sp++; }
      } else { order[cnt++] = c; sp--; }
    }
  }
  int changed = 1;
  while (changed) {
    changed = 0;
    for (int k = 0; k < cnt; k++) {
      int v = order[k];
      if (cut[v]) continue;
      unsigned x = mask[v];
      for (long e = ustart[v]; e < ustart[v + 1]; e++) x |= mask[uses[e]];
      if (x != mask[v]) { mask[v] = x; changed = 1; }
    }
  }
  for (int i = 0; i < n; i++) printf("%u\n", mask[i]);
  return 0;
}
