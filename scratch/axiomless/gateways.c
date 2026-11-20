/* Where an axiom enters a library.

   gateways EDGES N ROOT WEIGHTS THRESHOLD

   EDGES is the graph that Census.lean writes with --edges: a line "i<TAB>j j ..." for the constants j that constant
   i names. N is the number of constants, ROOT the number of an axiom, WEIGHTS a file of N lines "0" or "1" (1 for
   the constants to count: the theorems with a name a person wrote).

   A constant c dominates a constant t if every chain of uses from t down to the axiom passes through c. If c were
   proved without the axiom, every constant it dominates would be free of it. The program computes the dominator
   tree of the reversed graph from ROOT (Cooper, Harvey and Kennedy's iteration) and prints, for each constant that
   dominates at least THRESHOLD counted constants, a line

       count <TAB> constant <TAB> its immediate dominator <TAB> number of constants it names that depend on the axiom
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int *idom, *rpo_num;

static int intersect(int a, int b) {
  while (a != b) {
    while (rpo_num[a] > rpo_num[b]) a = idom[a];
    while (rpo_num[b] > rpo_num[a]) b = idom[b];
  }
  return a;
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: gateways EDGES N ROOT WEIGHTS THRESHOLD\n"); return 1; }
  int n = atoi(argv[2]), root = atoi(argv[3]);
  long threshold = atol(argv[5]);
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror(argv[1]); return 1; }
  /* forward graph in CSR form: uses[ustart[i] .. ustart[i+1]) */
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
      if (j != i) uses[m++] = (int)j;
      p = q;
    }
  }
  ustart[n] = m;
  fclose(f);
  /* reversed graph: usedby */
  long *rstart = calloc(n + 2, sizeof(long));
  for (long e = 0; e < m; e++) rstart[uses[e] + 2]++;
  for (int i = 0; i < n; i++) rstart[i + 2] += rstart[i + 1];
  int *usedby = malloc(m * sizeof(int));
  for (int i = 0; i < n; i++)
    for (long e = ustart[i]; e < ustart[i + 1]; e++) usedby[rstart[uses[e] + 1]++] = i;
  /* now usedby[rstart[j] .. rstart[j+1]) are the constants that name j */
  /* depth-first postorder of the reversed graph from the root */
  int *order = malloc(n * sizeof(int)), cnt = 0;
  rpo_num = malloc(n * sizeof(int));
  for (int i = 0; i < n; i++) rpo_num[i] = -1;
  int *stack = malloc(n * sizeof(int)); long *pos = malloc(n * sizeof(long)); int sp = 0;
  char *seen = calloc(n, 1);
  stack[0] = root; pos[0] = rstart[root]; seen[root] = 1; sp = 1;
  while (sp) {
    int c = stack[sp - 1];
    if (pos[sp - 1] < rstart[c + 1]) {
      int d = usedby[pos[sp - 1]++];
      if (!seen[d]) { seen[d] = 1; stack[sp] = d; pos[sp] = rstart[d]; sp++; }
    } else { order[cnt++] = c; sp--; }
  }
  /* reverse postorder number: the root gets 0 */
  for (int k = 0; k < cnt; k++) rpo_num[order[k]] = cnt - 1 - k;
  idom = malloc(n * sizeof(int));
  for (int i = 0; i < n; i++) idom[i] = -1;
  idom[root] = root;
  int changed = 1, passes = 0;
  while (changed) {
    changed = 0; passes++;
    for (int k = cnt - 2; k >= 0; k--) {
      int v = order[k], best = -1;
      /* the predecessors of v in the reversed graph are the constants v names */
      for (long e = ustart[v]; e < ustart[v + 1]; e++) {
        int p = uses[e];
        if (rpo_num[p] < 0 || idom[p] < 0) continue;
        best = best < 0 ? p : intersect(p, best);
      }
      if (best != idom[v]) { idom[v] = best; changed = 1; }
    }
  }
  /* counts over the dominator tree */
  long *count = calloc(n, sizeof(long));
  FILE *w = fopen(argv[4], "r");
  if (!w) { perror(argv[4]); return 1; }
  for (int i = 0; i < n; i++) { int x = 0; if (fscanf(w, "%d", &x) != 1) break; if (rpo_num[i] >= 0) count[i] = x; }
  fclose(w);
  long total = 0;
  for (int i = 0; i < n; i++) total += count[i];
  for (int k = 0; k < cnt - 1; k++) { int v = order[k]; count[idom[v]] += count[v]; }
  fprintf(stderr, "%d constants depend on the axiom, %ld of them counted; %d passes\n", cnt, total, passes);
  for (int k = cnt - 1; k >= 0; k--) {
    int v = order[k];
    if (count[v] >= threshold) {
      long tainted = 0;
      for (long e = ustart[v]; e < ustart[v + 1]; e++) if (rpo_num[uses[e]] >= 0) tainted++;
      printf("%ld\t%d\t%d\t%ld\n", count[v], v, idom[v], tainted);
    }
  }
  return 0;
}
