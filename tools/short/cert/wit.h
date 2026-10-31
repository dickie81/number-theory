// The witnesses of the certificate and their exact checks on a box, and the generator's searches for them.
#pragma once
#include "nodes.h"

// the root cell's context: which side of 2/5 (region C's two forms) and the interval I_h of nu(alpha_1)
struct RootCtx { int branch; int h; };
// the root's region constraint: Li's region C, alpha1 + 3 alpha2 < 1 (branch 0, alpha1 <= 2/5) or 2 alpha2 < alpha1
// (branch 1), or its complement (branches 2 and 3: the Lean's cells outside region C)
Con regionConOf(const RootCtx& rc);

// options of the Type II (real-exponent Hoelder) witnesses the certificate may use
struct TIIOpt { bool roughFactor = true; bool group = true; int maxGroup = 9; };
extern TIIOpt TIIO;
extern bool USE_G2, USE_TII;

// counters of the kernel's work (incremented by the exact checks)
struct Work {
    long long out = 0, g2 = 0, tii = 0, tyI = 0, bound = 0;     // checks of each kind
    long long tiiGroups = 0;                                     // groups (= f evaluations) over the TII checks
};
extern thread_local Work WK;

bool outside(NT t, const Box& B, const RootCtx& rc);
bool regionOutside(const Box& B, const RootCtx& rc);

// G2 (Li's Lemma 3.1): items M (mask) and R (mask, the complement of M and N); exact check on the box
bool checkG2(const std::vector<Item>& it, const Box& B, int M, int R);
bool searchG2(const std::vector<Item>& it, const Box& B, int& M, int& R);

// TII (the real-exponent Hoelder test): a partition of the items, as a label (4 bits) per item
bool checkTII(const std::vector<Item>& it, const Box& B, uint64_t part);
bool searchTII(const std::vector<Item>& it, const Box& B, uint64_t& part);
// the linearised check (tangents of f on its ramps): at least as strong as checkTII
bool checkTIIlin(const std::vector<Item>& it, const Box& B, uint64_t part);
extern bool TANDOM;                     // the linearised check's tangent minimised with the active constraints
extern long long WK_TIILIN;
i64 fexact(i64 A);    // floor(SCF / delta_req) for a factor of least exponent A / DEN (with kappa)

// Type I (Li's D0', D1', D2'): kind (0 ALL, 1 D0, 2 D1, 3 D2) and a role (0 m, 1 n, 2 h) per variable: code =
// kind | roles << 2
bool checkTypeI(const TypeIReq& r, const Box& B, uint32_t code);
bool searchTypeI(const TypeIReq& r, const Box& B, uint32_t& code);

i64 dropCost(NT t, const Box& B);     // the bound of the loss over the box, units 1/SC
extern int CHAINBOUND, CHAINREF;
extern thread_local long long WK_CHAINOPS;

// the upper end of the range of the child's new coordinate over the box (exclusive), from the child's domain
i64 childUpper(NT child, const Box& B);

// box tightening: a box containing box ∩ domain, by propagating the domain's linear constraints (twice); false if
// the box meets no point of the domain. The kernel recomputes it at every node.
bool tighten(NT t, Box& B, const RootCtx& rc);

// the active diagonal constraints of the domain on a box (for the domain-aware extremes lfminA / lfmaxA)
void actives(NT t, const Box& B, const RootCtx& rc, Act& A);
i64 tiiLinValue(const std::vector<Item>& it, const Box& B, uint64_t part);

// regions with cuts (diagonal splits): box ∩ domain ∩ cut half-spaces
static const int MAXCUT = 16;
struct Cuts { int n = 0; Con c[MAXCUT]; };
bool tightenC(NT t, Box& B, const RootCtx& rc, const Cuts& K);
Cuts pruneCuts(const Cuts& K, const Box& B);
bool outsideC(NT t, const Box& B, const RootCtx& rc, const Cuts& K);
void activesC(NT t, const Box& B, const RootCtx& rc, const Cuts& K, Act& A);
i64 dropCostVS(NT t, const Box& B, const RootCtx& rc, const Cuts& K, int q1, int k1, int q2, int k2);
extern thread_local long long WK_VSPARTS;
// generator-only: points of the current region used to filter the searches (0: off)
extern thread_local Box FILT_P[4];
extern thread_local int FILT_N;
// generator-only fast searches at a point (P a point box)
bool searchG2Pt(const std::vector<Item>& it, const Box& P, int& Mo, int& Ro);
bool searchTIIPt(const std::vector<Item>& it, const Box& P, uint64_t& part);
bool searchTypeIPt(const TypeIReq& r, const Box& P, uint32_t& code);
