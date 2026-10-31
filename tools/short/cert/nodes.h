// The node types of the certificate: Li's decomposition of region C (Section 5 of arXiv:2308.04458v8, his code's
// regions U_C01 ... U_C13) as a tree of sums S(A_q, p_last) over boxes of exponents.
// Coordinates: x0..x7 = alpha_1..alpha_8 (alpha_j the exponent of p_j). S_k = 1 - x0 - ... - x_{k-1}.
#pragma once
#include "exact.h"
#include <string>

enum NT {
    N2,      // (+) S(A_{p1 p2}, p2), (a1, a2) in region C                                                  depth 2
    N3,      // (-) S(A_{p1 p2 p3}, p3)                                                                     depth 3
    N4S,     // (+) S(A_{p1..p4}, p4) (straightforward)                                       loss U_C01    depth 4
    N4R,     // (+) S(A_{beta p2 p3 p4}, p4) (role reversal: beta = S3 sifted by p3, beta1 = x0 - x3) loss U_C08
    N5Ss,    // (-) under D*                                                                                depth 5
    N5Sd,    // (-) under D-double-dagger (role reversal at depth 5)
    N5Rb1,   // (-) N4R, beta1 decomposed (alpha4' in D*)
    N5Rb,    // (-) N4R, beta decomposed (alpha4'' in D*)
    N6Ss,    // (+) loss U_C03                                                                              depth 6
    N6Sd,    // (+) (gamma = S5 sifted by p5, p2..p6, gamma1 = x0 - x5 sifted by p6)               loss U_C04
    N6Rb1,   // (+) loss U_C12
    N6Rb,    // (+) loss U_C13
    N7Ss, N8Ss,     // under D** (U_C05)                                                                    depth 7, 8
    N7Dg1, N8Dg1,   // alpha6-dd in D**: gamma1 decomposed (U_C06)
    N7Dg, N8Dg,     // alpha6-dd' in D**: gamma decomposed (U_C07)
    NA2,     // (+) region A (dropped)
    NT_COUNT
};

// decisions
enum Dec : uint8_t { D_OUT, D_ASYM_G2, D_ASYM_TII, D_DROP, D_SPLIT, D_DEC0, D_DEC1, D_FAIL };

struct Item { LF a; bool rough; int sift; };          // a rough item sifted by p_sift (x[sift])
struct Con { LF L; bool lt; };                        // domain: L < 0 (lt) or L >= 0
struct Omega { LF N; int k; };                        // omega*(N / x_k)
// a Type I requirement: variables (linear forms); kinds allowed (bit 0 ALL, 1 D0, 2 D1, 3 D2)
struct TypeIReq { std::vector<LF> v; int kinds; };
struct Child { NT type; std::vector<TypeIReq> req; };  // the decomposition into the child type, with its Type I needs

struct NodeDef {
    std::string name;
    int dim;
    bool plus;                   // + terms may be dropped
    std::vector<Item> items;     // the factors (sum to 1)
    std::vector<Con> dom;        // the domain (all coordinates)
    std::vector<Child> ch;       // the decompositions (DEC0, DEC1)
    std::vector<Omega> om;       // the loss integrand's omegas (+ nodes)
    int wt[MAXD];                // the weights: 0 dt, 1 dt/t, 2 dt/t^2
    int loss;                    // Li's loss term index for reports (U_Cxx), -1 none
};

extern NodeDef ND[NT_COUNT];
void initNodes();
