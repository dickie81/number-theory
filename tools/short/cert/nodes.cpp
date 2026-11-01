#include "nodes.h"

NodeDef ND[NT_COUNT];

static LF X(int j) { return lfT(j); }
static LF S(int k) { return lfS(k); }
static LF K(i64 v) { return lfK(v); }
static Item P(LF a) { return {a, false, -1}; }
static Item R(LF a, int s) { return {a, true, s}; }
static Con lt(LF a, LF b) { return {a - b, true}; }          // a < b
static Con geK(LF a, i64 v) { return {a - K(v), false}; }    // a >= v / DEN

// x_j in [nu0, min(uppers)) where each upper is "2 x_j < U" (twice) or "x_j < U"
static void rng(std::vector<Con>& d, int j, std::vector<LF> lt1, std::vector<LF> lt2) {
    d.push_back(geK(X(j), NU0));
    for (auto& u : lt1) d.push_back(lt(X(j), u));
    for (auto& u : lt2) d.push_back({2 * X(j) - u - K(ESL + 1), true});    // 2 x_j <= u + E: the checker's slack
}
static std::vector<LF> V(std::initializer_list<LF> l) { return std::vector<LF>(l); }
static void setW(NodeDef& d, std::initializer_list<int> w) {
    int j = 0;
    for (int x : w) d.wt[j++] = x;
    for (; j < MAXD; ++j) d.wt[j] = 0;
}
static const int ALLK = 15, K2 = 3;   // all kinds; ALL and D0 only (Li's TypeIRegion2D)

void initNodes() {
    std::vector<Con> d2;
    rng(d2, 0, {}, {K(DEN)});                         // x0 in [nu0, 1/2)
    rng(d2, 1, {X(0)}, {S(1)});                       // x1 in [nu0, min(x0, (1 - x0)/2)); region C: root context
    std::vector<Con> d3 = d2; rng(d3, 2, {X(1)}, {S(2)});
    std::vector<Con> d4s = d3; rng(d4s, 3, {X(2)}, {S(3)});
    std::vector<Con> d4r = d3; rng(d4r, 3, {}, {X(0)});
    std::vector<Con> d5s = d4s; rng(d5s, 4, {X(3)}, {S(4)});
    std::vector<Con> d5b1 = d4r; rng(d5b1, 4, {X(3)}, {X(0) - X(3)});
    std::vector<Con> d5b = d4r; rng(d5b, 4, {X(2)}, {S(3)});
    std::vector<Con> d6s = d5s; rng(d6s, 5, {X(4)}, {S(5)});
    std::vector<Con> d6d = d5s; rng(d6d, 5, {}, {X(0)});
    std::vector<Con> d6b1 = d5b1; rng(d6b1, 5, {X(4)}, {X(0) - X(3) - X(4)});
    std::vector<Con> d6b = d5b; rng(d6b, 5, {X(4)}, {S(3) - X(4)});
    std::vector<Con> d7s = d6s; rng(d7s, 6, {X(5)}, {S(6)});
    std::vector<Con> d8s = d7s; rng(d8s, 7, {X(6)}, {S(7)});
    std::vector<Con> d7g1 = d6d; rng(d7g1, 6, {X(5)}, {X(0) - X(5)});
    std::vector<Con> d8g1 = d7g1; rng(d8g1, 7, {X(6)}, {X(0) - X(5) - X(6)});
    std::vector<Con> d7g = d6d; rng(d7g, 6, {X(4)}, {S(5)});
    std::vector<Con> d8g = d7g; rng(d8g, 7, {X(6)}, {S(5) - X(6)});
    std::vector<Con> dA;
    dA.push_back(geK(X(0), DEN / 4)); dA.push_back(lt(5 * X(0), K(2 * DEN)));
    dA.push_back(lt(S(1), 3 * X(1)) /* x1 > (1 - x0)/3, closed in Li: kept as an over-approximation */);
    dA.push_back(lt(X(1), X(0))); dA.push_back(lt(X(1), K(DEN) - 2 * X(0)));

    auto& n2 = ND[N2];
    n2 = {"N2", 2, true, {P(X(0)), P(X(1)), R(S(2), 1)}, d2, {{N3, {{V({X(0), X(1)}), K2}}}}, {{S(2), 1}}, {}, -1};
    setW(n2, {1, 2});
    auto& n3 = ND[N3];
    n3 = {"N3", 3, false, {P(X(0)), P(X(1)), P(X(2)), R(S(3), 2)}, d3,
          {{N4S, {{V({X(0), X(1), X(2)}), ALLK}}}, {N4R, {{V({S(3), X(1), X(2)}), ALLK}}}}, {}, {}, -1};
    setW(n3, {});
    auto& n4s = ND[N4S];
    n4s = {"N4S", 4, true, {P(X(0)), P(X(1)), P(X(2)), P(X(3)), R(S(4), 3)}, d4s,
           {{N5Ss, {{V({X(0), X(1), X(2), X(3), X(3)}), ALLK}}},
            {N5Sd, {{V({X(0), X(1), X(2), X(3)}), ALLK}, {V({S(4), X(1), X(2), X(3)}), ALLK}}}},
           {{S(4), 3}}, {}, 1};
    setW(n4s, {1, 1, 1, 2});
    auto& n4r = ND[N4R];
    n4r = {"N4R", 4, true, {R(S(3), 2), P(X(1)), P(X(2)), P(X(3)), R(X(0) - X(3), 3)}, d4r,
           {{N5Rb1, {{V({S(3), X(1), X(2), X(3), X(3)}), ALLK}}},
            {N5Rb, {{V({X(0) - X(3), X(1), X(2), X(3), X(2)}), ALLK}}}},
           {{X(0) - X(3), 3}, {S(3), 2}}, {}, 8};
    setW(n4r, {0, 1, 2, 2});
    std::vector<Item> it5s = {P(X(0)), P(X(1)), P(X(2)), P(X(3)), P(X(4)), R(S(5), 4)};
    ND[N5Ss] = {"N5Ss", 5, false, it5s, d5s, {{N6Ss, {}}}, {}, {}, -1};
    ND[N5Sd] = {"N5Sd", 5, false, it5s, d5s, {{N6Sd, {}}}, {}, {}, -1};
    ND[N5Rb1] = {"N5Rb1", 5, false, {R(S(3), 2), P(X(1)), P(X(2)), P(X(3)), P(X(4)), R(X(0) - X(3) - X(4), 4)}, d5b1,
                 {{N6Rb1, {}}}, {}, {}, -1};
    ND[N5Rb] = {"N5Rb", 5, false, {R(X(0) - X(3), 3), P(X(1)), P(X(2)), P(X(3)), P(X(4)), R(S(3) - X(4), 4)}, d5b,
                {{N6Rb, {}}}, {}, {}, -1};
    for (NT t : {N5Ss, N5Sd, N5Rb1, N5Rb}) setW(ND[t], {});
    auto& n6s = ND[N6Ss];
    n6s = {"N6Ss", 6, true, {P(X(0)), P(X(1)), P(X(2)), P(X(3)), P(X(4)), P(X(5)), R(S(6), 5)}, d6s,
           {{N7Ss, {{V({X(0), X(1), X(2), X(3), X(4), X(5), X(5)}), ALLK}}}}, {{S(6), 5}}, {}, 3};
    setW(n6s, {1, 1, 1, 1, 1, 2});
    auto& n6d = ND[N6Sd];
    n6d = {"N6Sd", 6, true, {R(S(5), 4), P(X(1)), P(X(2)), P(X(3)), P(X(4)), P(X(5)), R(X(0) - X(5), 5)}, d6d,
           {{N7Dg1, {{V({S(5), X(1), X(2), X(3), X(4), X(5), X(5)}), ALLK}}},
            {N7Dg, {{V({X(0) - X(5), X(1), X(2), X(3), X(4), X(5), X(4)}), ALLK}}}},
           {{X(0) - X(5), 5}, {S(5), 4}}, {}, 4};
    setW(n6d, {0, 1, 1, 1, 2, 2});
    auto& n6b1 = ND[N6Rb1];
    n6b1 = {"N6Rb1", 6, true,
            {R(S(3), 2), P(X(1)), P(X(2)), P(X(3)), P(X(4)), P(X(5)), R(X(0) - X(3) - X(4) - X(5), 5)}, d6b1, {},
            {{S(3), 2}, {X(0) - X(3) - X(4) - X(5), 5}}, {}, 12};
    setW(n6b1, {0, 1, 2, 1, 1, 2});
    auto& n6b = ND[N6Rb];
    n6b = {"N6Rb", 6, true, {R(X(0) - X(3), 3), P(X(1)), P(X(2)), P(X(3)), P(X(4)), P(X(5)), R(S(3) - X(4) - X(5), 5)},
           d6b, {}, {{S(3) - X(4) - X(5), 5}, {X(0) - X(3), 3}}, {}, 13};
    setW(n6b, {0, 1, 1, 2, 1, 2});
    ND[N7Ss] = {"N7Ss", 7, false, {P(X(0)), P(X(1)), P(X(2)), P(X(3)), P(X(4)), P(X(5)), P(X(6)), R(S(7), 6)}, d7s,
                {{N8Ss, {}}}, {}, {}, -1};
    setW(ND[N7Ss], {});
    ND[N8Ss] = {"N8Ss", 8, true,
                {P(X(0)), P(X(1)), P(X(2)), P(X(3)), P(X(4)), P(X(5)), P(X(6)), P(X(7)), R(S(8), 7)}, d8s, {},
                {{S(8), 7}}, {}, 5};
    setW(ND[N8Ss], {1, 1, 1, 1, 1, 1, 1, 2});
    ND[N7Dg1] = {"N7Dg1", 7, false,
                 {R(S(5), 4), P(X(1)), P(X(2)), P(X(3)), P(X(4)), P(X(5)), P(X(6)), R(X(0) - X(5) - X(6), 6)}, d7g1,
                 {{N8Dg1, {}}}, {}, {}, -1};
    setW(ND[N7Dg1], {});
    ND[N8Dg1] = {"N8Dg1", 8, true,
                 {R(S(5), 4), P(X(1)), P(X(2)), P(X(3)), P(X(4)), P(X(5)), P(X(6)), P(X(7)),
                  R(X(0) - X(5) - X(6) - X(7), 7)}, d8g1, {}, {{X(0) - X(5) - X(6) - X(7), 7}, {S(5), 4}}, {}, 6};
    setW(ND[N8Dg1], {0, 1, 1, 1, 2, 1, 1, 2});
    ND[N7Dg] = {"N7Dg", 7, false,
                {R(X(0) - X(5), 5), P(X(1)), P(X(2)), P(X(3)), P(X(4)), P(X(5)), P(X(6)), R(S(5) - X(6), 6)}, d7g,
                {{N8Dg, {}}}, {}, {}, -1};
    setW(ND[N7Dg], {});
    ND[N8Dg] = {"N8Dg", 8, true,
                {R(X(0) - X(5), 5), P(X(1)), P(X(2)), P(X(3)), P(X(4)), P(X(5)), P(X(6)), P(X(7)),
                 R(S(5) - X(6) - X(7), 7)}, d8g, {}, {{X(0) - X(5), 5}, {S(5) - X(6) - X(7), 7}}, {}, 7};
    setW(ND[N8Dg], {0, 1, 1, 1, 1, 2, 1, 2});
    ND[NA2] = {"NA2", 2, true, {P(X(0)), P(X(1)), R(S(2), 1)}, dA, {}, {{S(2), 1}}, {}, -1};
    setW(ND[NA2], {1, 2});
    // the factors of every node sum to 1
    for (int t = 0; t < NT_COUNT; ++t) {
        LF s;
        for (auto& it : ND[t].items) s = s + it.a;
        bool ok = s.c0 == DEN;
        for (int j = 0; j < MAXD; ++j) ok = ok && s.c[j] == 0;
        if (!ok) { fprintf(stderr, "items of %s do not sum to 1\n", ND[t].name.c_str()); exit(1); }
    }
}
