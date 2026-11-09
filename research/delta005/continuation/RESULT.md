# Continuation towards delta = 0.005 — target not attained

This branch does not prove delta=0.005 and does not replace the submitted exact-DFT theorem. A green finite-research workflow is not Lean acceptance.

## Additional finite chart edit

The starting artifact is the 71,826-event word produced by research branch commit ca5515bad3dff29fda707429b70a4c9e795bd5a9, derived from DreamingOfClouds PR6934 (4e13b7acdbea1c9f12aa88126435360eecea7401) and Ali Romman's PR5599 helper-split identity.

At eight guarded events, replace the intermediate chart with binary basis [28,45,199,268] by [28,45,76,139,268]. All six incident moves remain strictly nested. The two scalar contacts are in the new common chart. Boundaries and normalized endpoint are unchanged. Complete replay over Q checks every public and owned output. The paid-profile change is +H1-2H2+H3; the productive profile is unchanged. Strict concavity gives 1+3^t<2*2^t for 0<t<1, hence a strict finite moment improvement.

The operator justification is frame induction: transitions apply Phi_V Phi_U^{-1}, same-frame rational additions commute with Phi, and unchanged boundary frames give the same operator whenever the inherited nested-map implementation applies. A complete all-width Lean instantiation of this PR6934-based circuit is NOT supplied.

The previous artifact had stale public metadata (1452 rather than 1453). The new output repairs and checks it without mutating the source. Improved payload SHA256: 96678afbc3b3b37983fb3667c814b599415abfdd5ba71aa8a16cd248434059a3.

## All-stage invoice obstruction

Native profiles:

```
H={1:11,2:17,3:44,4:215,5:68,6:41,7:10,8:61,9:586}
P={1:4131,2:885,3:771,4:217,5:299,6:12,7:10,8:6}
```

For L,R>=1 and N=L+R, define the invoice family

```
A_t(k)=sum_{j=1}^k (8j+1)^t-sum_{j=1}^{k-1}(8j)^t
F_t(L,R)=N*(sum_r(H_r-P_r)*r^t-16*8^t)
          +208*((8N+1)^t+A_t(L)+A_t(R))-416.
```

At 9+9 this equals the literal retained bill. Other stage counts are a defined pricing model, not newly materialized physical callers. Other native profiles and other caller formulas are outside the theorem.

For 0<t<1, A_t(k+1)-A_t(k)=(8k+9)^t-(8k)^t decreases with k. Balancing L,R therefore increases F. The balanced sequence B_t(N)=F_t(floor(N/2),ceil(N/2)) has decreasing increments: root increments decrease; the chain increment repeats each decreasing A_t increment twice.

At t=199/200, integer-only enclosures prove

```
B(2) in (-176.918213780808358964,-176.918213780808358963)
B(3)-B(2) in (-4.946171663628325973,-4.946171663628325972).
```

Thus F_{199/200}(L,R)<0 for EVERY positive L,R. The actual 9+9 margin is in (-571.075180524584726693,-571.075180524584726692).

The exact all-N invoice frontier is in (0.00362461493511114136,0.00362461493511114137), at 8+9. frontier.py proves the opposite signs of B(17)-B(16) and B(18)-B(17) throughout this interval and the crossing signs. For globality, F_t/5^t is strictly increasing in t>=0: the native signed coefficients are nonpositive at ranks <=5 and nonnegative at ranks >=6; the remaining differences are x^t-y^t with x>y>1, and the constant -416/5^t increases. This frontier is NOT a new exact-DFT bound. The 18-stage raw crossing is approximately 0.003624213737156872.

Tensor products multiply moments and direct sums add them. Completing a target r to r+d adds paid cost d^t, changing the margin by (r+d)^t-r^t-d^t<=0. Splitting paid ranks also cannot improve the margin. Those standard operations alone do not repair a failing invoice. This is not a DFT complexity lower bound.

## Even free binary splits of every helper are insufficient

Allow every rank-r helper to become at most two independent positive-rank targets summing to r, for free, with no feasibility constraint. Keep paid calls fixed. Concavity maximizes each reward at floor(r/2),ceil(r/2). Even that optimistic profile has an all-N maximum at 4+5, in (-57.791338532039077506,-57.791338532039077505). Exact positive/negative adjacent increments plus discrete concavity prove the global maximum.

Three pieces are not excluded: freely splitting all helpers into <=3 balanced parts gives a positive relaxed margin at 11+11. In the still-optimistic model where all helpers are already bisected and only rank-9 helpers can be promoted from 4+5 to 3+3+3, 291 promotions still fail globally; 292 give a positive margin at 6+6. None of these relaxed splits is claimed feasible.

## Reproduce

```
python3 research/delta005/refine.py --rounds 64 --budget 120
python3 research/delta005/continuation/verify.py --native research/delta005/out/refined-word.json.gz
python3 -O research/delta005/continuation/verify.py --native research/delta005/out/refined-word.json.gz
python3 research/delta005/continuation/frontier.py
python3 -O research/delta005/continuation/frontier.py
```

The obstruction checker encloses r^(199/200) by integer 200th-root comparisons at 30 decimal places. Newton and binary root implementations must agree. The frontier checker uses rational logarithm and exponential series with explicit remainder bounds. No floating value decides acceptance. The quantified concavity argument is written mathematics, not a Lean proof.

Other local searches included broader cut spaces, historical caches, paid-stop combinations, rerouting, zero-helper relaxations, chart alpha-expansion, and new one-dimensional neighbouring charts. Their negative results are bounded searches, not global optimality certificates.

Attribution: preserve PR6934's full lineage, Ali Romman's split mechanism, the original frame/compiler authors, Jacob Sussman, Halit Ziya Kartal, and OpenAI's exact-DFT model. Concavity and integer-root methods are classical. No priority claim, global circuit optimum, or delta=0.005 result is made.
