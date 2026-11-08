# Mathematical note: paired two-chain DFT candidate

Date: 8 November 2026. Status: partial formalization; the all-length DFT bound
is an open theorem. This note documents the available extracted package and
newly checked work. The unavailable original PDF has not been silently treated
as a read or verified source.

## Exact target

For `δ = 3363623/1000000000`, the intended conclusion is existence of the
original exact scalar/index RAM programs and their cost function satisfying
`DFTProgram` and `W(n) = O(n (log n)^(1-δ))`. All positive lengths, canonical
roots, scalar preparation, indexing, storage and operation costs remain in
that trusted definition.

The local `FFTChainDFT.Target` is this proposition. No theorem inhabits it.

## Universal paired normalizer

Let `P` be precomposition by an involution `σ` on an arbitrary index type.
The two inputs are independent complex arrays `x,y`. Define ordinary maps

- `D(x,y)=(x,Py)`;
- `H(x,y)=(x+y,x-y)`;
- `H⁻¹(x,y)=((x+y)/2,(x-y)/2)`.

Chronologically apply `D,H⁻¹,D,H`. Their composite `Λ` is

```
Λ(x,y) = ((x+Px-y+Py)/2, (x-Px+y+Py)/2).
```

Lean proves `Λ²(x,y)=(Px,Py)` without restrictions on `x,y`. If a complex
linear map `Q` has `Q²=P`, it commutes with `P` and with `Λ`. Consequently
`(ΛQ)²=I`. Also `Q⁴=I`, so its inverse is its cube; the separate theorem
`transported_inverse_query_involution` proves exactly `(ΛQ⁻¹)²=I`.

These are universal array equalities. They do not charge physical RAM
instructions, prove an in-place implementation, or identify a concrete
`matAct` query. Those bridges remain separate obligations.

## Finite reconstruction and histogram

The baseline owned772 word is pinned by its upstream commit and decompressed
payload SHA256. Edit A moves helper 732's read of register 771 to frame 117,
including three earlier pre-reads. Edit B retains reader 451's operand in an
unused lifetime of owned register 794, and removes the root's frame-737 stop.
The patterns are guarded against exact source events.

The reconstructed word has 22,836 events, 29 owned register labels, 32 owned
lifetimes and peak occupancy 14. Its Python sparse coordinate replay verifies
799 endpoint rows (638,401 coefficients), including every public helper input.
The paid native histogram is

```
1:2216  2:456  3:496  4:98  5:165  6:8  7:9  8:1
```

and the helper target histogram is

```
1:14  2:8  3:4  4:107  5:14  6:2  7:9  8:19  9:385.
```

The raw DreamingOfClouds 9+9 controller has 1,237 events on 20 roles, including
62 complex normalizer macros. Each non-normalizer event is copied onto two
independent arrays. Each normalizer macro is replaced by four rational array
gates, so the paired word has `2(1237-62)+4·62 = 2598` macros on 40 roles.

The exact rational symbolic interpreter retains a separate variable for every
stage, and reduces only `q⁴=1`. It verifies all 1,600 endpoint matrix entries:
each role receives `q⁻¹` times its declared stage monomial of its own original
input, with no cross-copy dependence. This is a Python algebraic certificate
conditional on the native interface, not a Lean live-kernel certificate.

Counting native invocations, thin queries and whole idles in the literal word,
and the stage support of the endpoint roles, recovers

```
productive count = 24392       paid count = 128116
productive rank mass = 336224  paid rank mass = 334704.
```

The raw controller's stored ambient dimension is 153; the proposed normalized
DFT geometry has dimension `1+18·8=145`. The geometry change needs its own
formal construction. Copying the raw metadata is not sufficient.

## Formal moment inequality

Let `T,P` be the asserted target and paid rank multisets, with multiplicities,
and let `M_t(A)=Σ_(r∈A) r^t`. Set `C=420453/125000000` and `t=1-C`.
`MomentAnalytic.lean` proves `M_t(P)<M_t(T)` over the reals.

The certificate generator only proposes rational endpoints. Lean proves the
log endpoints through positive exponential series: a 40-term lower series
certifies each log upper bound; a 16-term upper series after division by 16
certifies each log lower bound. For each rank it then proves bounds on
`r^(1-C)=r/exp(C log r)` using an 8-term series and its proved remainder.
All numerical comparisons are checked by `norm_num`, through kernel proof
terms. No Python result is imported as an axiom.

The resulting lower bound for the raw moment gap is approximately
`0.00005160947256`. It is intentionally a little wider than the independent
Python receipt's interval

```
51611111215192/10^18 < gap < 51611111215193/10^18.
```

The latter tighter inclusion is only a Python certificate; the Lean proof
uses its own independently replayed endpoints.

The following real inequalities are proved in Lean:

```
M_t(P) ≤ (1-10⁻¹⁰) M_t(T)
334704 ≤ (499/500) 12^C M_t(T)
24392·13 ≤ (19/20) 12^C M_t(T).
```

Sussman's inventory-level strictification theorem applies with `v=12800`,
cutoff `J=12^v`, floor `L=13^v`, and tail exponent `u=C`. A Bernoulli estimate
and the exact power comparisons `(499/500)^400 ≤ 1/2`, `(19/20)^80 ≤ 1/2`
prove the tail budget. Lean proves the completed/split moment inequality,
`J<L`, and `L≤145^v`. The analytic multiset counts are proved equal
to the original histogram functions at every natural rank; the completion
floor is attained for every tensor power. This does not construct a certified unit for the tensor
engine.

Finally, Lean verifies the exact rational gaps

```
C - η = η - δ = 1/2000000000,
η = 6727247/2000000000,
δ = 3363623/1000000000.
```

## Missing implication

The completed analytic results have the form “these histograms have sufficient
moment surplus.” The missing input is a concrete physical program whose
`GLiveKernelM` and cost contracts realize those histograms. Without it, the
moment theorem cannot instantiate `TensorEng.BU.tensor_engine` and yields no
DFT complexity bound. The all-length Fourier compiler must then be rebuilt at
the new symbolic exponent. Reusing its older final theorem is insufficient.
