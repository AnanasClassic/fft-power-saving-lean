# Exact DFT bound: construction and proof map

Target saving: δ = 3363623/1000000000. The source exports `Race.bound` in
`Submission/Chain/Bound.lean`, using the unchanged `OAI.PowerSaving.DFTProgram`.
Verification status is recorded separately in the audit report. A source theorem
is not, by itself, evidence that Lean or the official comparator accepted it.

The three named ZIP/PDF attachments were unavailable. This work instead uses the
preserved extracted package and an explicitly identified reconstruction of the
finite word. Its SHA256 differs from the digest quoted in the unavailable note.
The proof concerns this reconstruction; it does not assert recovery of that file.

## Finite program

The native word has 22,836 events, 104 main ports, 562 productive helper slots
and 29 owned scratch labels. Two local edits are transplanted into the pinned
owned772 word: DreamingOfClouds' helper-732 scheduling change and Ali Romman's
retention of reader 451's operand. The latter uses an available lifetime of
register 794 in this reconstruction. The changed middle row state rejoins the
baseline after the second edited chunk. The KLW checker, its soundness theorem,
exact labels, scalar certificates and frame semantics prove the all-width native
supplier contract; no Python replay is a premise of that contract.

The paired controller has 2,598 literal instructions on forty main roles. It is
the two-array lowering of DreamingOfClouds' 9+9 controller: eighteen logical
native sites become thirty-six physical native invocations. Each has a separate
bank of 562 live helper inputs. The shared supplier-owned scratch is reused.
There are also six allocated query scratch registers per port; overwrite makes
reuse independent of the previous contents.

Let H = Fin 9 and let A be the new label type of dimension 145 = 1+18·8. Its
pivot axis and eighteen disjoint eight-axis increments realize the stage
geometry. For every orthogonal gauge g, port t and main role i, the target is
the pivot together with the increments in `Schedule.targetStages i`. Its rank is
1+8 times the number of these stages. The target stage lists are proved nodup.

The live roles are

    (Γ × (Fin 40 × Fin 104)) ⊕ (Γ × (Fin 36 × Fin 562)),

where Γ is the finite nonempty type of orthogonal gauges on A. The remaining
roles are supplier-owned and query scratch. All embeddings are proved injective.

## Two-array normalizer and physical endpoint

For arbitrary independent complex arrays x,y and an involutive permutation P,
put D(x,y)=(x,Py), H(x,y)=(x+y,x-y), and
H⁻¹(x,y)=((x+y)/2,(x-y)/2). Chronologically applying D,H⁻¹,D,H gives

    Λ(x,y) = ((x+Px-y+Py)/2, (x-Px+y+Py)/2).

The universal identities are Λ² = P I₂ and, for the transported query Q with
Q²=P, (ΛQ⁻¹)²=I₂. The phase calculation gives Q⁻¹=Q³. The physical normalizer
and transported-query files construct proper GWords, prove their actual actions
at every tensor width and every input array, and prove their recursive costs
(zero for Λ; two rank-one calls for the transported square). The scalar endpoint
certificate alone is not used as a substitute for these physical operations.

`RawCompiler` realizes each literal opcode as a proper GWord. It proves the main
view and the complete action on every helper bank, on arbitrary data. The bank
trace is exactly Fin.range 36; each bank is called once. The raw main endpoint is
q³ times the specified stage monomial of that main role's own original input.
The helper endpoint is its native residual applied to its own original input.

For each helper bank the inherited fresh-frame lemma supplies free pre/post
adapters turning that native residual into the required block target. The
adapters act on helper roles only, so they preserve the main endpoint. A final
free main shift by pivot plus target correction turns the raw q³ endpoint into
the target block matrix. These composed actual words establish `wordCert`,
including the trusted `MX.GLiveKernelM` contract. Its proof works on arbitrary
input arrays, stronger than the contract's zero-on-scratch premise.

“Free” here refers only to recursive block cost. The words still contain their
finite local matrix/shift instructions. The inherited tensor/RAM compiler counts
these ordinary operations and their scalar, integer, address and storage work.

## Exact invoice and live-target counts

Per gauge the recursive price is

    36·nativePrice(φ) + 104·(6φ(1) + Σ[j=1..8] 4φ(8j)).

The proof first prices the actual literal schedule, then uses indicator price
lists to recover its histogram at every natural rank. The productive histogram
is obtained by counting the actual main roles and all thirty-six helper banks.
No role multiplicity is discarded.

| Quantity per gauge | Value |
|---|---:|
| Productive roles | 24,392 |
| Paid recursive calls | 128,116 |
| Productive rank mass | 336,224 |
| Paid rank mass | 334,704 |

Every productive rank lies in [1,145]; paid ranks are at most 64. The main roles
include 208 targets of rank 145 and enough rank-one targets for the tensor floor.
`Finite.rawCert_exists` combines the actual word, independent target families,
properness, live contract and both complete histograms. It imports no final
asymptotic bound to establish this finite witness.

## Moment, tensor and all-length reduction

Use C=0.003363624=420453/125000000 and t=1-C. Rational log/exp enclosures prove
real power bounds at every nonzero histogram rank. They yield the strict finite
moment inequality and the ratios α≤1−10⁻¹⁰, γ≤499/500, and completion≤19/20.
These inequalities are Lean theorems; the generating Python arithmetic is only
an independently reproducible certificate generator.

Sussman's strictification is instantiated at v=12800, paid cutoff J=12^v and
completion floor L=13^v. The proof establishes 0<J<L≤145^v, nonempty live roles,
the proper paid-rank restrictions, attainment of L and the strictified moment
bound. Common gauge multiplicity scales the moments by the same nonnegative
factor and does not weaken the comparison. The actual finite witness then
instantiates the generic mixed tensor engine, at saving
η=0.0033636235=6727247/2000000000. Both gaps C−η and η−δ equal 1/2000000000.

The copied all-length Fourier reduction is re-instantiated at this new engine
and η. It retains OpenAI's root-order selection, scalar preparation, integer and
address bounds, polynomial storage, convolution reduction and operation-count
model. Its Big-O transfer uses η>δ to absorb the reduction overhead. The final
`Race.bound` projects the exact δ Big-O estimate from this new all-length theorem;
it does not import a prior final DFT bound with a weaker hardcoded saving.

## Attribution and independent checking

OpenAI supplies the original exact DFT model and Fourier reduction. Jacob
Sussman supplies the generic engines, tensor/live-kernel infrastructure and
reduction integration. Halit Ziya KARTAL supplies the preceding Lean
instantiations and adaptation patterns. DreamingOfClouds supplies the two-chain
controller and prior circuit work; Ali Romman supplies local circuit/controller
optimizations. CubeJerry/Jerry Chen, Cinna Davis and the contributors named in
retained source notices supply inherited constructions and certificates. The
source report pins the commits and distinguishes this integration from that
inherited work. Kernel acceptance alone does not establish novelty or priority.

The final audit must distinguish Python certificates, Lean elaboration, Lean
kernel acceptance, permitted axioms, official Comparator acceptance, nanoda
replay, and the competition's public Lean Verified label. A private test-only
preflight does not grant that label. Publication and issue submission require
separate explicit authorization.
