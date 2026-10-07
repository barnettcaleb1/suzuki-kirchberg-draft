# Conditional Lean verification

The exact final theorem is `Suzuki.fullTheoremConditional : PublishedInputs → Target.MainClaim` (with the printed universe/category parameters). The conditional proof compiles. The exact theorem and its hypotheses passed an independent conditional manuscript/source review. The exact review targets and package checks are recorded in `status.json`; the manuscript remains a research draft.

Published results are explicit parameters, never hidden global axioms. The intended actual-KK realization is a remaining external obligation. The kernel audit checks proof dependencies; the separate hypothesis review checks that the new manuscript contributions are not assumed by an interface. Neither review is an implementation of the published analytic theory.

## Published-input ledger

The full signatures, including every nested field and exact quantifier, are printed in `conditional-hypotheses.txt`. `external-inputs.json` supplies precise source versions, local snapshot hashes, uses and correspondence obligations. The groups below summarize those entries.

### `kk`

Actual separable possibly nonunital complex C*-algebras in carrier universe u are assigned objects of a preadditive category K with object universe v and Hom universe w. Actual nonunital star maps give KK classes, preserving identity/composition. K is intended to consist of designated separable actual KK objects, so all-Z quantifiers include no nonadmissible objects.

Source: Meyer math/0702145v2 §§4.1–4.3; Rosenberg–Schochet Duke 55(2) (1987), Theorem 1.11, within recorded scope.

Used in `ActualCoefficientKK.mapIso`, `ConditionalMainConstruction`, `FullTheoremConditional`.

### `extension`

Nuclearity permanence for actual c0 matrix sums, suspension, exact extensions and external unitization. Surjective star map with separable nuclear quotient admits CPC right inverse. For every separable nuclear B, original exact RFD extension of S(B) by c0 finite matrices. For every separable semisplit exact extension I→H→Q, the literal pointwise map Cone(theta)→S(Q) is KK invertible; double suspension is Bott equivalent. For every nuclear separable F, actual unitization inclusion has split retraction and reduced idempotent 1-[eta∘epsilon].

Source: Dadarlat January 2002 author PDF, Lemma 2.4 pp.2–3 and construction (11) p.8; no later K*(A)=0 assumption. Blackadar operator revision 8 February 2017 IV.3.1 and IV.3.2.4–5. Choi–Effros 1976 Theorem 3.10. Meyer v2 §4.2 Definition 55/Theorem 56 and preceding Bott statement; RS Theorem 1.11.

Used in `CoefficientModelFromExtension.coefficient_model`, `ConditionalMainConstruction.coefficientIso`, `ActualCoefficientKK.ScalarTensorInput.splitting`.

### `spatial`, `finiteTensor`

Actual unital spatial/minimal tensor algebra with bounded bilinear pure map, dense pure span, actual functorial star maps, matrix tensor isomorphisms, commuting factor embeddings. Literal finite block and coefficient matrix tensor coordinates match every pure matrix entry. MaximalOn specifies the full universal extension for any pair of commuting factor maps.

Source: Blackadar operator revision 8 February 2017 II.9 (minimal/maximal tensors); Blackadar K-Theory second edition §§17.8,18.9; Meyer v2 §4.1.

Used in `TensorCoefficientChannels.tensor_isFullAmalgam`, `ActualGraphCoefficientSystem`, `ActualInitialProjection`.

### `analytic`

For every finite rank-two strictly positive adjacency with diagonal ≥2 and positive corner weights: ordinary scalar graph corner is Kirchberg. Generic positive-size matrix simplicity, finite-matrix maximality, tensor and injective-limit separability/nuclearity, proper closed-ideal quotient realization, standard positive cuts and unstabilized Cuntz/hereditary projection transfer, tensor preservation of a jointly faithful matrix representation family. Every nuclear coefficient satisfies minimal=maximal. These laws name no constructed sequence, bond, projection, or limit.

Source: KPR February 1998 author PDF Corollary 3.11; Ara–Goodearl 1102.4296v2 Remark 3.10; Blackadar operator revision 8 February 2017 II.8.2,II.9,IV.3.1 and Cuntz comparison passages; APT 2009 Theorem 2.13, Lemma 2.16, Proposition 2.17, Lemmas 2.18/2.19.

Used in `GraphCoefficientLimit.limit_kirchberg`, `ActualFiniteCoefficientLimits.limit_properties`, `ActualAmalgamCorner.corner_hasFiniteAmalgam`.

### `finiteNuclear`

Every finite product of complex full matrix algebras, including zero-size blocks, has the exact CPC finite-matrix approximation predicate; no positive block-size hypothesis is required by this generic input.

Source: Blackadar operator revision 8 February 2017 IV.3.1; ordinary finite-dimensional nuclearity (explicit matching to Target CPAP).

Used in `ActualFiniteCoefficientLimits.scalar_nuclear`, `ActualAmalgamCorner.finiteConstituent`.

### `tensorKK`, `scalarTensor`

Universal exterior products on separable nonunital KK objects: identity, composition, bilinearity and classes of orthogonal actual maps. Actual tensor algebra equivalences bind this SAME Spatial tensor to the exterior tensor, natural for all actual factor maps. Actual ULift scalar unit constraints are natural for every KK morphism. No local scalar classes, transport, or bond equation is supplied.

Source: Meyer v2 §4.1 minimal-tensor monoidal constraints and §4.2 split exactness; Blackadar K-Theory second edition §§17.8,18.9.

Used in `ActualCoefficientKK.SpatialKKInput.phi_class`, `ActualCoefficientKK.ActualBond.bond_class`, `ActualUnitKK.referenceTransport`.

### `matrix`, `morita`

Every specified rank-one corner a↦a e_rr of a positive-size finite matrix algebra over a separable algebra is KK invertible; finite matrix separability. Actual inclusion of every norm-closed full projection corner of a separable nuclear unital algebra is KK invertible. No construction projection, noise map, limit or equivalence is given.

Source: Blackadar K-Theory second edition 17.8.2(c),17.8.5–6; Meyer v2 §§4.1–4.2; RS Theorem 1.11 stabilization/Morita within nuclear scope.

Used in `ActualCoefficientKK.UniverseCone.Input.noise_zero`, `ActualKKCornerClassification.classifyCorner`.

### `kGroups`, `finiteK0`, `ranks`

Ordinary graded K-theory functor on actual KK classes. Finite complex matrix products have K0 equal to integer rank vectors; all actual finite multiplicity maps act by their multiplicity matrices. Ordinary projection ranks are additive, stable and natural for every finite map.

Source: Blackadar K-Theory second edition §§5.1–5.5 and 17.5; Meyer v2 §4.3.

Used in `ActualCoefficientKK.UniverseCone.Input.scalar_class`, `ActualUnitKK.commonMinimal_coordinate`.

### `graphUCT`, `finiteCone`, `coneProjection`

UCT Hom classification for bootstrap/free scalar sources only. Every positive finite actual full [I I]/[I A] presentation is bootstrap and has K0 coker(B), K1 ker(B), with universally natural comparison under all compatible actual nonunital finite diagrams. Pair classes use left minus right and K1 boundary (-y,y). Every first-factor projection maps under SAME comparison to the cokernel class of its ordinary rank vector. No individual new channel action or prescribed projection sign is assumed.

Source: Fima–Germain 1510.02418v3, 27 December 2016, Theorem 4.1 p.20; RS 1987 Theorem 1.17 and Proposition 7.1; Drinen–Tomforde math/0103036v1 Theorem 3.1 for ordinary graph group convention; ordinary finite-cone exactness and K0 normalization.

Used in `ActualCoefficientKK.UniverseCone.Input.kappa`, `ActualCoefficientKK.ActualBond.bond_class`, `ActualUnitKK.stageZero_projection_prescribed`.

### `reference`, `referenceGenerator`

Actual C⊕SC is bootstrap with even/odd groups Z and actual first-summand endomorphism acting identity on even and zero on odd. Its actual scalar inclusion is the chosen even generator.

Source: Blackadar K-Theory second edition §§5.1–5.5,17.5; Meyer v2 §§4.2–4.3; RS scalar/suspension/bootstrap closure.

Used in `ActualCoefficientKK.ReferenceInput.projection_class`, `ActualUnitKK.referenceK0`, `ActualUnitKK.stageZero_scalar`.

### `projection`, `projectionInterpretation`, `representable`, `projectionExterior`, `projectionRepresentatives`

For every actual unital algebra ordinary K0 projection laws, same-size Grothendieck representatives, orthogonal addition, stabilization, finite block/matrix Morita and exterior naturality. For every separable actual A: K0(A) ≃ KK(C,A), natural for all KK classes; literal projection z↦z p gives its K0 class. Ordinary K0 exterior product agrees with the SAME normalized Kasparov exterior product. No prescribed target class or signed graph/common projection is a field.

Source: Blackadar K-Theory second edition §§5.1–5.5,17.5.4–17.5.6,17.8,18.9; Meyer v2 §§4.1/4.3.

Used in `ActualUnitKK.prescribedRepresentatives`, `ActualUnitKK.referenceTransport`, `ActualUnitKK.stageZero_projection_prescribed`.

### `milnor`

For every actual injective sequential system with separable nuclear stages and actual completed limit/canonical maps, analytic Milnor product-boundary sequence for every designated admissible KK test object Z: coboundary descent, kernel exactness and surjectivity onto compatible families. Suspension denotes actual degree-one shift. Stage and limit objects/maps are fixed by actual constructions; no limit equivalence or idempotent conclusion is supplied.

Source: RS Duke 55(2) (1987), Theorems 1.12 and 1.14(b), pp.436–437; frozen extracted excerpts only, complete original journal PDF not inspected.

Used in `ConditionalMainConstruction.graphMilnor`, `ConditionalKKTransport.limitIso`, `Suzuki.fullTheoremConditional`.

### `classification`

Any two actual unital separable nuclear nonzero simple purely infinite algebras, with invertible even KK class carrying literal scalar unit class to literal scalar unit class, are unital complex star isomorphic. Exact Target hypotheses are supplied for both algebras by the proof.

Source: Phillips funct-an/9506010v2, 18 December 1997, Corollary 4.2.2 p.42.

Used in `ActualKKCornerClassification.classifyCorner`, `Suzuki.fullTheoremConditional`.

## End-to-end derivation

`ConditionalMainConstruction` chooses only the original published extension and derives F, nuclearity/RFD, its actual cone/Bott equivalence to B, E=unitization(F), and its separating schedule. Generic projection representatives supply p,q for the pulled-back target unit. Their scalar augmentation vanishes by the actual split-unitization maps.

The recursive positive finite diagrams give actual graph channels. `ActualCoefficientKK` applies the universal finite-cone law to the SAME actual graphStage.{u}, including the amplified noise presentation. Literal restrictions and the proved finite actions derive +/−/0 classes. Exterior products bind to the SAME spatial tensor maps and their orthogonal sum gives the actual reduced idempotent. `system_bond` proves dependent successor transport, and `fullTheoremConditional` rewrites the actual system step to that map.

Actual evaluation paths prove the product limit simple/purely infinite and finite constituents simple/stably finite. Standard nuclear/limit support supplies nuclearity/separability. `ActualAmalgamCorner` proves the completed full-amalgam property and corner properties. `ActualInitialProjection.limit_projection` equates the exact corner projection with the actual stage-zero tensor projection.

`ActualUnitKK.stageZero_projection_prescribed` uses the SAME κ as the bond calculation. Universal finite rank normalization gives the scalar signs; representability and exterior naturality give the full tensor class, with zero residual. The final proof instantiates analytic Milnor on the exact separable nuclear injective system, obtains the limit equivalence and inverse restrictions, then transports the calculated projection class. Its final equivalence carries the corner unit to the target unit. Full-corner Morita and the exact unit-preserving classification input give `HasFiniteAmalgam B`.

There is no target/coefficient UCT, trace-existence input, assumed final presentation, or desired unit/bond equation in the final parameters. Stable finiteness uses a proved evaluation/matrix-limit route rather than the manuscript's trace route.

## Remaining external dependencies

Realize the documented category, object/class maps, ordinary K-theory, spatial tensor, suspension, scalar generators and published universal laws in actual separable Kasparov KK. In particular, the finite-cone comparison and signs, actual pointwise coefficient-cone quotient map, rank-one/full-corner Morita classes, Milnor all-Z formulation, and exact Target predicate conventions must have the correspondences described in the ledger. These are standard external synthesis obligations, not discarded hypotheses or kernel axioms. Relevant passages were inspected within recorded access limits; no complete original RS journal-PDF inspection or actual-KK Lean instance is claimed.

Independent human review and novelty assessment remain pending. The manuscript is a draft. Verification is conditional; no unconditional formalization is claimed. The included status and review records describe the local proof checkpoint before this GitHub publication, and their historical publication fields are retained as evidence of that checkpoint.
