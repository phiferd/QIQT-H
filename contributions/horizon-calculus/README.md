# Independent entropy guards and horizon-calculus pilot

This isolated contribution preserves the upstream QIQT-H tree unchanged. It is an
independent Mathlib-only verification package, **not a build or repair of the
upstream gravity stack** and not a formalization of Einstein's equations.

## Contents and verified scope

- `UniformHeatGuard.lean`: exact finite Shannon/KL definitions, separately
  namespaced, prove that normalized `H(p)+KL(p||uniform)` is constant. The audited
  upstream `hK` premise therefore forces zero contracted flux in this setting.
- `NonuniformHeatWitness.lean`: a positive normalized sine family with nonuniform
  reference has actual nonzero heat derivative `log(2)/6`; the KL derivative at
  the reference is zero. This repairs finite algebra only, not geometry/capacity.
- `HorizonCalculus.lean`: actual dilation differentiation, derived compact-domain
  domination, integration by parts, and nonzero bounded-interval sign controls.
- `HalfLineCalculus.lean`: compact-support lift to the entire negative half-line;
  fixed support for every parameter, actual integrability, and no condition at
  zero because the weighted boundary term vanishes.
- `CompactWitness.lean`: `f(u)=u*chi(u)` for a mathlib smooth bump centered at -2,
  inner radius 1/4 and outer radius 1/2. Proves smoothness, compact support,
  `f'(-2)=1`, and strictly negative weighted energy. Both pairing conventions
  and unconditional opposite-sign rejection are checked. The bump is
  library-defined, not an asserted elementary closed-form formula.
- `manuscript/`: contributor-review TeX and rendered PDF, **not submitted**.
  Authorship, disclosure, archival and licensing decisions remain for review.
- `logs/`: fresh package-build output and theorem-axiom checks.

With `sigma_plus(g,h)=integral(g*h'-h*g')` and dilation `exp(c*t)`, the derivative
of `sigma_plus(D_t f,f)` is `2*c*integral(u*(f')^2)`. The KPV opposite pairing
flips this sign while keeping the same dilation. This is a convention-sensitive
calculus statement, not a quantum relative-entropy or geometry identification.

## Reproduction and dependency boundary

This package pins **Lean v4.30.0-rc2** and Mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`, with transitive versions recorded in
`lake-manifest.json`. From this directory, with elan available:

```sh
lake exe cache get
lake build
./check-axioms.sh
```

The recorded build used already-cached dependencies at these revisions and fresh
local outputs for all five contribution modules. No upstream theorem imports
are required. A clean network download is not claimed to have been retested.
The checked declarations depend only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, or custom axiom is used.

**Do not mix compiled artifacts with upstream:** the audited upstream package
pins Lean v4.30.0 and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Compatibility with that separate environment has not been tested. No `.olean`
files or local dependency symlinks are distributed here.

PDF reproduction (Tectonic 0.17.0 used for the recorded rendering):

```sh
tectonic --untrusted --keep-logs manuscript/horizon-calculus.tex
```

The four-page PDF was visually checked; its long identifiers and bibliography
were formatted to avoid overflow. This is not human peer review.

## Attribution and rights

Upstream project: Pawel Kaplanski's [QIQT-H](https://github.com/kaplan196883/QIQT-H),
audited at `0313e288c7ab3d3868c73ccdc6a68242efc0214a`. The two short definitions in
`UniformHeatGuard.lean` are attributed to `lean/mathlib/QIQTH/BranchLedger.lean:40`
and `RelEntPositivity.lean:78`. The guard concerns the combination of the uniform
reference and `hK` in `QiqtGrComplete.lean`; it does not establish a Lean kernel
bug or refute the original physics paper. Full upstream files are not recopied
into this contribution directory.

Mathlib and its authors supply the analysis infrastructure and smooth bump.
The manuscript identifies the Dorau-Much and Kurpicz-Pinamonti-Verch sources and
distinguishes their conventions. Work was directed by Dan Phifer with AI-assisted
implementation and separate AI-assisted recompilation/review, not human peer
review or upstream endorsement.

At the audited commit, GitHub reports no repository license and no repository-wide
LICENSE/COPYING/NOTICE file was found. Some upstream files have individual license
headers, which remain intact. This native GitHub fork does **not** grant a blanket
license to upstream material or assert permission for off-GitHub redistribution.
No new license is assigned to upstream by these additions. Resolve any additional
reuse/publication rights before an external archive or submission.
