# Hodge Core Deep-Blocker Plan

## Scope
This note tracks the five remaining theorem-level `sorry`s on the analytic RR path:
- `HodgeTheory/HodgeDecomposition/Core.lean`
  - `dbarRealTransitionFactor_contMDiffAt_hd`
  - `hodge_decomposition_01`
  - `exact_harmonic01_vanishes`
  - `closed_exactPair_commonPotential`
- `HodgeTheory/HodgeDecomposition/DimensionGenus.lean`
  - `finrank_harmonic10_eq_genus`

The objective is to close these using reusable infrastructure (no placeholder defs,
no statement weakening, no wrapper-smuggling). De Rham/additive packaging now lives
in `HodgeTheory/HodgeDecomposition/DeRhamCore.lean`, so this note keeps
`Core.lean`-specific blockers separate from de Rham-quotient plumbing.

## Current baseline (2026-03-03)
- Build frontier passes warning-only:
  - `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition`
  - `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
- File-size check passes:
  - `scripts/check_lean_file_length.sh 2000`
  - `HodgeTheory/HodgeDecomposition/Core.lean` is 1845 lines.
- Fixed-chart transition-factor wrapper and inverse-overlap transport lemmas are now
  split into `HodgeTheory/HodgeDecomposition/TransitionFactorGlue.lean`, keeping
  Core focused on the remaining deep theorem-level blockers.

## Dependency Flow (high level)
1. Gate A:
   selector-independent `dbar_real_hd` smoothness closure.
2. Gate B:
   Hodge decomposition existence for `(0,1)`.
3. Gate C:
   exact-harmonic vanishing and common-potential compatibility.
4. Gate D/F:
   finrank/genus identities feeding Dolbeault and RR terminal statements.

## Blocker A: `dbarRealTransitionFactor_contMDiffAt_hd`
### Current issue
- The current target is formulated via moving selector data:
  `p ↦ chartAt ℂ p` inside derivative/evaluation.
- On `RiemannSphere` this selector-dependent factor has a proven non-smoothness
  diagnostic at `0`, so an unconditional theorem in that exact shape is not viable.

### Practical closure route
1. Shift the universal theorem target to a selector-independent object:
   fixed chart pair `e, e'` overlap formulas, then glue.
2. Reuse existing fixed-chart infrastructure in
   `Infrastructure/TransitionFactor.lean`:
   `chartTransitionFactorByCharts_contMDiffAt`,
   `chartTransitionByCharts_contMDiffAt`,
   overlap nonvanishing lemmas.
3. Prove local-to-global assembly for `dbarRealSectionCandidate_hd` using
   chart-indexed overlap identities rather than moving-selector derivatives.

### Lean micro-targets
- A chart-indexed version of `dbar_real_hd_smooth_section` with explicit
  overlap hypotheses.
- A gluing lemma that depends only on atlas compatibility, not on
  `ChartAtLocallyConstant`.

## Blocker B: `hodge_decomposition_01`
### Mathematical route
- Build decomposition as projection onto harmonic subspace plus exact part.
- Formalize in two reusable stages:
  1. existence of harmonic representative modulo `im(∂̄)`,
  2. exactness witness via `dbar_real_hd`.

### Lean micro-targets
- A helper that packages "closed class has harmonic representative" in the
  `Form_01` / quotient model already used by
  `InnerProductAndDolbeault.lean`.
- A helper that reconstructs the representative-level equality
  `ω = ω_harm + dbar_real_hd f` from quotient equality.

## Blocker C1: `exact_harmonic01_vanishes`
### Mathematical route
- Standard Hodge orthogonality/energy identity:
  if `∂̄f` is harmonic and exact, then its harmonic component is zero.

### Lean micro-targets
- A reusable "exact harmonic class is zero" lemma at the sheaf/Dolbeault bridge
  level.
- A transfer lemma from class-level zero to form-level zero for `dbar_real_hd f`.

## Blocker C2: `closed_exactPair_commonPotential`
### Mathematical route
- For closed pair `(ω10, ω01)` with componentwise exact primitives `(f10, f01)`,
  show potential difference has harmonic exact derivatives, then use vanishing.

### Lean micro-targets
- Lemma: from `dbar_10 ω10 + del_01 ω01 = 0` and component exactness, derive
  harmonicity constraints on primitive differences.
- Lemma: apply `exact_harmonic01_vanishes` (and conjugate mirror) to conclude
  primitive difference is constant, then build common potential.

### Current reduction status (2026-03-03)
- Compile-checked in `HodgeTheory/HodgeDecomposition/ExactPair.lean`:
  - `exactPair_commonPotential_of_closed_of_mixed_and_exact_harmonic01_vanishes`
    (proves common-potential compatibility from two hypotheses:
    exact-harmonic `(0,1)` vanishing + mixed identity `dbar_10 (del_real f) + del_01 (dbar_real_hd f) = 0`).
- Compile-checked in `HodgeTheory/HodgeDecomposition/DeRhamBridge.lean`:
  - `harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_mixed_and_exact_harmonic01_vanishes`
    (surjectivity criterion routed through the new `ExactPair` lemma).
  - `closed_exactPair_commonPotential_of_mixed_and_exact_harmonic01_vanishes`
    (direct common-potential bridge under `hmixed + hvanish01`).
  - `harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_mixed_and_exact_harmonic01_vanishes`
    and `hodge_isomorphism_of_mixed_and_exact_harmonic01_vanishes`
    (full de Rham bijectivity/isomorphism packaging under the same pair of hypotheses).
- Compile-checked chart-stabilized mixed identity (in `Core.lean`):
  - `dbar_10_del_real_add_del_01_dbar_real_hd_eq_zero_of_chartAtLocallyConstant`.
- Compile-checked pointwise mixed-identity localization (new module
  `HodgeTheory/HodgeDecomposition/MixedIdentity.lean`):
  - `dbar_10_del_real_add_del_01_dbar_real_hd_toSection_eq_zero_of_chartAt_eventuallyEq`.
  - `dbar_10_del_real_add_del_01_dbar_real_hd_toSection_eq_zero_riemannSphere_coe_of_ne_zero`.
  together with chart-selection infrastructure
  `ChartSelection.chartAt_eventuallyEq_center_riemannSphere_coe_of_ne_zero`.
- Compile-checked chart-stabilized common-potential/de Rham packages:
  - `ExactPair.exactPair_commonPotential_of_closed_of_chartAtLocallyConstant_and_exact_harmonic01_vanishes`.
  - `DeRhamBridge.harmonicPairToDeRham_surjective_of_hodgeDecomposition_and_chartAtLocallyConstant_and_exact_harmonic01_vanishes`.
  - `DeRhamBridge.harmonicPairToDeRham_bijective_of_hodgeDecomposition_and_chartAtLocallyConstant_and_exact_harmonic01_vanishes`.
  - `DeRhamBridge.hodge_isomorphism_of_chartAtLocallyConstant_and_exact_harmonic01_vanishes`.
- Remaining closure gap for core theorem:
  - promote/prove the mixed identity without chart-selection stabilization
  assumptions, then instantiate the reduced theorem to discharge
  `Core.closed_exactPair_commonPotential` unconditionally.
  In the explicit sphere selector, this is now localized to the `0` chart-switch point.

## Blocker D: `finrank_harmonic10_eq_genus`
### Current reality
- The proof currently has only an injective-family package; this is a lower-bound
  style interface, not a direct finrank equality proof.

### Closure route
1. Build finite-dimensional rank bridge through the de Rham/Hodge equivalence path.
2. Connect harmonic `(1,0)` rank to topological genus via the established
   de Rham dimension package (ultimately `2g` split into `(1,0)` and `(0,1)`).
3. Keep this in `DimensionGenus.lean` so `Core.lean` remains under the file-size cap.

## Compile frontier for this plan
- `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.HodgeDecomposition`
- `lake build StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.DolbeaultCohomology`
- `lake build StringGeometry.RiemannSurfaces.Analytic.RiemannRoch`
