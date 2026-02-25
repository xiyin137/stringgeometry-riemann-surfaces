# stringgeometry-riemann-surfaces

Split from https://github.com/xiyin137/StringGeometry.

## Build

    git clone <this-repo-url>
    cd stringgeometry-riemann-surfaces
    lake build

## Notes

- Lean module namespace remains under StringGeometry.* to minimize import churn.
- This repository was generated with:
  ./scripts/factorization/extract_component_repo.sh riemann-surfaces <output_dir>
