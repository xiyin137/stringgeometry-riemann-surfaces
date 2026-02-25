import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Harmonic
import StringGeometry.RiemannSurfaces.Analytic.Applications.GreenFunction
import StringGeometry.RiemannSurfaces.Analytic.Moduli
import StringGeometry.RiemannSurfaces.Analytic.Jacobian.AbelJacobi
import StringGeometry.RiemannSurfaces.Analytic.Jacobian.ThetaFunctions
import StringGeometry.RiemannSurfaces.Analytic.HodgeTheory.Helpers.HarmonicHelpers
import StringGeometry.RiemannSurfaces.Analytic.Applications.Helpers.GreenHelpers
import StringGeometry.RiemannSurfaces.Analytic.Jacobian.Helpers.ThetaHelpers

/-!
# Analytic Theory of Riemann Surfaces

This module collects the analytic (PDE and complex analysis) aspects of
Riemann surface theory:

- Harmonic functions and potential theory
- Green's functions and the Dirichlet problem
- Teichmüller theory and quasiconformal maps
- Weil-Petersson geometry
- Abel-Jacobi map and period matrices
- Theta functions

These tools are essential for:
1. Computing period matrices
2. Integrating over moduli space
3. Understanding the analytic structure of M_g
4. Explicit constructions via theta functions (Jacobi inversion)
-/
