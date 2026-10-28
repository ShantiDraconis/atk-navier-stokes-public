import Mathlib

namespace MPrivate.NS.ThirdCoefficient

/-!
# ThirdCoefficientFrontier

A typed status register for the current Navier--Stokes ThirdCoefficient route.
This file intentionally carries no proof of the open PDE bridges.  It exists so
that proved algebra, rigorous no-go results, and unresolved analytic obligations
cannot be conflated.
-/

inductive FrontierStatus where
  | provedLogic
  | formalRefuted
  | openBridge
  | conditional
  | external
  deriving DecidableEq, Repr

structure FrontierItem where
  name : String
  status : FrontierStatus
  statementClass : String
  dependsOn : List String
  note : String
  deriving Repr

/-- Current T3/T4c frontier after the signed decomposition, Bony/LP scalar
composition, scaling, viscosity and non-circularity audits. -/
def currentThirdCoefficientFrontier : List FrontierItem := [
  { name := "signed_decomposition",
    status := .provedLogic,
    statementClass := "algebra",
    dependsOn := [],
    note := "signed decomposition algebra is retained without declaring the actual PDE block estimates proved" },
  { name := "T2_state_dependent_scaling_spec",
    status := .provedLogic,
    statementClass := "specification",
    dependsOn := [],
    note := "a3(scale lambda u,t)=lambda^2 a3(u,lambda^2 t); actual candidate still must discharge this spec" },
  { name := "viscosity_margin_algebra",
    status := .provedLogic,
    statementClass := "algebra",
    dependsOn := ["nonnegative epsilon expenditures", "strict total margin"],
    note := "strict total absorption below nu leaves positive surviving viscosity" },
  { name := "fixed_dimensional_cutoff",
    status := .formalRefuted,
    statementClass := "scaling no-go",
    dependsOn := [],
    note := "a nonzero fixed R0 cannot be NS scale covariant" },
  { name := "data_dependent_cutoff_homogeneity",
    status := .provedLogic,
    statementClass := "scaling algebra",
    dependsOn := ["cutoff_degree_plus_one", "budget_degree_zero"],
    note := "R^2 times invariant amplitude has degree +2 when the stated scaling hypotheses hold" },
  { name := "positive_constant_low_budget",
    status := .formalRefuted,
    statementClass := "T4 no-go",
    dependsOn := [],
    note := "constant positive aLow gives linear-in-time integral and no uniform initial-data-only budget" },
  { name := "low_absorption_from_upper_Bernstein_only",
    status := .formalRefuted,
    statementClass := "logical insufficiency",
    dependsOn := [],
    note := "Zlow<=R^2Ylow and Vlow<=R^2Ylow do not imply Vlow<=eps Zlow" },
  { name := "low_direct_absorption_actual_NS",
    status := .openBridge,
    statementClass := "PDE estimate",
    dependsOn := ["additional signed cancellation or lower dissipation control"],
    note := "needed only if choosing the reduced aLow=0 route" },
  { name := "low_three_component_budget_route",
    status := .conditional,
    statementClass := "T4 alternative",
    dependsOn := ["low pointwise coefficient", "low spacetime budget"],
    note := "if low direct absorption is unavailable, low remains an explicit third coefficient with its own budget" },
  { name := "bony_scalar_square_control_composition",
    status := .provedLogic,
    statementClass := "scalar algebra",
    dependsOn := ["bony factor bound", "low velocity square control", "low vorticity energy control"],
    note := "verified composition only; does not assert the actual NS/Bony factor estimate" },
  { name := "actual_NS_bony_holder_factor",
    status := .openBridge,
    statementClass := "PDE/LP estimate",
    dependsOn := ["actual Bony decomposition", "Holder/Bernstein", "projector and shell controls"],
    note := "must derive the concrete factor estimate from the real Navier--Stokes blocks" },
  { name := "cross_young_absorption",
    status := .provedLogic,
    statementClass := "algebra",
    dependsOn := ["Vcross<=x*b", "x^2<=Z"],
    note := "Vcross<=eps Z+b^2/(4eps) once the representation is actually supplied" },
  { name := "cross_exact_ratio_candidate",
    status := .formalRefuted,
    statementClass := "circularity diagnostic",
    dependsOn := [],
    note := "defining aCross by dividing the Young remainder by Y violates the no-Y-denominator rule" },
  { name := "cross_independent_factorization",
    status := .openBridge,
    statementClass := "PDE/spectral estimate",
    dependsOn := ["actual_NS_bony_holder_factor", "cross spectral representation"],
    note := "must factor the Young remainder as C aCross Y without Y in the denominator" },
  { name := "cross_spacetime_budget",
    status := .openBridge,
    statementClass := "T4c analytic estimate",
    dependsOn := ["cross_independent_factorization"],
    note := "integrability of aCross must be scale invariant, uniform below Tstar and non-circular" },
  { name := "cross_energy_multiplier_route",
    status := .conditional,
    statementClass := "T4c reduction",
    dependsOn := ["degree-one initial multiplier", "pointwise coefficient-to-energy-density reduction"],
    note := "scalar implication is proved; construction of the actual multiplier remains open" },
  { name := "alignment_scaling",
    status := .provedLogic,
    statementClass := "scaling algebra",
    dependsOn := ["critical amplitude", "dimensionless defect"],
    note := "Acrit*D retains degree +2 under the stated scaling hypotheses" },
  { name := "alignment_uniform_positive_defect_escape",
    status := .formalRefuted,
    statementClass := "barrier diagnostic",
    dependsOn := [],
    note := "if D>=c>0 then Acrit*D still dominates the old amplitude barrier" },
  { name := "alignment_signed_factorization",
    status := .openBridge,
    statementClass := "geometric PDE estimate",
    dependsOn := ["joint direction/strain defect", "principal-value kernel control"],
    note := "must prove Valign<=C Acrit D Y with a genuinely useful defect" },
  { name := "alignment_spacetime_budget",
    status := .openBridge,
    statementClass := "T4c analytic estimate",
    dependsOn := ["alignment_signed_factorization"],
    note := "integrability of Acrit*D must be proved independently of target regularity" },
  { name := "T3_reduced_assembly",
    status := .conditional,
    statementClass := "assembly theorem",
    dependsOn := ["low_direct_absorption_actual_NS", "cross_independent_factorization", "alignment_signed_factorization"],
    note := "algebraic assembly is proved once analytic subgates are supplied" },
  { name := "T3_three_component_assembly",
    status := .conditional,
    statementClass := "assembly theorem",
    dependsOn := ["low coefficient estimate", "cross_independent_factorization", "alignment_signed_factorization"],
    note := "retains aLow when direct low absorption is not certified" },
  { name := "T4c_reduced_assembly",
    status := .conditional,
    statementClass := "budget assembly",
    dependsOn := ["certified low elimination", "cross_spacetime_budget", "alignment_spacetime_budget"],
    note := "two-component budget is valid only after independent certification that low contributes no time coefficient" },
  { name := "T4c_three_component_assembly",
    status := .conditional,
    statementClass := "budget assembly",
    dependsOn := ["low spacetime budget", "cross_spacetime_budget", "alignment_spacetime_budget"],
    note := "default honest route when low elimination is unavailable" },
  { name := "T4c_maximal_time_passage",
    status := .openBridge,
    statementClass := "measure-theoretic passage",
    dependsOn := ["uniform budgets for every T<Tstar", "measurability/integrability"],
    note := "finite-time estimates must pass to the maximal interval without inserting Tstar into the budget" },
  { name := "G1_flex_from_T3_T4",
    status := .conditional,
    statementClass := "differential inequality",
    dependsOn := ["exact enstrophy balance", "one certified T3 route", "T4c_maximal_time_passage", "strict viscosity margin"],
    note := "downstream algebra is proved; ActualNS to the analytic premises remains open" }
]

/-- Count only entries explicitly marked as open bridges. -/
def openBridgeCount : Nat :=
  (currentThirdCoefficientFrontier.filter (fun x => x.status == .openBridge)).length

/-- Count rigorous refutations/no-go certificates separately from open bridges. -/
def formalRefutedCount : Nat :=
  (currentThirdCoefficientFrontier.filter (fun x => x.status == .formalRefuted)).length

end MPrivate.NS.ThirdCoefficient
