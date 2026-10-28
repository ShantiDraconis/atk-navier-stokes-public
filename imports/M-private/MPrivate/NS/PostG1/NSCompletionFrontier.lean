import Mathlib
import MPrivate.NS.PostG1.G2HighFrequencyInterface
import MPrivate.NS.PostG1.G3FixedScaleReconstruction
import MPrivate.NS.PostG1.DirectCriticalReconstruction
import MPrivate.NS.PostG1.G4ESSInterface

namespace MPrivate.NS.PostG1

/-!
# NSCompletionFrontier

Typed metadata register for the path after G1-flex. This prevents a local
ThirdCoefficient success from being mislabeled as global regularity.

Important: the list below is a dependency ledger only.  A `.conditional`,
`.openBridge`, or even `.provedLogic` tag is not a proof of the corresponding
analytic theorem.  Proof-producing objects must live in the imported modules
and discharge their explicit frontiers.

Identity-continuity rule for all future gates: every arrow must transport the
same actual solution, maximal interval, viscosity, cutoff where applicable,
concrete norm/coefficient and concrete time integral.  Scaling agreement,
pointwise scalar proxies, finite truncations, profile surrogates, or downstream
endpoint bounds are never substitutes for an identification theorem.

Two post-G1 reconstruction routes are kept distinct:

* DIRECT: uniform enstrophy + energy + Sobolev/interpolation -> uniform L3;
* LP: G2 high-frequency + fixed-scale low-frequency reconstruction -> uniform L3.

The direct route is shorter whenever G1 genuinely yields uniform enstrophy.
-/

inductive NSGateStatus where
  | provedLogic
  | openBridge
  | conditional
  | externalPending
  | notEstablished
  deriving DecidableEq, Repr

structure NSGate where
  name : String
  status : NSGateStatus
  dependencies : List String
  note : String
  deriving Repr

/-- Current logical frontier with alternative reconstruction paths explicit. -/
def currentNSCompletionFrontier : List NSGate := [
  { name := "ActualNS_Bony_cross_bridge",
    status := .openBridge,
    dependencies := ["actual_Bony_decomposition", "same_T3_cross_coefficient", "actual_low_Linf_identification", "cross_representation", "dissipative_factor", "square_control"],
    note := "scalar algebra is insufficient; UL must be the same actual low L-infinity factor used by T3, not a pointwise-field or norm proxy substitution" },
  { name := "T4_cross_budget",
    status := .openBridge,
    dependencies := ["ActualNS_Bony_cross_bridge", "same_aCross_as_T3", "same_solution_interval_viscosity_cutoff", "same_concrete_time_integral", "L1_t_low_velocity_square_budget", "initial_data_only", "scale_invariant"],
    note := "scaling or a profile/shell surrogate does not identify the T3 cross coefficient; no supY, Z/Y, BKM/LPS, endpoint reuse, or future target data" },
  { name := "LOW_route",
    status := .openBridge,
    dependencies := ["valid_low_estimate_on_R3 OR independent_low_L1_budget", "same_low_block_as_T3", "same_cutoff", "same_viscosity"],
    note := "generic reverse low-pass Poincare is rejected; finite shell algebra or low-profile scaling alone is not a low-elimination certificate" },
  { name := "ALIGNMENT_route",
    status := .openBridge,
    dependencies := ["signed_alignment_factorization", "same_alignment_coefficient_as_T3", "alignment_T4_budget", "same_solution_interval_viscosity"],
    note := "pointwise and temporal alignment obligations remain independent and must target the same T3 coefficient" },
  { name := "G1_flex",
    status := .openBridge,
    dependencies := ["ActualNS_Bony_cross_bridge", "T4_cross_budget", "LOW_route", "ALIGNMENT_route", "strict_viscosity_margin", "same_actual_enstrophy_balance"],
    note := "primary analytic bottleneck; no post-G1 reconstruction or endpoint theorem may be used to establish any upstream component" },
  { name := "DIRECT_uniform_L3",
    status := .conditional,
    dependencies := ["G1_flex", "same_actual_solution", "energy_uniform_L2", "homogeneous_Sobolev_interpolation", "grad_u_vorticity_identification", "actual_L3_norm", "essSup_mapping"],
    note := "preferred shorter path if G1 gives a genuine uniform enstrophy bound; scalar norm proxies are insufficient" },
  { name := "G2_fixed_scale_high_frequency",
    status := .openBridge,
    dependencies := ["G1_flex", "same_actual_solution_and_interval", "concrete_kernel_or_LP_theorem", "prior_data_cutoff", "uniform_shell_sum"],
    note := "alternative LP route; interface/status metadata is not a kernel proof and G2 cannot be reused upstream" },
  { name := "G3_fixed_scale_critical_reconstruction",
    status := .conditional,
    dependencies := ["G2_fixed_scale_high_frequency", "low_frequency_energy_bound", "same_solution", "same_interval", "same_viscosity", "same_cutoff", "same_exact_critical_space"],
    note := "alternative LP route once both actual pieces and reconstruction are rigorous; downstream-only" },
  { name := "UNIFORM_L3_ENDPOINT_INPUT",
    status := .conditional,
    dependencies := ["DIRECT_uniform_L3 OR G3_fixed_scale_critical_reconstruction", "same_actual_solution", "actual_L3_norm", "same_maximal_interval", "maximal_interval_uniformity"],
    note := "recognized critical endpoint input; scalar proxies, different norms, or different intervals are insufficient" },
  { name := "G4_ESS_hypothesis_mapping",
    status := .externalPending,
    dependencies := ["UNIFORM_L3_ENDPOINT_INPUT", "same_G3_or_DIRECT_solution", "same_actual_L3_bound", "same_maximal_interval", "ESSMappingHolds", "pinned_external_statement", "pinned_reference"],
    note := "strictly downstream: every exact external endpoint hypothesis must be proved and ESS cannot be recycled to establish G1/T3/T4/cross/G3" },
  { name := "exclude_finite_Tstar",
    status := .conditional,
    dependencies := ["G4_ESS_hypothesis_mapping", "externally_certified_continuation", "same_actual_maximal_lifespan"],
    note := "endpoint continuation consequence only after exact mapping and external theorem application" },
  { name := "global_regularity",
    status := .notEstablished,
    dependencies := ["G1_flex", "one certified L3 reconstruction path", "G4_ESS_hypothesis_mapping", "exclude_finite_Tstar", "identity_continuity_across_entire_DAG"],
    note := "must not be created as a final theorem before every dependency and every identity-continuity guard is certified" }
]

end MPrivate.NS.PostG1
