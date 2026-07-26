#!/usr/bin/env python3
"""Build Archon/PhyX-compatible JSONL inputs for the 2026 IPhO papers.

The source PDFs and page renders live under ``ipho_2026_source``.  This script
does not OCR the papers at build time: the small-question statements and the
official final results below are curated from the official English papers and
solutions, while every row retains links to the original PDF and a page image.
"""

from __future__ import annotations

import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "ipho_2026_source"
RAW = SOURCE / "raw"
IMAGE = SOURCE / "image"
PROCESSED = SOURCE / "processed"
REVIEW = SOURCE / "review"

HIPHO_REFERENCE = (
    ROOT
    / "hipho_ipho_2024_2025"
    / "hipho_ipho_2024_2025_archon.jsonl"
)

ARCHON_SCHEMA_FIELDS = (
    "index",
    "category",
    "source_dataset",
    "source_dataset_url",
    "year",
    "problem_id",
    "problem_number",
    "part_id",
    "part_letter",
    "subquestion_number",
    "formalization_input_policy",
    "context",
    "current_question",
    "question",
    "answer",
    "answers",
    "marking",
    "answer_type",
    "unit",
    "points",
    "modality",
    "field",
    "source",
    "previous_parts",
    "previous_part_count",
    "images",
    "image",
    "image_count",
    "raw_hipho_image_question",
)

FIELD_BY_CONTEXT = {
    "T1-A": "Fluid Mechanics",
    "T1-B": "Classical Mechanics and Electromagnetism",
    "T1-C": "Atomic and Molecular Physics",
    "T2-A": "Optics",
    "T2-B": "Optics",
    "T2-C": "Optics",
    "T3-A": "Electromagnetism",
    "T3-B": "Thermodynamics and Electromagnetism",
    "T3-C": "Thermodynamics and Electromagnetism",
    "E1-A": "Experimental Thermodynamics",
    "E1-B": "Experimental Thermodynamics",
    "E1-C": "Experimental Thermal Physics",
}

ANSWER_TYPE_BY_KIND = {
    "theory": "Expression or Numerical Value",
    "experiment-derived": "Expression or Numerical Value",
    "measurement": "Experimental Measurement",
    "graphing": "Graph",
}


SOURCE_URLS = {
    "theory_general_instructions.pdf": (
        "https://cdn.phoxiv.org/olympiads/ipho/2026/"
        "theory_general_instructions.pdf"
    ),
    "T1_problem.pdf": "https://cdn.phoxiv.org/olympiads/ipho/2026/T1/problem.pdf",
    "T1_solution.pdf": "https://cdn.phoxiv.org/olympiads/ipho/2026/T1/solution.pdf",
    "T1_marking_scheme.pdf": (
        "https://cdn.phoxiv.org/olympiads/ipho/2026/T1/marking_scheme.pdf"
    ),
    "T2_problem.pdf": "https://cdn.phoxiv.org/olympiads/ipho/2026/T2/problem.pdf",
    "T2_solution.pdf": "https://cdn.phoxiv.org/olympiads/ipho/2026/T2/solution.pdf",
    "T2_marking_scheme.pdf": (
        "https://cdn.phoxiv.org/olympiads/ipho/2026/T2/marking_scheme.pdf"
    ),
    "T3_problem.pdf": "https://cdn.phoxiv.org/olympiads/ipho/2026/T3/problem.pdf",
    "T3_solution.pdf": "https://cdn.phoxiv.org/olympiads/ipho/2026/T3/solution.pdf",
    "T3_marking_scheme.pdf": (
        "https://cdn.phoxiv.org/olympiads/ipho/2026/T3/marking_scheme.pdf"
    ),
    "E1_problem.pdf": "https://cdn.phoxiv.org/olympiads/ipho/2026/E1/problem.pdf",
    "E1_solution.pdf": "https://cdn.phoxiv.org/olympiads/ipho/2026/E1/solution.pdf",
}


CONTEXT = {
    "T1-A": """
Two water reservoirs are separated by a vertical wall MN.  A square slot of
vertical size a*sqrt(2)/2 is sealed by a fully submerged solid cube of side a
and density 3*rho_0, where rho_0 is the density of water.  The cube is hinged
frictionlessly at O and may rotate about an axis perpendicular to the figure.
The maximum permitted difference in water levels is Delta h = 1.41 m.  Use
Figure 1a on the source page for the exact geometry and lever arms.
""",
    "T1-B": """
At one instant a positron and an electron, each of mass m and charges of equal
magnitude and opposite sign, are separated by 100*a_0.  Their velocities are
antiparallel and perpendicular to their separation.  Each particle has angular
momentum of magnitude mu*hbar about the center of mass.  The system is isolated,
classical, non-relativistic, and has only electrostatic interaction.  The Bohr
radius is a_0 = 4*pi*epsilon_0*hbar^2/(m*e^2), and k = 1/(4*pi*epsilon_0).
""",
    "T1-C": """
A photon of angular frequency omega is absorbed by an ozone molecule O3 at rest,
dissociating it into O2 and O.  Let U_i and U_f be the ground-state energies of
O3 and O2 and define Delta U = U_f - U_i.  The outgoing O2 momentum makes angle
theta with the incident photon.  Treat the oxygen fragments classically and
non-relativistically, take the mass of an oxygen atom to be m, and use photon
momentum p_gamma = E_gamma/c = hbar*omega/c.
""",
    "T2-A": """
Parallel rays strike the inside of a half-cylindrical mirror of radius R.  For
an incident ray with transverse coordinate x, let N be its number of
reflections.  The positive threshold x_N is the largest distance from the
optical axis for which a ray undergoes at most N reflections.  Use Figures
2c--2e for the mirror and limiting-ray geometry.
""",
    "T2-B": """
A half-cylindrical mirror of radius R illuminates a fully absorbing cylindrical
container of radius a.  Their axes are parallel, and the container center lies
R/2 from the mirror center on the symmetry plane.  Uniform parallel sunlight
arrives along the optical axis.  Any ray absorbed by the container reflects at
most once.  Let theta_max be the largest incidence angle on the mirror among
rays that strike the container, and let P_0 be the power the cylinder would
receive without the mirror.  See Figure 2f.
""",
    "T2-C": """
For the half-cylindrical mirror of radius R, ray A is incident at angle theta
and its reflected line is y = m_A*x + b_A.  A neighboring parallel ray B is
incident at theta + Delta theta, with Delta theta much smaller than theta, and
its reflected line is y = m_B*x + b_B.  The envelope/intersection of neighboring
rays forms the caustic.  Use Figure 2g and its coordinate convention.
""",
    "T3-A": """
A homogeneous isotropic paramagnetic torus has mean radius R, inner radius r
with r << R, volume V, and cross-sectional area A.  An insulated conducting
wire is wound densely around it with N turns and instantaneous current I.
Fields H and B and magnetization M are approximately uniform in the torus.
Use B = mu_0*H + mu_0*M, Ampere's law, and the sign convention that work and
heat entering the paramagnetic torus are positive.
""",
    "T3-B": """
Continue with the paramagnetic torus.  Its equation of state is T*M*V = n*K*H,
its heat capacity at constant M is C_M = n*lambda/T^2, and dU = C_M*dT.
The volume is fixed and the magnetic work on the material is
dW = mu_0*V*H*dM.  Work and heat entering the torus are positive.
""",
    "T3-C": """
The paramagnetic torus executes the Carnot refrigeration cycle
1 -> 2 -> 3 -> 4 -> 1 shown in Figure 3b in the H-versus-T plane.  T_h and T_c
are the hot- and cold-reservoir temperatures; Q_h is the magnitude of heat
delivered to the hot reservoir and Q_c is the magnitude absorbed from the cold
reservoir.  The equation of state is T*M*V = n*K*H and the isothermal heat
relation from part B may be reused.
""",
    "E1-A": """
The experimental apparatus contains a sealed air column (CA) in the inner
cylinder.  Propylene glycol is introduced to h = 4.5 cm so the air volume is
fixed.  Use the cylinder dimensions in Figure 17, ambient air density
rho_a = 1.12 kg/m^3, and the ideal-gas law P*V = n*R*T.  The outer-cylinder
water bath is heated while pressure and temperature are recorded.
""",
    "E1-B": """
The inner cylinder contains dry air plus water vapor at total pressure
approximately P_atm.  The water level is adjusted and its height H is recorded
as temperature T falls.  At T_0 = 273.15 K, extrapolated height is H_0 and the
water vapor pressure may be taken as zero.  Vapor pressure obeys
ln(P_v/P_v0) = -(Q_v/R)*(1/T - 1/T_0).  Use the experimental procedure and
geometry on pages 11--12.
""",
    "E1-C": """
Water in the inner and outer cylinders exchanges heat radially through an
acrylic cylindrical wall.  Record T_IC and T_OC versus time.  The heat-flow
model is dQ/dt = (T_OC - T_IC)/R_Th.  For radial Fourier conduction,
dQ/dt = -lambda*A*dT/dr.  Ignore apparatus heat capacity where instructed and
use the dimensions in Figure 17.
""",
}


def p(
    part_id: str,
    *,
    problem_id: str,
    context: str,
    points: float,
    page: int,
    printed_page: int,
    question: str,
    answer: str,
    dependencies: tuple[str, ...] = (),
    kind: str = "theory",
    formalization_ready: bool = True,
    extra_pages: tuple[int, ...] = (),
) -> dict[str, Any]:
    paper = problem_id.rsplit("_", 1)[-1].upper()
    return {
        "part_id": part_id,
        "problem_id": problem_id,
        "context_key": context,
        "points": points,
        "paper": paper,
        "page": page,
        "printed_page": printed_page,
        "current_question": question.strip(),
        "answer": answer.strip(),
        "dependencies": list(dependencies),
        "kind": kind,
        "formalization_ready": formalization_ready,
        "extra_pages": list(extra_pages),
    }


THEORY_PARTS = [
    p(
        "T1-A1",
        problem_id="ipho_2026_t1",
        context="T1-A",
        points=3.0,
        page=1,
        printed_page=4,
        question="Calculate the side length a that makes Delta h = 1.41 m the maximum permissible water-level difference.",
        answer="a = Delta h/(2*sqrt(2)) = 0.50 m.",
    ),
    p(
        "T1-B1",
        problem_id="ipho_2026_t1",
        context="T1-B",
        points=1.0,
        page=2,
        printed_page=5,
        question="For mu = 4 the pair is bound. Find the maximum electron-positron separation in units of a_0.",
        answer="r_max = (1600/9)*a_0.",
    ),
    p(
        "T1-B2",
        problem_id="ipho_2026_t1",
        context="T1-B",
        points=2.5,
        page=2,
        printed_page=5,
        question="For mu = 15/2 the pair is unbound. Find the angle between the asymptotic relative velocity u_infinity and the initial positron line of motion.",
        answer="The signed deflection is -16.60 degrees, i.e. 16.60 degrees below the initial line of motion.",
    ),
    p(
        "T1-C1",
        problem_id="ipho_2026_t1",
        context="T1-C",
        points=2.5,
        page=3,
        printed_page=6,
        question="Determine the minimum angular frequency omega_min required for dissociation at outgoing O2 angle theta, in terms of hbar, c, theta, Delta U, and m.",
        answer=(
            "For theta <= pi/2, omega_min = "
            "3*m*c^2*[1 - sqrt(1 - (Delta U/(3*m*c^2))*(2*sin(theta)^2 + 1))]"
            "/[hbar*(2*sin(theta)^2 + 1)]. For theta >= pi/2 use the same "
            "threshold evaluated at theta = pi/2."
        ),
    ),
    p(
        "T1-C2",
        problem_id="ipho_2026_t1",
        context="T1-C",
        points=1.0,
        page=3,
        printed_page=6,
        question="For theta = pi/6, Delta U = 1.10 eV, and m = 16.0 amu, calculate hbar*omega_min - Delta U in eV.",
        answer="hbar*omega_min - Delta U = 2.03e-11 eV.",
        dependencies=("T1-C1",),
    ),
    p(
        "T2-A1",
        problem_id="ipho_2026_t2",
        context="T2-A",
        points=1.5,
        page=2,
        printed_page=8,
        question="Find the general expression for the threshold x_N in terms of R and the positive integer N.",
        answer="x_N = R*sin((2*N - 1)*pi/(4*N + 2)) = R*cos(pi/(2*N + 1)).",
        extra_pages=(1,),
    ),
    p(
        "T2-B1",
        problem_id="ipho_2026_t2",
        context="T2-B",
        points=2.0,
        page=3,
        printed_page=9,
        question="Given a = alpha*sin(theta_max) + beta*sin(2*theta_max), determine alpha and beta in terms of R.",
        answer="alpha = R and beta = -R/2.",
    ),
    p(
        "T2-B2",
        problem_id="ipho_2026_t2",
        context="T2-B",
        points=1.5,
        page=3,
        printed_page=9,
        question="Express the power ratio P/P_0 in terms of theta_max.",
        answer="P/P_0 = 1/(1 - cos(theta_max)).",
        dependencies=("T2-B1",),
    ),
    p(
        "T2-B3",
        problem_id="ipho_2026_t2",
        context="T2-B",
        points=0.5,
        page=3,
        printed_page=9,
        question="For R = 1.0 m, find a such that P = 5*P_0, and report it in cm.",
        answer="cos(theta_max) = 4/5 and a = 0.12 m = 12 cm.",
        dependencies=("T2-B1", "T2-B2"),
    ),
    p(
        "T2-C1",
        problem_id="ipho_2026_t2",
        context="T2-C",
        points=0.5,
        page=4,
        printed_page=10,
        question="Write the slope m_A and intercept b_A of reflected ray A in terms of theta and R.",
        answer="m_A = cot(2*theta), and b_A = R/(2*cos(theta)).",
    ),
    p(
        "T2-C2",
        problem_id="ipho_2026_t2",
        context="T2-C",
        points=2.0,
        page=4,
        printed_page=10,
        question="Expand m_B and b_B to first order in Delta theta.",
        answer=(
            "m_B = cot(2*theta) - 2*csc(2*theta)^2*Delta theta; "
            "b_B = [R/(2*cos(theta))]*(1 + tan(theta)*Delta theta), "
            "up to O(Delta theta^2)."
        ),
        dependencies=("T2-C1",),
    ),
    p(
        "T2-C3",
        problem_id="ipho_2026_t2",
        context="T2-C",
        points=1.0,
        page=4,
        printed_page=10,
        question="Find the limiting intersection coordinates (X_c,Y_c) of the neighboring reflected rays.",
        answer="X_c = R*sin(theta)^3; Y_c = (R/2)*cos(theta)*(2 - cos(2*theta)).",
        dependencies=("T2-C1", "T2-C2"),
    ),
    p(
        "T2-C4",
        problem_id="ipho_2026_t2",
        context="T2-C",
        points=1.0,
        page=4,
        printed_page=10,
        question="For theta << 1, put the caustic in the form Y_c = v*|X_c|^(p/q) + u. Determine u, v, and the integers p,q.",
        answer="u = R/2, v = (3/4)*R^(1/3), p = 2, and q = 3.",
        dependencies=("T2-C3",),
    ),
    p(
        "T3-A1",
        problem_id="ipho_2026_t3",
        context="T3-A",
        points=0.2,
        page=2,
        printed_page=12,
        question="Write the field magnitude H inside the torus in terms of N, I, A, and V.",
        answer="H = N*I*A/V.",
        extra_pages=(1,),
    ),
    p(
        "T3-A2",
        problem_id="ipho_2026_t3",
        context="T3-A",
        points=0.6,
        page=2,
        printed_page=12,
        question="Find the work dW_emf performed by the external voltage source when B changes by dB.",
        answer="dW_emf = V*H*dB.",
        dependencies=("T3-A1",),
        extra_pages=(1,),
    ),
    p(
        "T3-A3",
        problem_id="ipho_2026_t3",
        context="T3-A",
        points=0.2,
        page=2,
        printed_page=12,
        question="Subtract the vacuum-core contribution and write the work dW done on the paramagnetic material.",
        answer="dW = mu_0*V*H*dM.",
        dependencies=("T3-A2",),
        extra_pages=(1,),
    ),
    p(
        "T3-B1",
        problem_id="ipho_2026_t3",
        context="T3-B",
        points=1.5,
        page=3,
        printed_page=13,
        question="At fixed temperature T, H changes from H_i to H_f. Find the heat Q transferred into the torus.",
        answer="Q = -(mu_0*n*K/(2*T))*(H_f^2 - H_i^2).",
        dependencies=("T3-A3",),
        extra_pages=(2,),
    ),
    p(
        "T3-B2",
        problem_id="ipho_2026_t3",
        context="T3-B",
        points=1.5,
        page=3,
        printed_page=13,
        question="For an adiabatic change H_i -> H_f starting at T_i, determine Delta T = T_f - T_i.",
        answer=(
            "Delta T = T_i*[sqrt((lambda + mu_0*K*H_f^2)/"
            "(lambda + mu_0*K*H_i^2)) - 1]."
        ),
        dependencies=("T3-A3",),
        extra_pages=(2,),
    ),
    p(
        "T3-C1",
        problem_id="ipho_2026_t3",
        context="T3-C",
        points=0.2,
        page=3,
        printed_page=13,
        question="Label T_h and T_c on Figure 3b and identify the processes on which Q_h and Q_c are transferred.",
        answer="States 1 and 4 lie at T_h; states 2 and 3 lie at T_c. Q_c is absorbed on 2->3, and Q_h is delivered on 4->1.",
        formalization_ready=False,
    ),
    p(
        "T3-C2",
        problem_id="ipho_2026_t3",
        context="T3-C",
        points=1.5,
        page=3,
        printed_page=13,
        question="Express M_1 in terms of M_2, M_3, and M_4.",
        answer="M_1 = sqrt(M_2^2 - M_3^2 + M_4^2), taking the nonnegative magnitude.",
        dependencies=("T3-B1", "T3-C1"),
    ),
    p(
        "T3-C3",
        problem_id="ipho_2026_t3",
        context="T3-C",
        points=0.8,
        page=4,
        printed_page=14,
        question="Using the supplied potassium-chromate and liquid-helium data, find the helium temperature after one cycle.",
        answer="Q_c = 1.29e-1 J, so |Delta T| = 9.92e-3 K and T_final = 0.99008 K.",
        dependencies=("T3-B1", "T3-C2"),
    ),
    p(
        "T3-C4",
        problem_id="ipho_2026_t3",
        context="T3-C",
        points=2.0,
        page=4,
        printed_page=14,
        question="A body of heat capacity C_c is cooled from T_0 to T while refrigerator input power P and hot-reservoir temperature T_h remain constant. Determine the elapsed time.",
        answer="t = (C_c*T_h/P)*[ln(T_0/T) - (T_0 - T)/T_h].",
    ),
    p(
        "T3-C5",
        problem_id="ipho_2026_t3",
        context="T3-C",
        points=1.5,
        page=4,
        printed_page=14,
        question="Determine the overall coefficient of performance COP = Q_c/W for all cycles up to the time found in C4.",
        answer="COP = [(T_h/(T_0 - T))*ln(T_0/T) - 1]^(-1).",
        dependencies=("T3-C4",),
    ),
]


EXPERIMENT_PARTS = [
    p(
        "E1-A1",
        problem_id="ipho_2026_e1",
        context="E1-A",
        points=0.4,
        page=9,
        printed_page=9,
        question="Determine the mass m, amount n, and number N of molecules in the confined air column.",
        answer="Official sample: m = 0.94 +/- 0.02 g, n = 3.24 mmol (reported uncertainty 0.7 mmol), N = (1.95 +/- 0.05)e21.",
        kind="experiment-derived",
    ),
    p(
        "E1-A2",
        problem_id="ipho_2026_e1",
        context="E1-A",
        points=1.0,
        page=9,
        printed_page=9,
        question="Record confined-air pressure P as a function of temperature T in a table.",
        answer="Measurement-dependent table; use the official solution data/graph as the archived reference.",
        kind="measurement",
        formalization_ready=False,
    ),
    p(
        "E1-A3",
        problem_id="ipho_2026_e1",
        context="E1-A",
        points=0.9,
        page=9,
        printed_page=9,
        question="Plot pressure as a function of temperature from A2.",
        answer="The expected isochoric ideal-gas plot is linear: P is proportional to absolute T.",
        dependencies=("E1-A2",),
        kind="graphing",
        formalization_ready=False,
    ),
    p(
        "E1-A4",
        problem_id="ipho_2026_e1",
        context="E1-A",
        points=1.0,
        page=9,
        printed_page=9,
        question="Use the graph from A3 to determine the experimental universal gas constant R.",
        answer="Official sample: R = 8.4 +/- 0.4 J/(mol*K).",
        dependencies=("E1-A1", "E1-A3"),
        kind="experiment-derived",
        formalization_ready=False,
    ),
    p(
        "E1-A5",
        problem_id="ipho_2026_e1",
        context="E1-A",
        points=0.7,
        page=9,
        printed_page=9,
        question="Determine the constant-volume thermal pressure coefficient beta_0 = (1/P_0)*(Delta P/Delta T).",
        answer="Official sample: beta_0 = 0.0034 +/- 0.0007 K^(-1); ideal-gas reference 1/273.15 K = 0.0037 K^(-1).",
        dependencies=("E1-A3",),
        kind="experiment-derived",
    ),
    p(
        "E1-B1",
        problem_id="ipho_2026_e1",
        context="E1-B",
        points=1.0,
        page=12,
        printed_page=12,
        question="Record liquid-free air-column height H as a function of temperature T.",
        answer="Measurement-dependent table; the official solution contains 20 sample (H,T,P_v) rows.",
        kind="measurement",
        formalization_ready=False,
        extra_pages=(11,),
    ),
    p(
        "E1-B2",
        problem_id="ipho_2026_e1",
        context="E1-B",
        points=1.0,
        page=12,
        printed_page=12,
        question="Plot H as a function of T using the B1 measurements.",
        answer="Measurement-dependent H(T) graph; approximately linear near room temperature.",
        dependencies=("E1-B1",),
        kind="graphing",
        formalization_ready=False,
        extra_pages=(11,),
    ),
    p(
        "E1-B3",
        problem_id="ipho_2026_e1",
        context="E1-B",
        points=0.5,
        page=12,
        printed_page=12,
        question="Extrapolate the B2 graph to determine H_0 at 0 degrees Celsius.",
        answer="Official sample: H_0 = 5.9 cm, corresponding to V_0 = 53.4 mL.",
        dependencies=("E1-B2",),
        kind="experiment-derived",
        formalization_ready=False,
        extra_pages=(11,),
    ),
    p(
        "E1-B4",
        problem_id="ipho_2026_e1",
        context="E1-B",
        points=1.0,
        page=12,
        printed_page=12,
        question="Assuming dry air plus water vapor and zero vapor pressure at T_0, express P_v using P_atm, H_0, H, T_0, and T.",
        answer="P_v = P_atm*[1 - (H_0*T)/(H*T_0)].",
        dependencies=("E1-B3",),
        kind="experiment-derived",
        extra_pages=(11,),
    ),
    p(
        "E1-B5",
        problem_id="ipho_2026_e1",
        context="E1-B",
        points=4.0,
        page=12,
        printed_page=12,
        question="Construct a Clausius-Clapeyron graph and use it to determine the molar latent heat Q_v.",
        answer="Plot ln(P_v/P_atm) against 1/T; official sample slope is -4700 +/- 200 K and Q_v = 39 +/- 2 kJ/mol.",
        dependencies=("E1-B1", "E1-B4"),
        kind="experiment-derived",
        formalization_ready=False,
        extra_pages=(11,),
    ),
    p(
        "E1-B6",
        problem_id="ipho_2026_e1",
        context="E1-B",
        points=0.5,
        page=12,
        printed_page=12,
        question="Convert Q_v into latent heat per unit mass L_v and state the formula.",
        answer="L_v = Q_v/M_0 = 2190 +/- 110 kJ/kg.",
        dependencies=("E1-B5",),
        kind="experiment-derived",
    ),
    p(
        "E1-C1",
        problem_id="ipho_2026_e1",
        context="E1-C",
        points=1.0,
        page=13,
        printed_page=13,
        question="Record T_IC and T_OC as functions of time t.",
        answer="Measurement-dependent table; the official solution supplies 15 sample rows from t=0 s to 840 s.",
        kind="measurement",
        formalization_ready=False,
        extra_pages=(12,),
    ),
    p(
        "E1-C2",
        problem_id="ipho_2026_e1",
        context="E1-C",
        points=1.0,
        page=13,
        printed_page=13,
        question="Plot T_IC(t) and T_OC(t) on one graph.",
        answer="Measurement-dependent graph: T_IC rises while T_OC falls toward equilibrium.",
        dependencies=("E1-C1",),
        kind="graphing",
        formalization_ready=False,
        extra_pages=(12,),
    ),
    p(
        "E1-C3",
        problem_id="ipho_2026_e1",
        context="E1-C",
        points=0.7,
        page=13,
        printed_page=13,
        question="On common axes plot T_OC-T_IC against T_OC and against T_IC.",
        answer="Two extrapolation lines intersect the zero temperature-difference axis at the equilibrium temperature.",
        dependencies=("E1-C1",),
        kind="graphing",
        formalization_ready=False,
        extra_pages=(12,),
    ),
    p(
        "E1-C4",
        problem_id="ipho_2026_e1",
        context="E1-C",
        points=1.1,
        page=13,
        printed_page=13,
        question="Use the C3 graph to determine the equilibrium temperature T_eq.",
        answer="Official sample: T_eq = 53 degrees Celsius.",
        dependencies=("E1-C3",),
        kind="experiment-derived",
        formalization_ready=False,
        extra_pages=(12,),
    ),
    p(
        "E1-C5",
        problem_id="ipho_2026_e1",
        context="E1-C",
        points=1.0,
        page=13,
        printed_page=13,
        question="Graph the finite-difference rate (T_IC,j-T_IC,j-1)/(t_j-t_j-1) against the corresponding average T_OC-T_IC.",
        answer="The graph is linear, with slope 1/(c_0*m*R_Th) under the stated model.",
        dependencies=("E1-C1",),
        kind="graphing",
        formalization_ready=False,
        extra_pages=(12,),
    ),
    p(
        "E1-C6",
        problem_id="ipho_2026_e1",
        context="E1-C",
        points=1.6,
        page=13,
        printed_page=13,
        question="Determine the effective wall thermal resistance R_Th from the C5 graph.",
        answer="R_Th = 1/(c_0*m*slope). Official sample: R_Th = 1.17 +/- 0.03 K/W.",
        dependencies=("E1-C5",),
        kind="experiment-derived",
    ),
    p(
        "E1-C7",
        problem_id="ipho_2026_e1",
        context="E1-C",
        points=1.6,
        page=14,
        printed_page=14,
        question="Combine the heat-flow relation and radial Fourier law to determine acrylic conductivity lambda.",
        answer="lambda = ln(r_2/r_1)/(2*pi*h*R_Th). Official sample: lambda = 0.25 +/- 0.01 W/(m*K).",
        dependencies=("E1-C6",),
        kind="experiment-derived",
        extra_pages=(13,),
    ),
]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def paper_file(paper: str, suffix: str) -> str:
    return f"{paper}_{suffix}.pdf"


def build_rows(parts: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_part = {part["part_id"]: part for part in parts}
    if len(by_part) != len(parts):
        raise ValueError("Duplicate part_id in curated IPhO data")

    rows: list[dict[str, Any]] = []
    for part in parts:
        paper = part["paper"]
        problem_pdf = paper_file(paper, "problem")
        solution_pdf = paper_file(paper, "solution")
        marking_pdf = (
            paper_file(paper, "marking_scheme") if paper.startswith("T") else None
        )
        image_name = f"{paper}_page-{part['page']}.png"
        image_names = [image_name] + [
            f"{paper}_page-{page}.png" for page in part["extra_pages"]
        ]

        required = [RAW / problem_pdf, RAW / solution_pdf]
        if marking_pdf:
            required.append(RAW / marking_pdf)
        required.extend(IMAGE / name for name in image_names)
        missing = [str(path) for path in required if not path.is_file()]
        if missing:
            raise FileNotFoundError("Missing IPhO source assets: " + ", ".join(missing))

        dependencies = []
        for dep_id in part["dependencies"]:
            if dep_id not in by_part:
                raise ValueError(f"{part['part_id']} references unknown dependency {dep_id}")
            dep = by_part[dep_id]
            dependencies.append(
                {
                    "source_id": f"ipho_2026_{dep_id.lower().replace('-', '_')}",
                    "part_id": dep_id,
                    "question": dep["current_question"],
                    "answer": dep["answer"],
                    "reusable_conclusions": [dep["answer"]],
                    "dependency_policy": (
                        "natural_language_prerequisite_only; the current target "
                        "and later answers must not be assumed"
                    ),
                }
            )

        index = f"ipho_2026_{part['part_id'].lower().replace('-', '_')}"
        source_lines = [
            "## Source",
            "LVI International Physics Olympiad, Bucaramanga, Colombia, 2026.",
            f"Official English paper: ../ipho_2026_source/raw/{problem_pdf}",
            f"Official solution: ../ipho_2026_source/raw/{solution_pdf}",
        ]
        if marking_pdf:
            source_lines.append(
                f"Official marking scheme: ../ipho_2026_source/raw/{marking_pdf}"
            )
        source_lines.extend(
            [
                f"Printed page: {part['printed_page']}; local PDF page: {part['page']}.",
                (
                    "The page PNG is primary visual evidence for formulas and figures; "
                    "the curated text below is provided for machine-readable routing."
                ),
                "",
                "## Physical scenario",
                CONTEXT[part["context_key"]].strip(),
                "",
                f"## Current subquestion {part['part_id']}",
                part["current_question"],
            ]
        )
        if dependencies:
            source_lines.extend(["", "## Reusable previous-part conclusions"])
            for dep in dependencies:
                source_lines.append(
                    f"- {dep['part_id']}: {dep['reusable_conclusions'][0]}"
                )
        source_lines.extend(
            [
                "",
                "## Dataset metadata",
                (
                    f"IPhO 2026; {paper}; {part['points']} points; "
                    f"kind={part['kind']}; "
                    f"formalization_ready={str(part['formalization_ready']).lower()}."
                ),
            ]
        )

        rows.append(
            {
                "id": index,
                "index": index,
                "source_index": part["part_id"],
                "problem_id": part["problem_id"],
                "part_id": part["part_id"],
                "question": "\n\n".join(source_lines).strip(),
                "current_question": part["current_question"],
                "shared_context": CONTEXT[part["context_key"]].strip(),
                "answer": part["answer"],
                "category": (
                    "IPhO 2026 Theory"
                    if paper.startswith("T")
                    else "IPhO 2026 Experiment"
                ),
                "dataset": "IPhO 2026 official English papers via phoXiv mirror",
                "dataset_format": "native",
                "points": part["points"],
                "paper": paper,
                "kind": part["kind"],
                "formalization_ready": part["formalization_ready"],
                "image": image_name,
                "images": image_names,
                "previous_parts": dependencies,
                "source_pdf": f"../ipho_2026_source/raw/{problem_pdf}",
                "source_page": part["page"],
                "printed_page": part["printed_page"],
                "solution_pdf": f"../ipho_2026_source/raw/{solution_pdf}",
                "marking_scheme_pdf": (
                    f"../ipho_2026_source/raw/{marking_pdf}"
                    if marking_pdf
                    else None
                ),
                "source_url": SOURCE_URLS[problem_pdf],
                "solution_url": SOURCE_URLS[solution_pdf],
            }
        )
    return rows


def canonical_identity(part: dict[str, Any]) -> dict[str, Any]:
    paper = str(part["paper"])
    local_part = str(part["part_id"]).split("-", 1)[1]
    part_letter = local_part[0]
    subquestion_number = int(local_part[1:])
    problem_number = int(paper[1:]) if paper.startswith("T") else 4
    problem_id = f"IPhO_2026_{problem_number}"
    return {
        "index": f"{problem_id}_{part_letter}_{subquestion_number}",
        "problem_id": problem_id,
        "problem_number": problem_number,
        "part_id": f"{part_letter}.{subquestion_number}",
        "part_letter": part_letter,
        "subquestion_number": subquestion_number,
    }


def build_archon_rows(
    parts: list[dict[str, Any]], enriched_rows: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    """Map curated rows to the exact HiPhO 2024-2025 Archon contract."""
    if len(parts) != len(enriched_rows):
        raise ValueError("Curated parts and enriched rows are not aligned")

    part_by_source_id = {str(part["part_id"]): part for part in parts}
    identity_by_source_id = {
        source_id: canonical_identity(part)
        for source_id, part in part_by_source_id.items()
    }

    archon_rows: list[dict[str, Any]] = []
    for part, enriched in zip(parts, enriched_rows, strict=True):
        source_id = str(part["part_id"])
        if enriched["source_index"] != source_id:
            raise ValueError(f"Misaligned enriched row for {source_id}")

        identity = identity_by_source_id[source_id]
        paper = str(part["paper"])
        image_names = [str(name) for name in enriched["images"]]
        image_entries = [
            {
                "path": name,
                "original_path": f"image/{name}",
                "role": "official_source_page",
                "evidence": (
                    f"Rendered from the official IPhO 2026 {paper} English "
                    "problem PDF; use the page image as primary evidence for "
                    "figures, formulas, tables, and apparatus geometry."
                ),
            }
            for name in image_names
        ]

        previous_parts = []
        for dependency_source_id in part["dependencies"]:
            dependency = part_by_source_id[dependency_source_id]
            dependency_identity = identity_by_source_id[dependency_source_id]
            previous_parts.append(
                {
                    "source_id": dependency_identity["index"],
                    "part_id": dependency_identity["part_id"],
                    "question": dependency["current_question"],
                    "answer": dependency["answer"],
                    "reusable_conclusions": [dependency["answer"]],
                    "dependency_policy": (
                        "natural_language_prerequisite_only; "
                        "do_not_import_Lean_output"
                    ),
                }
            )

        context = str(enriched["shared_context"]).strip()
        current_question = str(enriched["current_question"]).strip()
        question = f"{context}\n\nCurrent subquestion:\n{current_question}"
        answer = str(enriched["answer"]).strip()
        marking_name = (
            paper_file(paper, "marking_scheme")
            if paper.startswith("T")
            else paper_file(paper, "solution")
        )
        marking_label = (
            "Official marking scheme"
            if paper.startswith("T")
            else "Official experimental solution"
        )

        archon_rows.append(
            {
                "index": identity["index"],
                "category": "physics",
                "source_dataset": (
                    "IPhO 2026 official English papers via phoXiv mirror"
                ),
                "source_dataset_url": (
                    "https://phoxiv.org/olympiads/ipho/2026/"
                ),
                "year": 2026,
                "problem_id": identity["problem_id"],
                "problem_number": identity["problem_number"],
                "part_id": identity["part_id"],
                "part_letter": identity["part_letter"],
                "subquestion_number": identity["subquestion_number"],
                "formalization_input_policy": {
                    "previous_parts": (
                        "Natural-language prerequisites only; do not import "
                        "or depend on previous Lean outputs."
                    ),
                    "images": (
                        "Use only listed official source-page images. Read "
                        "figures, formulas, tables, and apparatus geometry "
                        "from the image when curated text is insufficient."
                    ),
                },
                "context": context,
                "current_question": current_question,
                "question": question,
                "answer": answer,
                "answers": [answer],
                "marking": [[
                    f"{marking_label}: raw/{marking_name}; "
                    f"this subquestion is worth {part['points']:g} points."
                ]],
                "answer_type": [ANSWER_TYPE_BY_KIND[part["kind"]]],
                "unit": [None],
                "points": [part["points"]],
                "modality": "text+official source-page image",
                "field": FIELD_BY_CONTEXT[part["context_key"]],
                "source": f"IPhO_2026_{paper}",
                "previous_parts": previous_parts,
                "previous_part_count": len(previous_parts),
                "images": image_entries,
                "image": image_names[0],
                "image_count": len(image_entries),
                "raw_hipho_image_question": [],
            }
        )

    validate_archon_rows(archon_rows)
    return archon_rows


def validate_archon_rows(rows: list[dict[str, Any]]) -> None:
    expected_fields = set(ARCHON_SCHEMA_FIELDS)
    if HIPHO_REFERENCE.is_file():
        with HIPHO_REFERENCE.open("r", encoding="utf-8") as handle:
            reference_row = json.loads(next(line for line in handle if line.strip()))
        reference_fields = set(reference_row)
        if reference_fields != expected_fields:
            raise ValueError(
                "Static Archon schema no longer matches the HiPhO reference: "
                f"missing={sorted(reference_fields - expected_fields)}, "
                f"extra={sorted(expected_fields - reference_fields)}"
            )

    seen: set[str] = set()
    for row_number, row in enumerate(rows, start=1):
        fields = set(row)
        if fields != expected_fields:
            raise ValueError(
                f"Archon row {row_number} has incompatible fields: "
                f"missing={sorted(expected_fields - fields)}, "
                f"extra={sorted(fields - expected_fields)}"
            )
        index = str(row["index"])
        if index in seen:
            raise ValueError(f"Duplicate Archon index: {index}")
        seen.add(index)
        if row["previous_part_count"] != len(row["previous_parts"]):
            raise ValueError(f"Bad previous_part_count for {index}")
        if row["image_count"] != len(row["images"]):
            raise ValueError(f"Bad image_count for {index}")
        if row["image"] != row["images"][0]["path"]:
            raise ValueError(f"Primary image mismatch for {index}")
        for image in row["images"]:
            if not (IMAGE / image["path"]).is_file():
                raise FileNotFoundError(IMAGE / image["path"])


def write_review(rows: list[dict[str, Any]]) -> None:
    REVIEW.mkdir(parents=True, exist_ok=True)

    def preview_text(value: object) -> str:
        return " ".join(str(value).replace("\t", " ").split())

    columns = (
        "index",
        "problem_id",
        "part_id",
        "image_count",
        "previous_part_count",
        "modality",
        "current_question",
        "answer",
    )
    preview_lines = ["\t".join(columns)]
    for row in rows:
        preview_lines.append(
            "\t".join(preview_text(row[column]) for column in columns)
        )
    (REVIEW / "preview.tsv").write_text(
        "\n".join(preview_lines) + "\n", encoding="utf-8"
    )

    sample_indices = sorted({0, 4, 12, 22, 23, len(rows) - 1})
    samples = [rows[index] for index in sample_indices]
    (REVIEW / "sample_items.json").write_text(
        json.dumps(samples, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    by_problem = Counter(row["problem_id"] for row in rows)
    unique_image_paths = sorted({
        image["path"] for row in rows for image in row["images"]
    })
    summary = "\n".join(
        [
            "# IPhO 2026 Archon Input Review",
            "",
            f"- Items: {len(rows)}",
            f"- By problem: {dict(by_problem)}",
            f"- Items with images: {sum(row['image_count'] > 0 for row in rows)}",
            (
                "- Items with explicit previous-part dependencies: "
                f"{sum(row['previous_part_count'] > 0 for row in rows)}"
            ),
            f"- Unique rendered source pages: {len(unique_image_paths)}",
            "",
            "## Compatibility",
            "",
            (
                "- Every row has exactly the same 29 top-level fields as "
                "hipho_ipho_2024_2025_archon.jsonl."
            ),
            (
                "- previous_parts contain natural-language prerequisites "
                "only; no Lean output is imported."
            ),
            (
                "- image paths resolve against the default image/ directory "
                "because this JSONL is stored at the dataset root."
            ),
            "",
            "## Primary input",
            "",
            "- ipho_2026_source/ipho_2026_archon.jsonl",
            (
                "- Formalization-ready subset: "
                "ipho_2026_source/ipho_2026_archon_pipeline.jsonl"
            ),
            "",
        ]
    )
    (REVIEW / "summary.md").write_text(summary, encoding="utf-8")

    manifest = {
        "source_dataset": (
            "IPhO 2026 official English papers via phoXiv mirror"
        ),
        "source_dataset_url": "https://phoxiv.org/olympiads/ipho/2026/",
        "generated_items": len(rows),
        "schema_reference": (
            "hipho_ipho_2024_2025/"
            "hipho_ipho_2024_2025_archon.jsonl"
        ),
        "schema_field_count": len(ARCHON_SCHEMA_FIELDS),
        "schema_fields": list(ARCHON_SCHEMA_FIELDS),
        "output_jsonl": "ipho_2026_source/ipho_2026_archon.jsonl",
        "image_files": len(unique_image_paths),
        "notes": [
            (
                "previous_parts use curated natural-language dependencies and "
                "never reference previous Lean outputs."
            ),
            (
                "Images are page renders of the official English problem PDFs; "
                "raw_hipho_image_question remains empty because this source is "
                "not the SciYu/HiPhO dataset."
            ),
        ],
    }
    (REVIEW / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.write_text(
        "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in rows),
        encoding="utf-8",
    )


def main() -> None:
    PROCESSED.mkdir(parents=True, exist_ok=True)
    all_parts = THEORY_PARTS + EXPERIMENT_PARTS
    all_rows = build_rows(all_parts)
    archon_rows = build_archon_rows(all_parts, all_rows)
    theory_rows = [row for row in all_rows if row["paper"].startswith("T")]
    experiment_rows = [row for row in all_rows if row["paper"] == "E1"]
    pipeline_rows = [row for row in all_rows if row["formalization_ready"]]
    archon_pipeline_rows = [
        archon_row
        for archon_row, row in zip(archon_rows, all_rows, strict=True)
        if row["formalization_ready"]
    ]

    outputs = {
        "ipho_2026_all.jsonl": all_rows,
        "ipho_2026_theory.jsonl": theory_rows,
        "ipho_2026_experiment.jsonl": experiment_rows,
        "ipho_2026_pipeline.jsonl": pipeline_rows,
    }
    for name, rows in outputs.items():
        write_jsonl(PROCESSED / name, rows)

    archon_outputs = {
        "ipho_2026_archon.jsonl": archon_rows,
        "ipho_2026_archon_pipeline.jsonl": archon_pipeline_rows,
    }
    for name, rows in archon_outputs.items():
        write_jsonl(SOURCE / name, rows)
    write_review(archon_rows)

    (PROCESSED / "ipho_2026_entries.json").write_text(
        json.dumps(all_rows, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    source_files = []
    for name, url in SOURCE_URLS.items():
        path = RAW / name
        if not path.is_file():
            raise FileNotFoundError(path)
        source_files.append(
            {
                "file": f"raw/{name}",
                "url": url,
                "bytes": path.stat().st_size,
                "sha256": sha256(path),
            }
        )

    manifest = {
        "schema_version": 2,
        "competition": "LVI International Physics Olympiad",
        "year": 2026,
        "location": "Bucaramanga, Colombia",
        "language": "English",
        "source_status": (
            "Complete papers mirrored by phoXiv; as of 2026-07-26 the JPhO page "
            "still labels the theory paper as forthcoming."
        ),
        "counts": {
            "all": len(all_rows),
            "theory": len(theory_rows),
            "experiment": len(experiment_rows),
            "formalization_ready": len(pipeline_rows),
            "by_paper": dict(Counter(row["paper"] for row in all_rows)),
            "by_kind": dict(Counter(row["kind"] for row in all_rows)),
        },
        "datasets": {
            **{
                f"processed/{name}": {
                    "rows": len(rows),
                    "sha256": sha256(PROCESSED / name),
                    "schema": "provenance-rich",
                }
                for name, rows in outputs.items()
            },
            **{
                name: {
                    "rows": len(rows),
                    "sha256": sha256(SOURCE / name),
                    "schema": "hipho-2024-2025-compatible",
                }
                for name, rows in archon_outputs.items()
            },
        },
        "archon_schema_reference": (
            "hipho_ipho_2024_2025/"
            "hipho_ipho_2024_2025_archon.jsonl"
        ),
        "archon_schema_field_count": len(ARCHON_SCHEMA_FIELDS),
        "source_files": source_files,
    }
    (PROCESSED / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    print(json.dumps(manifest["counts"], ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()
