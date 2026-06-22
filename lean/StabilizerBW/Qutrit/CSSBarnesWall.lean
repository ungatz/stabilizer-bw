/-
# QutritCSSBW — aggregator

The genuine qutrit-CSS Barnes–Wall lattice and the re-run of the qubit-chapter
stress tests against it.  See `FullyGeneralHeadline.lean` for the headline
`qutrit_arithmetic_view_fully_general`.

* `QutritReedMuller`        — `QRM(m, r)` over `𝔽₃` * `BWCssQutrit`             — the qutrit-CSS Barnes–Wall code * `QutritGrade`             — the genuine `λ₃²`-lattice grade `gradeQ` * `StrictSubsetCorrected`   — TEST 1: coefficient `2 = ν_{λ₃}(3)` * `ExtendedCyclotomicRing`  — `ℤ[ζ₉]` and the Howard–Vala T-gate * `IncomparabilityCorrected`— TEST 4: cT vs CCZ incomparability * `FullyGeneralHeadline`    — the headline + `AxiomProbe` -/
import StabilizerBW.Qutrit.CSSBarnesWall.QutritReedMuller
import StabilizerBW.Qutrit.CSSBarnesWall.BWCssQutrit
import StabilizerBW.Qutrit.CSSBarnesWall.QutritGrade
import StabilizerBW.Qutrit.CSSBarnesWall.StrictSubsetCorrected
import StabilizerBW.Qutrit.CSSBarnesWall.ExtendedCyclotomicRing
import StabilizerBW.Qutrit.CSSBarnesWall.IncomparabilityCorrected
import StabilizerBW.Qutrit.CSSBarnesWall.FullyGeneralHeadline
import StabilizerBW.Qutrit.CSSBarnesWall.AxiomProbe
