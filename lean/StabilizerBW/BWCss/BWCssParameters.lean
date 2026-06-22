import StabilizerBW.BWCss.ReedMuller
import StabilizerBW.BWCss.CSS
import StabilizerBW.BWCss.Grade

/-!
# Barnes–Wall CSS code family: top-level entry point

This is the headline module for the Barnes–Wall CSS development.  It collects the
Reed–Muller theory (`ReedMuller`), the CSS construction and parameter formula
(`CSS`), and the grade-to-logical-operator correspondence (`Grade`).

## Main results

* `BWCss.RM_dim`, `BWCss.RM_min_dist`, `BWCss.RM_chain`, `BWCss.RM_dual` —
  the parameters and duality of the binary Reed–Muller codes `RM(r, m)`.
* `BWCss.CSSCode.ofRMPair`, with `ofRMPair_n`, `ofRMPair_k`, `ofRMPair_d` —
  the Reed–Muller-pair CSS code and its `[[n, k, d]]` parameters.
* `BWCss.BWCss_params` — the headline parameter formula for `BWCss(m, r₁, r₂)`.
* `BWCss.BWCss_recovers_canonical_seeds` — the Steane and Bravyi–Haah seed
  codes as members of the family.
* `BWCss.grade_logical_correspondence` — phase-polynomial operators as logical-X
  representatives.
* `BWCss.gradeEnumerator_closed_form` / `BWCss.grade_refined_logical_enumerator`
  — the all-`m` Möbius/grade closed form `G_m(z) = 8·4^m·(1+z)^m`.

-/
