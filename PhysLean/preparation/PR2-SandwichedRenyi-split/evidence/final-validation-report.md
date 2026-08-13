# PR2 V2 Final Validation Report

Status: **PASS**

## Claude Review

Claude review reported no blocking findings and recommended final equivalence / full-build / harness validation.

## V1 To V2 Public Surface

Matches expected drift: **True**
- `relative_removed`: inner_log_bounded_near, qRelativeEnt_lowerSemicontinuous_2
- `relative_added`: (none)
- `sandwiched_added`: inner_log_bounded_near, qRelativeEnt_lowerSemicontinuous_2, sandwichedRelRentropy_one_lowerSemicontinuous
- `sandwiched_removed`: eigenWeight, eigenWeight.eq_1, eigenWeight_nonneg, eigenWeight_zero_of_eigenvalue_zero, inner_cfc_eq_sum_eigenWeight

## Wrapper Equivalence

- `qRelativeEnt.lowerSemicontinuous` normalized type unchanged: **True**
- baseline type hash: `sha256:c6f4b7803b3d796464fe65156f63e93e2f794bc240b01a5d709746c10a3f7f00`
- final type hash: `sha256:c6f4b7803b3d796464fe65156f63e93e2f794bc240b01a5d709746c10a3f7f00`
- final wrapper body depends on `sandwichedRelRentropy_one_lowerSemicontinuous`: **True**

## Private Helper Resolution

- `eigenWeight` -> `_private.QuantumInfo.Entropy.SandwichedRenyi.0.eigenWeight` (def), private: **True**
- `inner_cfc_eq_sum_eigenWeight` -> `_private.QuantumInfo.Entropy.SandwichedRenyi.0.inner_cfc_eq_sum_eigenWeight` (theorem), private: **True**
- `eigenWeight_nonneg` -> `_private.QuantumInfo.Entropy.SandwichedRenyi.0.eigenWeight_nonneg` (theorem), private: **True**
- `eigenWeight_zero_of_eigenvalue_zero` -> `_private.QuantumInfo.Entropy.SandwichedRenyi.0.eigenWeight_zero_of_eigenvalue_zero` (theorem), private: **True**

## Kernel And Harness Checks

- `lake_build_sandwichedrenyi`: **PASS** (/Volumes/second-store/devel/knowledge-base-mcp/mentormind/helios-projects/project/yaqin/evidence/pr2-v2/final/lake-build-sandwichedrenyi.post-review.log)
- `lake_build_relative`: **PASS** (/Volumes/second-store/devel/knowledge-base-mcp/mentormind/helios-projects/project/yaqin/evidence/pr2-v2/final/lake-build-relative.post-review.log)
- `pr2_harness`: **PASS** (/Volumes/second-store/devel/knowledge-base-mcp/mentormind/helios-projects/project/yaqin/evidence/pr2-v2/final/pr2-harness.log)
- `pr2_harness_axioms`: **PASS** (/Volumes/second-store/devel/knowledge-base-mcp/mentormind/helios-projects/project/yaqin/evidence/pr2-v2/final/pr2-harness-axioms.log)
- `lake_build_full`: **PASS** (/Volumes/second-store/devel/knowledge-base-mcp/mentormind/helios-projects/project/yaqin/evidence/pr2-v2/final/lake-build-full.post-review.log)

## Notes

- The first final Varro wrapper query for qRelativeEnt.lowerSemicontinuous returned lean-query-empty-output; direct Lean replay and a Varro retry both succeeded. The canonical final snapshot is the retry, and the first error is preserved as *.first-error.json.
- The PR2 harness whitelist was updated to include the reviewed V2 public boundary theorem sandwichedRelRentropy_one_lowerSemicontinuous.
