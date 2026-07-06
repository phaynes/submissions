# Verification evidence

Working checkout:
`/Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib`

Branch:
`feature/surfaces-torus-ellipsoid`

Code commit:
`db52bba8 feat(PhyslibAlpha): add curved surface measures`

Lean:
`lake env lean --version` reports Lean 4.31.0.

## Build checks

Passed:

```text
lake build PhyslibAlpha.SpaceAndTime.Space.Surfaces.Torus
lake build PhyslibAlpha.SpaceAndTime.Space.Surfaces.Ellipsoid
lake build PhyslibAlpha
lake build
/Volumes/second-store/devel/knowledge-base-mcp/submissions/PhysLean/preparation/PR1-Surfaces/verify.sh
```

`lake build` completed successfully. It reported an existing unused-simp warning in
`Physlib/Electromagnetism/Kinematics/EMPotential.lean`, outside this PR1 surface work.

## Lint and source checks

Passed:

```text
lake exe runPhyslibAlphaLinters
./scripts/lint-style.py \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Torus.lean \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Ellipsoid.lean \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Cone.lean
lake exe sorry_lint
rg -n "\\b(sorry|admit)\\b|axiom " \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Torus.lean \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Ellipsoid.lean \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Cone.lean
```

The `rg` scan returned no matches.

`lake exe lint_all --fast` was also run. Its build, import, duplicate-tag, and sorry
checks passed. Its style step reported pre-existing style issues in tracked `Physlib/*`
files outside this surface work; that linter does not target the untracked Alpha files
added here. The direct `lint-style.py` invocation above is the relevant style evidence
for Cone/Torus/Ellipsoid.

## Axiom checks

Command:

```lean
import PhyslibAlpha.SpaceAndTime.Space.Surfaces.Torus
import PhyslibAlpha.SpaceAndTime.Space.Surfaces.Ellipsoid

#print axioms Space.torus
#print axioms Space.torusMeasure
#print axioms Space.torusDist
#print axioms Space.ellipsoid
#print axioms Space.ellipsoidMeasure
#print axioms Space.ellipsoidDist
```

Output:

```text
'Space.torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'Space.torusMeasure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Space.torusDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Space.ellipsoid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Space.ellipsoidMeasure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Space.ellipsoidDist' depends on axioms: [propext, Classical.choice, Quot.sound]
```
