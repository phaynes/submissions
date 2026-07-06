#!/usr/bin/env bash
set -euo pipefail

repo="${1:-/Volumes/second-store/devel/knowledge-base-mcp/mentormind/physlib-contrib}"
cd "$repo"

lake build PhyslibAlpha.SpaceAndTime.Space.Surfaces.Torus
lake build PhyslibAlpha.SpaceAndTime.Space.Surfaces.Ellipsoid
lake build PhyslibAlpha

lake env lean --stdin <<'EOF'
import PhyslibAlpha.SpaceAndTime.Space.Surfaces.Torus
import PhyslibAlpha.SpaceAndTime.Space.Surfaces.Ellipsoid

#print axioms Space.torus
#print axioms Space.torusMeasure
#print axioms Space.torusDist
#print axioms Space.ellipsoid
#print axioms Space.ellipsoidMeasure
#print axioms Space.ellipsoidDist
EOF

if rg -n "\\b(sorry|admit)\\b|axiom " \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Torus.lean \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Ellipsoid.lean \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Cone.lean
then
  echo "Unexpected sorry/admit/axiom marker found." >&2
  exit 1
fi

./scripts/lint-style.py \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Torus.lean \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Ellipsoid.lean \
  PhyslibAlpha/SpaceAndTime/Space/Surfaces/Cone.lean

lake exe runPhyslibAlphaLinters
