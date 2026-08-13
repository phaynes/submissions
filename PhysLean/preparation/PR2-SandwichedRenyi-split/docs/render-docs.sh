#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"

quarto render "$here/physics-brief.qmd"
quarto render "$here/refactor-methodology.qmd"
