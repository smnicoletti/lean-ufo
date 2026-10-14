#!/bin/sh
# Keep execution inside the image: host filesystem sharing and host Lean caches
# must not become unrecorded dependencies of the measured workflow.
set -eu
cd /workspace/alien
case "${1:-help}" in
  reference)
    export UFO_GENERATE_TABLES=1
    export UFO_EXPERIMENT_RESULTS=/opt/alien/reference
    export UFO_TABLE_OUTPUT=/results/reference-tables
    exec lake test
    ;;
  smoke)
    export LEANUFO_PERFORMANCE_TESTS=1 UFO_GENERATE_TABLES=1
    exec lake test
    ;;
  experiments)
    export LEANUFO_PERFORMANCE_TESTS="${2:-10}" UFO_GENERATE_TABLES=1
    exec lake test
    ;;
  tables)
    export UFO_GENERATE_TABLES=1
    if [ "$#" -gt 1 ]; then export UFO_EXPERIMENT_RESULTS="$2"; fi
    exec lake test
    ;;
  check) exec lake test ;;
  shell) exec /bin/bash ;;
  help)
    echo 'ALIEN: reference | smoke | experiments [N] | tables [RUN] | check | shell'
    echo 'Results are retained under /results. Copy them out before removing the container.'
    ;;
  *) echo "Unknown artifact command: $1" >&2; exit 2 ;;
esac
