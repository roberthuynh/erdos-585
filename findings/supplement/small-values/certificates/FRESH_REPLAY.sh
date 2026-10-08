#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
: "${FINITE_NAUTY_DIR:?Set FINITE_NAUTY_DIR to your built nauty 2.9.3 directory}"
export FINITE_NAUTY_DIR
timeout 240 python3 -B build_tools.py
timeout 240 python3 -B run_census.py controls
timeout 240 python3 -B run_census.py baseline
timeout 240 python3 -B run_census.py parents
timeout 240 python3 -B extend_parents.py
timeout 240 python3 -B verify_certificates.py
timeout 240 python3 -B verify_full_streams.py
printf '%s\n' 'COMPLETE COMPUTATIONAL CERTIFICATE'
