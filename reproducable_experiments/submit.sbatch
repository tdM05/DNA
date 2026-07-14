#!/usr/bin/env bash
#SBATCH --job-name=euclid_timing
#SBATCH --partition=cpunodes
#SBATCH --constraint=EPYC_9634
#SBATCH --exclusive
#SBATCH --nodes=1
#SBATCH --time=24:00:00
#SBATCH --output=euclid_timing_%j.log
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PATH="/u/taddmao/.venvs/leaneuclid/bin:$PATH"   # z3, cvc5
export CAP="${CAP:-600}" JOBS="${JOBS:-1}"
mkdir -p "$HERE/results"
{ echo "host: $(hostname)"; echo "date: $(date)"; echo "cap:  ${CAP}s  jobs: ${JOBS}";
  echo "git:  $(git -C "$HERE/.." rev-parse HEAD)"; echo "z3:   $(which z3)  cvc5: $(which cvc5)";
  echo; lscpu | grep -E 'Model name|Socket|Core|Thread'; } > "$HERE/results/run_meta_${SLURM_JOB_ID:-local}.txt"
bash "$HERE/run_timing.sh"
